/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.EmitterScannability.NonemptyStructure

/-!
# `SeqInteriorSeparators` — the seq-typed separator carrier (sub-brick `(i'-b-descend-defn)`)

This module lands the DEFINITION half of `(i'-b-descend)`: the guard conjunct that the recursive
seq-body producer threads, together with the proof that its descend/advance edges are SUBSET
restrictions (the easy half — the genuine cost is the root seed `(i'-b-descend-root)`, owed
separately).

## Why a carrier, and why it descends trivially

`ref-non-restriction-residual-root-seed` established that the two separator facts (`bodySucc`,
`noTrailingSep`) are NOT local-window-restriction facts: keyed relative to a moving origin they go
silent across `descend` (a child's depth-`0` is the parent's depth-`1`). The R297 minimal-pair probe
(`Tests/Guards/Proofs/BodySuccSeqDiscriminator.lean`) then showed the rescue: the facts hold on every
**seq-typed** depth-`0`-balanced bracket interior and fail on map-typed ones, and the discriminator
is the `btStack` TOP that `WellTyped`/`btFold` already computes — read off the pair, not invented.

So the carrier quantifies over sub-windows `[a,b) ⊆ [lo,hi)` that are **seq-typed and balanced**, and
asserts the two separator facts on each. The decisive design choice: every gate condition
(`SeqTypedInterior`) and every asserted fact (`bodySuccFact`/`noTrailingSepFact`) is keyed ONLY on
`a`, `b` and the global `tokens` — never on the outer origin `lo`/`hi`. The window bounds enter the
carrier ONLY through the domain inequalities `lo ≤ a` and `b ≤ hi`. Hence narrowing `[lo,hi)` to any
sub-interval is a pure subset restriction: the body is reused verbatim and only the domain shrinks
(`SeqInteriorSeparators_narrow`). `descend` and `advance` are two instances of exactly that.
-/

namespace L4YAML.Proofs.EmitterScannability

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.Proofs.ParserGrammable

/-- The **seq-typed bracket-interior gate** for a sub-window `[a,b)` of `tokens`, read off the same
    substrate the R297 probe used. Three window-ABSOLUTE conditions:

    * the window is depth-`0`-balanced (`flowBracketBalance tokens a b = 0`),
    * its immediately enclosing bracket is a SEQUENCE — the head of `WellTyped`/`btFold`'s typed
      stack after consuming the strict prefix `[0, a)` is `true`
      (`flowSequenceStart ↦ true`, `flowMappingStart ↦ false`), and
    * the window is **locally Dyck** — `flowBracketBalance tokens a i ≥ 0` for every `a ≤ i ≤ b`.

    **The local-Dyck floor is load-bearing (R313).** Without it the gate is *floor-blind*: a
    `#guard`-backed probe on `[[1], [2]]` (`Tests/Guards/Proofs/SeqGateFloorProbe.lean`) shows the
    CROSS-SIBLING window `[3, 7)` (from inside the first inner seq to inside the second) is
    depth-`0`-balanced and seq-enclosed — passing the bare two-conjunct gate — yet `bodySuccFact`
    is outright FALSE on it (its first entry `tokens[3] = "1"` is depth-`0`-complete but
    `tokens[4] = ]`, not a `.flowEntry`), so the carrier `SeqInteriorSeparators` would be FALSE on a
    *valid* witness. Such windows DIP below `0` (crossing the first sibling's close: `balance 3 5 =
    -1`), so the floor excludes EXACTLY them: every floor-violating gated window is a cross-sibling
    one, and `floored ⟹ bodySuccFact` at every gated window of the witness. The floor also discharges
    the consumer's `b ≤ hiS` for free (a window crossing the located opener's matching close `j` would
    have `balance a (j+1) < 0`). This is [[ref-probe-provider-head-blind-gate]] for a FLOOR-blind
    gate, and the gate-domain dual of [[ref-downstream-derisk-restores-upstream]] (R311 restored a
    dropped *producer* conjunct; here the missing conjunct is in the *gate*).

    Each condition is window-ABSOLUTE (no outer origin), which is exactly what makes the carrier below
    a subset restriction: the floor restricts to any `[a', b'] ⊆ [a, b]` by `flowBracketBalance`
    composition. -/
def SeqTypedInterior (tokens : Array (Positioned YamlToken)) (a b : Nat) : Prop :=
  flowBracketBalance tokens a b = 0 ∧
  (btFold (some []) (tokens.toList.take a)).bind (·.head?) = some true ∧
  (∀ i, a ≤ i → i ≤ b → flowBracketBalance tokens a i ≥ 0)

/-- The `bodySucc` separator fact, relativised to an arbitrary window `[a,b)` (the
    `FlowBodyContent.bodySucc`/`flowBodyContent_of_deep` premise with `lo := a`, `hi := b`): at every
    depth-`0` balanced-prefix end that is not itself a separator, the entry either closes the window
    or is immediately followed by a `.flowEntry`. -/
def bodySuccFact (tokens : Array (Positioned YamlToken)) (a b : Nat) : Prop :=
  ∀ k, a ≤ k → k < b →
    flowBracketBalance tokens a (k + 1) = 0 →
    tokens[k]!.val ≠ .flowEntry →
    k + 1 = b ∨ ∃ (_ : k + 1 < b), tokens[k + 1]!.val = .flowEntry

/-- The `noTrailingSep` fact, relativised to an arbitrary window `[a,b)` (the
    `flowBodyContent_of_deep` `h_noTrailingSep` premise with `lo := a`, `hi := b`): the window cannot
    END on a depth-`0` separator — a `.flowEntry` at the last position would have to be followed by
    flow content, which an end-of-window cannot supply. -/
def noTrailingSepFact (tokens : Array (Positioned YamlToken)) (a b : Nat) : Prop :=
  ∀ k, a ≤ k → k + 1 = b →
    tokens[k]!.val = .flowEntry →
    flowBracketBalance tokens a k = 0 →
    isFlowContentStart tokens[k + 1]!.val

/-- **The separator carrier.** Over the window `[lo,hi)`: for every seq-typed depth-`0`-balanced
    bracket-interior sub-window `[a,b) ⊆ [lo,hi)`, both separator facts hold on `[a,b)`.

    This is the guard conjunct the recursive seq-body producer threads. Its body is `lo`/`hi`-free
    except through the domain bounds `lo ≤ a`, `b ≤ hi`, so it restricts to sub-windows for free. -/
def SeqInteriorSeparators (tokens : Array (Positioned YamlToken)) (lo hi : Nat) : Prop :=
  ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → SeqTypedInterior tokens a b →
    bodySuccFact tokens a b ∧ noTrailingSepFact tokens a b

/-- **Subset restriction (the descend/advance edge, generic form).** Narrowing the window to any
    sub-interval `[lo',hi') ⊆ [lo,hi)` preserves the carrier: the quantifier body is reused verbatim,
    only the domain shrinks. This is the 3-line `omega`-style core the 145th-revision map promised. -/
theorem SeqInteriorSeparators_narrow {tokens : Array (Positioned YamlToken)} {lo hi lo' hi' : Nat}
    (h_lo : lo ≤ lo') (h_hi : hi' ≤ hi)
    (h : SeqInteriorSeparators tokens lo hi) :
    SeqInteriorSeparators tokens lo' hi' := by
  intro a b ha hab hb hgate
  exact h a b (Nat.le_trans h_lo ha) hab (Nat.le_trans hb h_hi) hgate

/-- **The DESCEND edge.** When the recursion descends into a nested bracket interior
    `[lo',hi') ⊆ [lo,hi)`, the carrier follows by subset restriction. -/
theorem SeqInteriorSeparators_descend {tokens : Array (Positioned YamlToken)} {lo hi lo' hi' : Nat}
    (h_lo : lo ≤ lo') (h_hi : hi' ≤ hi)
    (h : SeqInteriorSeparators tokens lo hi) :
    SeqInteriorSeparators tokens lo' hi' :=
  SeqInteriorSeparators_narrow h_lo h_hi h

/-- **The ADVANCE edge.** When the recursion advances past a separator at `m` to the tail
    `[m+1, hi)`, the carrier follows by subset restriction (`hi` unchanged). -/
theorem SeqInteriorSeparators_advance {tokens : Array (Positioned YamlToken)} {lo hi m : Nat}
    (h_lo : lo ≤ m + 1)
    (h : SeqInteriorSeparators tokens lo hi) :
    SeqInteriorSeparators tokens (m + 1) hi :=
  SeqInteriorSeparators_narrow h_lo (Nat.le_refl hi) h

/-! ## The MAP separator carrier — the `some false` mirror of the seq carrier (R513)

The seq axis above is one root carrier away from done: `seqHRec_of_root_and_emit` (`:6582`) folds the
whole discharged seq chain into `flowSubrangesOk_of_window_producers`'s `h_seq_rec` slot from the
single carrier `SeqInteriorSeparators tokens 2 (size-2)` (R512). The MAP axis has had NO analog — its
`h_map_rec` and the SIX map-grammar facts ride into the consumer as seven RAW per-window producers
(the recorded seq/map ASYMMETRY). This block lands the FOUNDATION of the map mirror: the gate, the
bundled grammar facts, the carrier, and its three subset-restriction edges.

Design is the faithful `some true → some false` dual of `SeqTypedInterior`/`SeqInteriorSeparators`
([[ref-window-absolute-gate-subset-restriction]]): the gate `MapTypedInterior` reads the `btFold`-top
`= some false` (an enclosing `{`, by the `btStep` convention `true = [`, `false = {`,
`WellBracketed.lean:1536`), and every one of the six asserted facts (`MapGrammarFacts`) is the
`lo→a`, `hi→b` re-key of the corresponding hypothesis in `flowSubrangesOk_of_window_producers`
(`NonemptyStructure.lean:10434+`), keyed window-ABSOLUTELY on `a`. The outer-origin `lo`/`hi` enters
only through the domain bounds `lo ≤ a`, `b ≤ hi`, so narrowing is a pure subset restriction whose
proof is byte-identical to the seq one regardless of how many facts are bundled — `_narrow` never
inspects the body. Marker-FREE by design: the consumer's `flowMappingEnd`/`flowMappingStart` boundary
premises are dropped (the gate's `= some false` enclosure identifies the map interior instead), so the
carrier is STRICTLY STRONGER and re-projects to each marker-bearing consumer hypothesis for free at
`a := lo, b := hi` (the next brick, `mapGrammarFacts_of_mapRoot`).

Verified-but-unconsumed: its consumer — a future `mapHRec_of_root_and_emit` map fold + a
`flowSubrangesOk_of_seqRoot_and_mapRoot` reconciliation — does not exist yet; references no sorry site;
frontier sorry count unchanged at 4; axioms `[propext]` only (the structural edges shed even
`Classical.choice`/`Quot.sound`). -/

/-- **Map-typed interior gate** — the `some false` dual of `SeqTypedInterior` (`:66`): a depth-`0`-
    balanced bracket interior `[a,b)` whose innermost enclosing opener is a `{` (`btFold`-top
    `= some false`) and whose every prefix stays balanced-or-deeper. -/
def MapTypedInterior (tokens : Array (Positioned YamlToken)) (a b : Nat) : Prop :=
  flowBracketBalance tokens a b = 0 ∧
  (btFold (some []) (tokens.toList.take a)).bind (·.head?) = some false ∧
  (∀ i, a ≤ i → i ≤ b → flowBracketBalance tokens a i ≥ 0)

/-- **The six map-grammar adjacency facts, relativised to a window `[a,b)`** — the `lo→a`, `hi→b`
    re-key of `flowSubrangesOk_of_window_producers`'s `h_key_content`, `h_key_scalar_value`,
    `h_value_content`, `h_value_scalar_succ`, `h_key_bracket_succ`, `h_value_bracket_succ`
    (`NonemptyStructure.lean:10434+`), each keyed window-absolutely on `a` (the map analog of the seq
    carrier's two-fact `bodySuccFact`/`noTrailingSepFact` bundle). -/
def MapGrammarFacts (tokens : Array (Positioned YamlToken)) (a b : Nat) : Prop :=
  (∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .key →
      k + 1 < b ∧ isFlowContentStart tokens[k + 1]!.val) ∧
  (∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .key →
      (∃ c s, tokens[k + 1]!.val = .scalar c s) → k + 2 < b ∧ tokens[k + 2]!.val = .value) ∧
  (∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .value →
      k + 1 < b ∧ isFlowContentStart tokens[k + 1]!.val) ∧
  (∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .value →
      (∃ c s, tokens[k + 1]!.val = .scalar c s) →
      k + 2 ≤ b ∧ (tokens[k + 2]!.val = .flowEntry ∨ (tokens[k + 2]!.val = .flowMappingEnd ∧ k + 2 = b))) ∧
  (∀ k j, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .key →
      k + 1 < j → j < b → flowBracketDelta tokens[j]!.val = -1 → flowBracketBalance tokens a (j + 1) = 0 →
      j + 1 < b ∧ tokens[j + 1]!.val = .value) ∧
  (∀ k j, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .value →
      k + 1 < j → j < b → flowBracketDelta tokens[j]!.val = -1 → flowBracketBalance tokens a (j + 1) = 0 →
      j + 1 ≤ b ∧ (tokens[j + 1]!.val = .flowEntry ∨ (tokens[j + 1]!.val = .flowMappingEnd ∧ j + 1 = b)))

/-- **The map separator carrier** — the `some false` mirror of `SeqInteriorSeparators` (`:96`). Over
    `[lo,hi)`: every map-typed depth-`0`-balanced bracket-interior sub-window `[a,b) ⊆ [lo,hi)`
    satisfies all six `MapGrammarFacts`. The body is `lo`/`hi`-free except through the domain bounds, so
    it restricts to sub-windows for free (the descend/advance edges below). -/
def MapInteriorSeparators (tokens : Array (Positioned YamlToken)) (lo hi : Nat) : Prop :=
  ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → MapTypedInterior tokens a b → MapGrammarFacts tokens a b

/-- **Subset restriction (the descend/advance edge, generic form).** The exact mirror of
    `SeqInteriorSeparators_narrow` (`:103`) — the quantifier body is reused verbatim, only the domain
    shrinks; `_narrow` never inspects the bundled facts, so the proof is byte-identical to the seq one. -/
theorem MapInteriorSeparators_narrow {tokens : Array (Positioned YamlToken)} {lo hi lo' hi' : Nat}
    (h_lo : lo ≤ lo') (h_hi : hi' ≤ hi)
    (h : MapInteriorSeparators tokens lo hi) :
    MapInteriorSeparators tokens lo' hi' := by
  intro a b ha hab hb hgate
  exact h a b (Nat.le_trans h_lo ha) hab (Nat.le_trans hb h_hi) hgate

/-- **The DESCEND edge.** Descending into a nested bracket interior `[lo',hi') ⊆ [lo,hi)` preserves the
    carrier by subset restriction (mirror of `SeqInteriorSeparators_descend`, `:112`). -/
theorem MapInteriorSeparators_descend {tokens : Array (Positioned YamlToken)} {lo hi lo' hi' : Nat}
    (h_lo : lo ≤ lo') (h_hi : hi' ≤ hi)
    (h : MapInteriorSeparators tokens lo hi) :
    MapInteriorSeparators tokens lo' hi' :=
  MapInteriorSeparators_narrow h_lo h_hi h

/-- **The ADVANCE edge.** Advancing past a separator at `m` to the tail `[m+1, hi)` preserves the
    carrier by subset restriction, `hi` unchanged (mirror of `SeqInteriorSeparators_advance`, `:120`). -/
theorem MapInteriorSeparators_advance {tokens : Array (Positioned YamlToken)} {lo hi m : Nat}
    (h_lo : lo ≤ m + 1)
    (h : MapInteriorSeparators tokens lo hi) :
    MapInteriorSeparators tokens (m + 1) hi :=
  MapInteriorSeparators_narrow h_lo (Nat.le_refl hi) h

/-! ### The boundary-ROBUST map separator carrier — the inhabited replacement (R541)

R540 PROBED the strict carrier `MapInteriorSeparators` (`:187`) at the boundary of its universal and
found it UNPROVABLE as defined: `MapGrammarFacts` (`:166`) is boundary-FRAGILE — conjuncts 1/2/3
conclude `k + 1 < b`, conjunct 5 concludes `j + 1 < b`, and conjuncts 2/4 require `k + 2 < b` /
`k + 2 ≤ b` (the marker's content must sit STRICTLY inside the window). Because
`flowBracketDelta .key = .value = 0` (`ParserGrammableBase.lean:506`), a gated `MapTypedInterior`
window can END one past a `.key`/`.value` marker at balance `0`, where those strict requirements
become `b < b` / `b + 1 ≤ b` — FALSE. Verified against the real defs on `{a: 1}`: the cut window
`[1,2)` is `MapTypedInterior` yet refutes `MapGrammarFacts` (R540, commit `1bfc4df0`).

This block lands the FIX as a NEW ADDITIVE PARALLEL TYPE
([[ref-additive-parallel-type-over-shared-edit]] — NEVER an edit to the strict shared
`MapGrammarFacts`, whose R513–R520 consumers depend on its exact strict shape): every genuinely
boundary-fragile conjunct (1/2/3/4/5) gains a window-CLOSE escape disjunct `b ≤ <asserted position>`
— exactly the `k + 1 = b ∨ …` shape that makes the seq `bodySuccFact` (`:75`) boundary-robust.
Conjunct 6 is already robust (`j < b` gives `j + 1 ≤ b` for free) and is reused verbatim. The escape
fires precisely at the cut window that killed the strict form; on a GENUINE map body (`b = hi`, the
only window the `mapGrammarFacts_of_mapRoot` consumer queries) the marker's content is genuinely
interior, so the strict form is recovered there for the existing consumers (the `b = hi` bridge, a
later brick).

INHABITATION-DEBT discipline ([[ref-inhabitation-debt-validate-target-defs]]): unlike the strict
carrier — which was surrounded by ~8 consumers before anyone checked it was inhabited — this one is
PROBED AT BIRTH. `Tests/Reflections/MapCarrierRobustInhabitation.lean` proves the robust facts
SURVIVE the window-close boundary (`b = a + 1`) for EVERY stream, while the strict facts are refuted
there. The probe lives under `Tests/` (not inline) so the carrier's inhabitation is a build-time
regression test, kept separate from the library definition.

Verified-but-unconsumed: the descent-provider chain that CONSTRUCTS this carrier, the rebase that
makes the robustness pay off, and the `b = hi` bridge back to `MapGrammarFacts`, are later bricks;
references no sorry site; frontier sorry count unchanged at 4. -/

/-- **The six map-grammar facts, made BOUNDARY-ROBUST** — the `'` variant of `MapGrammarFacts`
    (`:166`). Each conjunct whose strict form requires the asserted position to lie STRICTLY inside
    `[a,b)` (conjuncts 1/2/3/4/5) gains a window-close escape `b ≤ <position>` (the map analog of
    `bodySuccFact`'s `k + 1 = b` disjunct, `:75`); conjunct 6 is already robust and is the verbatim
    strict conjunct. The escape is what lets the carrier survive a window that ends one past a
    delta-`0` `.key`/`.value` marker — exactly the cut that makes the strict `MapGrammarFacts`
    unprovable (R540). -/
def MapGrammarFacts' (tokens : Array (Positioned YamlToken)) (a b : Nat) : Prop :=
  (∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .key →
      b ≤ k + 1 ∨ (k + 1 < b ∧ isFlowContentStart tokens[k + 1]!.val)) ∧
  (∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .key →
      (∃ c s, tokens[k + 1]!.val = .scalar c s) →
      b ≤ k + 2 ∨ (k + 2 < b ∧ tokens[k + 2]!.val = .value)) ∧
  (∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .value →
      b ≤ k + 1 ∨ (k + 1 < b ∧ isFlowContentStart tokens[k + 1]!.val)) ∧
  (∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .value →
      (∃ c s, tokens[k + 1]!.val = .scalar c s) →
      b ≤ k + 1 ∨ (k + 2 ≤ b ∧ (tokens[k + 2]!.val = .flowEntry ∨ (tokens[k + 2]!.val = .flowMappingEnd ∧ k + 2 = b)))) ∧
  (∀ k j, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .key →
      k + 1 < j → j < b → flowBracketDelta tokens[j]!.val = -1 → flowBracketBalance tokens a (j + 1) = 0 →
      b ≤ j + 1 ∨ (j + 1 < b ∧ tokens[j + 1]!.val = .value)) ∧
  (∀ k j, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .value →
      k + 1 < j → j < b → flowBracketDelta tokens[j]!.val = -1 → flowBracketBalance tokens a (j + 1) = 0 →
      j + 1 ≤ b ∧ (tokens[j + 1]!.val = .flowEntry ∨ (tokens[j + 1]!.val = .flowMappingEnd ∧ j + 1 = b)))

/-- **The boundary-robust map separator carrier** — the `'` variant of `MapInteriorSeparators`
    (`:187`), identical except it threads the robust `MapGrammarFacts'`. Over `[lo,hi)`: every
    map-typed depth-`0`-balanced bracket-interior sub-window `[a,b) ⊆ [lo,hi)` satisfies the robust
    facts. The body is `lo`/`hi`-free except through the domain bounds, so it restricts to sub-windows
    for free (the descend/advance edges below). Unlike the strict carrier, this one is INHABITED (the
    `Tests/` probe survives the window-close boundary the strict carrier could not). -/
def MapInteriorSeparators' (tokens : Array (Positioned YamlToken)) (lo hi : Nat) : Prop :=
  ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → MapTypedInterior tokens a b → MapGrammarFacts' tokens a b

/-- **Subset restriction (the descend/advance edge, robust form).** The exact mirror of
    `MapInteriorSeparators_narrow` (`:193`) — the quantifier body is reused verbatim, only the domain
    shrinks; `_narrow` never inspects the bundled facts, so the proof is byte-identical regardless of
    fragile-vs-robust payload. -/
theorem MapInteriorSeparators'_narrow {tokens : Array (Positioned YamlToken)} {lo hi lo' hi' : Nat}
    (h_lo : lo ≤ lo') (h_hi : hi' ≤ hi)
    (h : MapInteriorSeparators' tokens lo hi) :
    MapInteriorSeparators' tokens lo' hi' := by
  intro a b ha hab hb hgate
  exact h a b (Nat.le_trans h_lo ha) hab (Nat.le_trans hb h_hi) hgate

/-- **The DESCEND edge (robust form).** Descending into a nested bracket interior `[lo',hi') ⊆ [lo,hi)`
    preserves the carrier by subset restriction (mirror of `MapInteriorSeparators_descend`, `:202`). -/
theorem MapInteriorSeparators'_descend {tokens : Array (Positioned YamlToken)} {lo hi lo' hi' : Nat}
    (h_lo : lo ≤ lo') (h_hi : hi' ≤ hi)
    (h : MapInteriorSeparators' tokens lo hi) :
    MapInteriorSeparators' tokens lo' hi' :=
  MapInteriorSeparators'_narrow h_lo h_hi h

/-- **The ADVANCE edge (robust form).** Advancing past a separator at `m` to the tail `[m+1, hi)`
    preserves the carrier by subset restriction, `hi` unchanged (mirror of
    `MapInteriorSeparators_advance`, `:210`). -/
theorem MapInteriorSeparators'_advance {tokens : Array (Positioned YamlToken)} {lo hi m : Nat}
    (h_lo : lo ≤ m + 1)
    (h : MapInteriorSeparators' tokens lo hi) :
    MapInteriorSeparators' tokens (m + 1) hi :=
  MapInteriorSeparators'_narrow h_lo (Nat.le_refl hi) h

/-! ### The MATCHING-CLOSE-pinned map separator carrier — the SECOND fragility axis (R548)

R547 refuted the robust carrier `MapInteriorSeparators'` (`:280`) on the bracket-VALUED map
`{a:[1], b:2}`: its `MapGrammarFacts'` conjuncts 5/6 fire on a GENERIC interior closer `j` with no
guard that the trigger's successor `tokens[k+1]` is a bracket-start. R548 PROBES the obvious fix —
adding the `MapBodyProps` M5/M8 bracket-start guard `tokens[k+1] ∈ {.flowSequenceStart, .flowMappingStart}`
— and finds it INSUFFICIENT (inhabitation-debt rule 2: probe the fix on a fixture where the conjunct
fires NON-vacuously, BEFORE building on it). On `{a:[1], [2]:3}` the value marker `k = 4` has a
bracket-start at `k+1` (guard fires), but a GENERIC closer `j = 12` — the matching close of the *next
entry's complex KEY* `[2]` — also returns the window-relative balance to `0`, and conjunct 6 then
demands `.flowEntry` at `j+1 = 13` where the stream has `.value`. FALSE. So conjuncts 5/6 have TWO
orthogonal fragility axes: (i) the trigger guard (R547's diagnosis), and (ii) the CLOSER must be
pinned to the trigger's OWN matching close, not any later depth-0-returning closer.

This block lands the corrected predicate as a NEW ADDITIVE PARALLEL TYPE `MapGrammarFacts''`
([[ref-additive-parallel-type-over-shared-edit]] — never an edit to the shared `MapGrammarFacts'`,
whose R542–R546 assembler/connector/bridge consumers depend on its exact shape). Conjuncts 1–4 are the
robust `MapGrammarFacts'` conjuncts verbatim; conjuncts 5/6 are re-keyed to the FULL `MapBodyProps`
M5/M8 EXISTENTIAL form — guard on `tokens[k+1]`, then `∃ j` that is the bracket's OWN matching close
(`flowBracketBalance tokens (k+2) j = 0` with the Dyck floor `∀ p ∈ [k+2,j], flowBracketBalance (k+2) p ≥ 0`,
which together pin `j` to the *first* return to depth 0 and so EXCLUDE the spurious `j = 12`) — and
KEEP the R541 window-close escape on both the trigger (`b ≤ k+1`) and the successor
(`b ≤ j+1 ∨ …`) so the carrier still survives the degenerate cut windows R541 made robust. The
existential matching-close form is exactly what `mapWindow_mapBodyProps_general` already PRODUCES off
emission (M5/M8), so the eventual `mapRoot_mapGrammarFacts''` producer derives from it; `MapGrammarFacts''`
is strictly WEAKER than M5/M8 (the escapes only add disjuncts), so the producer takes the genuine arm.

INHABITATION-DEBT discipline ([[ref-inhabitation-debt-validate-target-defs]]): probed AT BIRTH in
`Tests/Reflections/MapCarrierRobustInhabitation.lean` (R548) on FOUR fixtures — `{a:1}` (5/6 vacuous),
`{a:[1], b:2}` (the EXACT fixture R547 refuted `MapGrammarFacts'` on, now TRUE — conjunct 6 fires
existentially picking the value's own close `j=7`), `{[1]:2}` (conjunct 5 fires at a complex key), and
`{a:[1], [2]:3}` (BOTH fire; the existential picks the right `j`, where the generic-guard form is
refuted) — all grounded against real `scanFiltered (emit ·)`. Verified-but-unconsumed: the rebase,
assembler, producer, and consumer-field reconciliation against this corrected target are later bricks;
references no sorry site; frontier sorry count unchanged at 4. -/

/-- **The six map-grammar facts with conjuncts 5/6 MATCHING-CLOSE-pinned** — the `''` variant of
    `MapGrammarFacts'` (`:256`). Conjuncts 1–4 are the robust `MapGrammarFacts'` conjuncts verbatim.
    Conjuncts 5/6 are re-keyed to the `MapBodyProps` M5/M8 form (`ParserGrammableBase.lean:1240`/`:1264`):
    a bracket-start GUARD on `tokens[k+1]`, an EXISTENTIAL `j` pinned to that bracket's own matching
    close (balance-from-`k+2` zero + Dyck floor), and the R541 window-close escapes on trigger and
    successor. This fires only on a COMPLEX KEY / BRACKET VALUE whose `j` is its OWN close — never on a
    later unrelated closer (the R548 fix for the second fragility axis). -/
def MapGrammarFacts'' (tokens : Array (Positioned YamlToken)) (a b : Nat) : Prop :=
  (∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .key →
      b ≤ k + 1 ∨ (k + 1 < b ∧ isFlowContentStart tokens[k + 1]!.val)) ∧
  (∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .key →
      (∃ c s, tokens[k + 1]!.val = .scalar c s) →
      b ≤ k + 2 ∨ (k + 2 < b ∧ tokens[k + 2]!.val = .value)) ∧
  (∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .value →
      b ≤ k + 1 ∨ (k + 1 < b ∧ isFlowContentStart tokens[k + 1]!.val)) ∧
  (∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .value →
      (∃ c s, tokens[k + 1]!.val = .scalar c s) →
      b ≤ k + 1 ∨ (k + 2 ≤ b ∧ (tokens[k + 2]!.val = .flowEntry ∨ (tokens[k + 2]!.val = .flowMappingEnd ∧ k + 2 = b)))) ∧
  (∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .key →
      (tokens[k + 1]!.val = .flowSequenceStart ∨ tokens[k + 1]!.val = .flowMappingStart) →
      b ≤ k + 1 ∨ (∃ j, k + 1 < j ∧ j < b ∧
        ((tokens[k + 1]!.val = .flowSequenceStart ∧ tokens[j]!.val = .flowSequenceEnd) ∨
         (tokens[k + 1]!.val = .flowMappingStart ∧ tokens[j]!.val = .flowMappingEnd)) ∧
        flowBracketBalance tokens (k + 2) j = 0 ∧
        (b ≤ j + 1 ∨ (j + 1 < b ∧ tokens[j + 1]!.val = .value)) ∧
        (∀ p, k + 2 ≤ p → p ≤ j → flowBracketBalance tokens (k + 2) p ≥ 0))) ∧
  (∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .value →
      (tokens[k + 1]!.val = .flowSequenceStart ∨ tokens[k + 1]!.val = .flowMappingStart) →
      b ≤ k + 1 ∨ (∃ j, k + 1 < j ∧ j < b ∧
        ((tokens[k + 1]!.val = .flowSequenceStart ∧ tokens[j]!.val = .flowSequenceEnd) ∨
         (tokens[k + 1]!.val = .flowMappingStart ∧ tokens[j]!.val = .flowMappingEnd)) ∧
        flowBracketBalance tokens (k + 2) j = 0 ∧
        (b ≤ j + 1 ∨ (j + 1 ≤ b ∧ (tokens[j + 1]!.val = .flowEntry ∨ (tokens[j + 1]!.val = .flowMappingEnd ∧ j + 1 = b)))) ∧
        (∀ p, k + 2 ≤ p → p ≤ j → flowBracketBalance tokens (k + 2) p ≥ 0)))

/-- **The matching-close-pinned map separator carrier** — the `''` variant of `MapInteriorSeparators'`
    (`:280`), threading the corrected `MapGrammarFacts''`. Over `[lo,hi)`: every map-typed
    depth-`0`-balanced bracket-interior sub-window `[a,b) ⊆ [lo,hi)` satisfies the corrected facts.
    Unlike `MapInteriorSeparators'`, this one is INHABITED on bracket-bearing maps (the `Tests/` probe
    holds on `{a:[1],b:2}`, `{[1]:2}`, `{a:[1],[2]:3}`, where `MapInteriorSeparators'` is refuted). -/
def MapInteriorSeparators'' (tokens : Array (Positioned YamlToken)) (lo hi : Nat) : Prop :=
  ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → MapTypedInterior tokens a b → MapGrammarFacts'' tokens a b

/-- **Subset restriction (the descend/advance edge, matching-close-pinned form).** The exact mirror of
    `MapInteriorSeparators'_narrow` (`:287`) — the quantifier body is reused verbatim, only the domain
    shrinks; `_narrow` never inspects the bundled facts, so the proof is byte-identical regardless of
    payload. -/
theorem MapInteriorSeparators''_narrow {tokens : Array (Positioned YamlToken)} {lo hi lo' hi' : Nat}
    (h_lo : lo ≤ lo') (h_hi : hi' ≤ hi)
    (h : MapInteriorSeparators'' tokens lo hi) :
    MapInteriorSeparators'' tokens lo' hi' := by
  intro a b ha hab hb hgate
  exact h a b (Nat.le_trans h_lo ha) hab (Nat.le_trans hb h_hi) hgate

/-- **The PRODUCER of the corrected facts off emission's structural bundle** — `MapGrammarFacts''` is a
    structural WEAKENING of `MapBodyProps` (`ParserGrammableBase.lean:1220`), so it follows from it on
    the SAME window `[lo,hi)`.  This is the artifact that GROUNDS the R548 corrected target in what
    real emission actually yields: `MapBodyProps`'s M5/M8 (`key_bracket_value`/`value_bracket_succ`) are
    the existential matching-close-pinned facts that conjuncts 5/6 were re-keyed to, and M3/M4/M6/M7
    feed conjuncts 1–4.  The mapping is exact:

      * conjunct 1 ← M3 `key_content`        (`k+1 < hi ∧ isFlowContentStart` ⟹ the interior arm)
      * conjunct 2 ← M4 `key_scalar_value`   (`k+2 < hi ∧ .value`)
      * conjunct 3 ← M6 `value_content`
      * conjunct 4 ← M7 `value_scalar_succ`  (`k+2 ≤ hi ∧ (.flowEntry ∨ (.flowMappingEnd ∧ k+2=hi))`)
      * conjunct 5 ← M5 `key_bracket_value`  (`∃ j` matching close + `j+1 < hi ∧ .value` ⟹ interior arm)
      * conjunct 6 ← M8 `value_bracket_succ` (`∃ j` matching close + `j+1 ≤ hi ∧ (.flowEntry ∨ …)`)

    Every conjunct takes the INTERIOR (`Or.inr`) arm; the `MapGrammarFacts''` window-close escapes
    (`b ≤ k+1`, `b ≤ j+1`) are slack `MapBodyProps` never needs (it is the stronger, escape-free form on
    a genuine body window).  So `MapGrammarFacts''` is strictly WEAKER than `MapBodyProps`, and this
    producer is correct-by-construction (a pure repackaging of the M-fields).  Since
    `mapWindow_mapBodyProps_general` (`:2912`) already produces `MapBodyProps` off emission, the eventual
    `mapRoot_mapGrammarFacts''` derives from this composition — the inhabitation of `MapGrammarFacts''`
    at real emission, not just on fixtures, lands HERE ([[ref-inhabitation-debt-validate-target-defs]],
    R545 "produce the witness first").

    INHABITATION-DEBT discipline: probed in `Tests/Reflections/MapCarrierRobustInhabitation.lean` (R549)
    by ROUTING a hand-built concrete `MapBodyProps fixtureMapSeqVal 2 13` (`{a:[1], b:2}`, the
    `#guard`-grounded emission where M8 FIRES at the value's bracket with an INTERIOR close `j=7`,
    `j+1 = 8 < 13` — the exact arm R547/R548 found buggy) through this producer, recovering the same
    `MapGrammarFacts''` the R548 birth-probe proved directly.  The witness is built INDEPENDENTLY (not
    projected), so the round-trip is a genuine non-vacuous reachability check of the producer's domain
    (rule 3).  Verified-but-unconsumed: references no sorry site; frontier sorry count unchanged at 4. -/
theorem mapGrammarFacts''_of_mapBodyProps (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h : MapBodyProps tokens lo hi) :
    MapGrammarFacts'' tokens lo hi := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- conjunct 1: key → content-start  (M3)
  · intro k hlo hhi hbal htok
    exact Or.inr (h.key_content k hlo hhi hbal htok)
  -- conjunct 2: key + scalar → value  (M4)
  · intro k hlo hhi hbal htok hsc
    exact Or.inr (h.key_scalar_value k hlo hhi hbal htok hsc)
  -- conjunct 3: value → content-start  (M6)
  · intro k hlo hhi hbal htok
    exact Or.inr (h.value_content k hlo hhi hbal htok)
  -- conjunct 4: value + scalar → FE/mapEnd  (M7)
  · intro k hlo hhi hbal htok hsc
    exact Or.inr (h.value_scalar_succ k hlo hhi hbal htok hsc)
  -- conjunct 5: key + bracket → ∃ j matching close, value successor  (M5)
  · intro k hlo hhi hbal htok hbr
    obtain ⟨j, hj1, hj2, hmatch, hbalj, hj3, hval, hdyck⟩ :=
      h.key_bracket_value k hlo hhi hbal htok hbr
    exact Or.inr ⟨j, hj1, hj2, hmatch, hbalj, Or.inr ⟨hj3, hval⟩, hdyck⟩
  -- conjunct 6: value + bracket → ∃ j matching close, FE/mapEnd successor  (M8)
  · intro k hlo hhi hbal htok hbr
    obtain ⟨j, hj1, hj2, hmatch, hbalj, hj3, hsucc, hdyck⟩ :=
      h.value_bracket_succ k hlo hhi hbal htok hbr
    exact Or.inr ⟨j, hj1, hj2, hmatch, hbalj, Or.inr ⟨hj3, hsucc⟩, hdyck⟩

/-- **`MapGrammarFacts'` RE-BASING** — the robust analog of `bodySuccFact_rebase` (`:1940`), bundled
    over all six conjuncts. On a sub-window `[a,b) ⊆ [loS,hiS)` re-seated to the enclosing map's top
    level (`flowBracketBalance tokens loS a = 0`), the robust facts follow from the ENCLOSING window's
    robust facts: each conjunct re-bases its depth premise by balance composition
    (`flowBracketBalance_compose`), fires the enclosing conjunct, and collapses its window-close escape
    `hiS ≤ p` down to `b ≤ p` (because `b ≤ hiS`), relocating the strict bound to `b` exactly as
    `bodySuccFact_rebase` does. This is the mechanism the strict `MapGrammarFacts` could NOT support —
    there is no fragile analog (the fragile rebase is concretely refuted, R540) — and it is precisely
    what the boundary-robust escape BUYS. This is the map twin of the seq carrier's
    `bodySuccFact_rebase`/`noTrailingSepFact_rebase` pair, in a single bundled lemma; it is the
    pre-condition for the eventual `mapInteriorSeparators'_of_enclosing_provider` assembler. -/
theorem mapGrammarFacts_rebase' (tokens : Array (Positioned YamlToken)) (loS a b hiS : Nat)
    (h_loS_a : loS ≤ a) (h_b_hiS : b ≤ hiS)
    (h_bal0 : flowBracketBalance tokens loS a = 0)
    (h_enc : MapGrammarFacts' tokens loS hiS) :
    MapGrammarFacts' tokens a b := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h_enc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- conjunct 1: key → content at k+1
  · intro k hak hkb hbalk htok
    have hk_hiS : k < hiS := Nat.lt_of_lt_of_le hkb h_b_hiS
    have hbal_enc : flowBracketBalance tokens loS k = 0 := by
      have hc := flowBracketBalance_compose tokens loS a k h_loS_a (by omega)
      rw [h_bal0, hbalk] at hc; omega
    rcases e1 k (Nat.le_trans h_loS_a hak) hk_hiS hbal_enc htok with h | ⟨_, hQ⟩
    · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge (k + 1) b with hb | hb
      · exact Or.inr ⟨hb, hQ⟩
      · exact Or.inl (by omega)
  -- conjunct 2: key + scalar → value at k+2
  · intro k hak hkb hbalk htok hsc
    have hk_hiS : k < hiS := Nat.lt_of_lt_of_le hkb h_b_hiS
    have hbal_enc : flowBracketBalance tokens loS k = 0 := by
      have hc := flowBracketBalance_compose tokens loS a k h_loS_a (by omega)
      rw [h_bal0, hbalk] at hc; omega
    rcases e2 k (Nat.le_trans h_loS_a hak) hk_hiS hbal_enc htok hsc with h | ⟨_, hQ⟩
    · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge (k + 2) b with hb | hb
      · exact Or.inr ⟨hb, hQ⟩
      · exact Or.inl (by omega)
  -- conjunct 3: value → content at k+1
  · intro k hak hkb hbalk htok
    have hk_hiS : k < hiS := Nat.lt_of_lt_of_le hkb h_b_hiS
    have hbal_enc : flowBracketBalance tokens loS k = 0 := by
      have hc := flowBracketBalance_compose tokens loS a k h_loS_a (by omega)
      rw [h_bal0, hbalk] at hc; omega
    rcases e3 k (Nat.le_trans h_loS_a hak) hk_hiS hbal_enc htok with h | ⟨_, hQ⟩
    · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge (k + 1) b with hb | hb
      · exact Or.inr ⟨hb, hQ⟩
      · exact Or.inl (by omega)
  -- conjunct 4: value + scalar → flowEntry/mapEnd at k+2
  · intro k hak hkb hbalk htok hsc
    have hk_hiS : k < hiS := Nat.lt_of_lt_of_le hkb h_b_hiS
    have hbal_enc : flowBracketBalance tokens loS k = 0 := by
      have hc := flowBracketBalance_compose tokens loS a k h_loS_a (by omega)
      rw [h_bal0, hbalk] at hc; omega
    rcases e4 k (Nat.le_trans h_loS_a hak) hk_hiS hbal_enc htok hsc with h | ⟨_, hinner⟩
    · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge (k + 1) b with hb | hb
      · refine Or.inr ⟨by omega, ?_⟩
        rcases hinner with hfe | ⟨hme, heq⟩
        · exact Or.inl hfe
        · exact Or.inr ⟨hme, by omega⟩
      · exact Or.inl (by omega)
  -- conjunct 5: key, closer at j → value at j+1
  · intro k j hak hkb hbalk htok hkj hjb hdelta hbalj
    have hk_hiS : k < hiS := Nat.lt_of_lt_of_le hkb h_b_hiS
    have hj_hiS : j < hiS := Nat.lt_of_lt_of_le hjb h_b_hiS
    have hbal_enc_k : flowBracketBalance tokens loS k = 0 := by
      have hc := flowBracketBalance_compose tokens loS a k h_loS_a (by omega)
      rw [h_bal0, hbalk] at hc; omega
    have hbal_enc_j : flowBracketBalance tokens loS (j + 1) = 0 := by
      have hc := flowBracketBalance_compose tokens loS a (j + 1) h_loS_a (by omega)
      rw [h_bal0, hbalj] at hc; omega
    rcases e5 k j (Nat.le_trans h_loS_a hak) hk_hiS hbal_enc_k htok hkj hj_hiS hdelta hbal_enc_j with
      h | ⟨_, hQ⟩
    · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge (j + 1) b with hb | hb
      · exact Or.inr ⟨hb, hQ⟩
      · exact Or.inl (by omega)
  -- conjunct 6: value, closer at j → flowEntry/mapEnd at j+1 (already robust; reused verbatim)
  · intro k j hak hkb hbalk htok hkj hjb hdelta hbalj
    have hk_hiS : k < hiS := Nat.lt_of_lt_of_le hkb h_b_hiS
    have hj_hiS : j < hiS := Nat.lt_of_lt_of_le hjb h_b_hiS
    have hbal_enc_k : flowBracketBalance tokens loS k = 0 := by
      have hc := flowBracketBalance_compose tokens loS a k h_loS_a (by omega)
      rw [h_bal0, hbalk] at hc; omega
    have hbal_enc_j : flowBracketBalance tokens loS (j + 1) = 0 := by
      have hc := flowBracketBalance_compose tokens loS a (j + 1) h_loS_a (by omega)
      rw [h_bal0, hbalj] at hc; omega
    obtain ⟨_, hinner⟩ :=
      e6 k j (Nat.le_trans h_loS_a hak) hk_hiS hbal_enc_k htok hkj hj_hiS hdelta hbal_enc_j
    refine ⟨by omega, ?_⟩
    rcases hinner with hfe | ⟨hme, heq⟩
    · exact Or.inl hfe
    · exact Or.inr ⟨hme, by omega⟩

/-- **Gated close-containment — a depth-`0` bracket-open's matching close lands INSIDE the gated window
    (R551).** The genuinely-NEW arithmetic kernel the `''` carrier's rebase needs, and the realization
    of the gate hypothesis R549 predicted (`[[ref-inhabitation-debt-validate-target-defs]]`, R549 rule-4
    note: "the `rebase''` will need an added gate hypothesis").

    **Why the `''` rebase needs this and `mapGrammarFacts_rebase'` (`:469`) did not.** The single-prime
    conjuncts 5/6 are FLAT (`∀ k j, … → j < b → …`): the close `j` arrives as a parameter with `j < b`
    GIVEN, so rebase' just re-fires the enclosing fact and never has to LOCATE the close. The corrected
    `''` conjuncts 5/6 (`:365`) are EXISTENTIAL — they must PRODUCE `∃ j, … ∧ j < b ∧ …`. Rebasing the
    enclosing window's witness `j < hiS` down to `j < b` is exactly the locate the flat form skipped,
    and it is FALSE without a gate: a bracket opened inside `[a,b)` could close past `b` if `[a,b)`
    were not itself balanced. The gate `flowBracketBalance tokens a b = 0` is what confines it.

    **The argument (pure `flowBracketBalance_compose` + `omega`, no per-token reasoning).** At `k+2` the
    open bracket has driven the absolute balance to `1` (`h_open`); the enclosing existential's Dyck floor
    `h_dyck` keeps the balance from `k+2` at `≥ 0` everywhere up to `j`.  If the close `j` were at or past
    `b` (`b ≤ j`), then `b ∈ [k+2, j]`, so `flowBracketBalance tokens (k+2) b ≥ 0`, hence
    `flowBracketBalance tokens a b = flowBracketBalance tokens a (k+2) + flowBracketBalance tokens (k+2) b
    = 1 + (≥0) ≥ 1`, contradicting the gate `= 0`.  So `j < b`.  (Notably this needs NEITHER the close's
    own balance `flowBracketBalance (k+2) j = 0` NOR `k+1 < j` — only that the region stays `≥ 0` and the
    window balances to `0`; the gate is the sole load-bearing extra over rebase'.)

    **The [[ref-parametric-assembler-extraction]] split.**  This is the ASSEMBLE/kernel half — the
    arithmetic confinement — taking the depth-`1` opener fact `h_open : flowBracketBalance tokens a (k+2)
    = 1` as a hypothesis.  The PRODUCE-primitive half (deriving `h_open` from `htok : tokens[k]!.val ∈
    {.key,.value}` ⟹ δ`0` and `hbr : tokens[k+1]!.val ∈ {seqStart,mapStart}` ⟹ δ`+1` via
    `flowBracketBalance_single`, with the `k+1 < size` bound) is the residual the eventual
    `mapGrammarFacts_rebase''` discharges inside conjuncts 5/6 before calling this.  Kept separate so this
    kernel stays pure arithmetic, lands high-confidence, and is probe-able by itself.

    INHABITATION-DEBT discipline (`[[ref-inhabitation-debt-validate-target-defs]]`, rule 3 — probe a
    lemma's HYPOTHESES are PRODUCIBLE before consumers build on it): probed in
    `Tests/Reflections/MapCarrierRobustInhabitation.lean` (R551) by
    `mapBracketClose_lt_of_gate_bracketVal`, which routes the GENUINE value-bracket of `{a:[1],b:2}`
    (`k=4`, `k+2=6`, `j=7`, gate window `[2,13)`, all facts `decide`-grounded against real emission) and
    recovers `7 < 13` — confirming every hypothesis (`h_open`, `h_dyck`, the gate) is satisfiable on real
    data where the bracket genuinely FIRES, so this is not the dead-hypothesis trap R550 caught one level
    up.  Verified-but-unconsumed (its consumer `mapGrammarFacts_rebase''` does not exist yet); references
    no sorry site; frontier sorry count unchanged at 4. -/
theorem mapBracketClose_lt_of_gate (tokens : Array (Positioned YamlToken)) (a b k j : Nat)
    (h_ak : a ≤ k) (h_k2_b : k + 2 ≤ b)
    (h_gate_bal : flowBracketBalance tokens a b = 0)
    (h_open : flowBracketBalance tokens a (k + 2) = 1)
    (h_dyck : ∀ p, k + 2 ≤ p → p ≤ j → flowBracketBalance tokens (k + 2) p ≥ 0) :
    j < b := by
  rcases Nat.lt_or_ge j b with hjb | hbj
  · exact hjb
  · -- b ≤ j: the open bracket is still open at b, so the window cannot balance to 0
    have h_dyck_b : flowBracketBalance tokens (k + 2) b ≥ 0 := h_dyck b h_k2_b hbj
    have h_comp : flowBracketBalance tokens a b
        = flowBracketBalance tokens a (k + 2) + flowBracketBalance tokens (k + 2) b :=
      flowBracketBalance_compose tokens a (k + 2) b (by omega) h_k2_b
    rw [h_open, h_gate_bal] at h_comp
    omega

/-- **The depth-`1` opener-balance PRODUCE-primitive (R552)** — derives the very `h_open :
    flowBracketBalance tokens a (k+2) = 1` that `mapBracketClose_lt_of_gate` (`:595`) CONSUMES, from the
    token deltas at `k` and `k+1`.  This is the produce-half the R551 split deferred
    (`[[ref-parametric-assembler-extraction]]`): the close kernel took `h_open` as a hypothesis to stay
    pure arithmetic; THIS kernel is what `mapGrammarFacts_rebase''` calls inside conjuncts 5/6 to
    discharge it before invoking the close kernel — the two compose into the existential `j < b`
    relocation.

    **The argument (the one-step balance recurrence, mirroring `flowBracketBalance_matching_close`'s
    `step`, `ParserGrammableBase.lean:635`).** Stepping the absolute balance one token at a time,
    `flowBracketBalance a (i+1) = flowBracketBalance a i + flowBracketDelta tokens[i]!.val` (by
    `flowBracketBalance_compose` + `flowBracketBalance_single`, bridging `tokens.toList[i] ↔ tokens[i]!`
    via `Array.getElem_toList`/`getElem!_pos`).  Applied at `k` then `k+1`: from `flowBracketBalance a k
    = 0` (`h_balk`), the trigger's δ`0` (`h_key` — a `.key` OR `.value` marker, both non-brackets, so
    this single kernel serves BOTH conjuncts 5 and 6), and the bracket-start's δ`+1` (`h_open_delta` —
    `flowSequenceStart`/`flowMappingStart`), the balance reaches `0 + 0 + 1 = 1` at `k+2`.

    **The NEW requirement-class the close kernel and `rebase'` did NOT carry: a SIZE bound.**
    `mapBracketClose_lt_of_gate` and `mapGrammarFacts_rebase'` reason purely by `flowBracketBalance_compose`
    over GIVEN endpoints, which is size-free.  Reading a token's individual contribution (`flowBracketDelta
    tokens[i]!.val` via `flowBracketBalance_single`) needs an IN-BOUNDS witness `i < tokens.size` — so this
    primitive, and only this primitive, takes `h_k1_size : k + 1 < tokens.size`.  Localizing the size
    obligation HERE keeps the close kernel and the conjunct-1–4 rebase plumbing size-free; the eventual
    `mapGrammarFacts_rebase''` sources `k + 1 < tokens.size` from `k + 1 < j < hiS ≤ tokens.size`
    (`hiS ≤ tokens.size` being the genuine-emission bound the root window `[2, size-2)` trivially meets —
    the seq twin's dispatcher carried exactly this `hi ≤ tokens.size`, `:707`).

    INHABITATION-DEBT discipline (`[[ref-inhabitation-debt-validate-target-defs]]`, rule 3 — probe the
    new hypothesis is PRODUCIBLE, not a dead gate): probed in
    `Tests/Reflections/MapCarrierRobustInhabitation.lean` (R552) by `mapBracketOpen_balance_one_bracketVal`,
    which routes the GENUINE value-bracket of `{a:[1],b:2}` (`k=4` `.value` δ`0`, `[` at index `5` δ`+1`,
    `flowBracketBalance 2 4 = 0`, size bound `5 < 15`) through this kernel and RECOVERS `flowBracketBalance
    2 6 = 1` — the exact `h_open` the R551 close-kernel probe asserted by `decide`, now PRODUCED from the
    deltas, closing the producer→consumer loop on real emission.  Verified-but-unconsumed (its consumer
    `mapGrammarFacts_rebase''` does not exist yet); references no sorry site; frontier sorry count
    unchanged at 4. -/
theorem mapBracketOpen_balance_one (tokens : Array (Positioned YamlToken)) (a k : Nat)
    (h_ak : a ≤ k) (h_k1_size : k + 1 < tokens.size)
    (h_balk : flowBracketBalance tokens a k = 0)
    (h_key : flowBracketDelta tokens[k]!.val = 0)
    (h_open_delta : flowBracketDelta tokens[k + 1]!.val = 1) :
    flowBracketBalance tokens a (k + 2) = 1 := by
  -- One-step balance recurrence (mirrors `flowBracketBalance_matching_close`'s `step`).
  have step : ∀ i, a ≤ i → i < tokens.size →
      flowBracketBalance tokens a (i + 1) =
        flowBracketBalance tokens a i + flowBracketDelta tokens[i]!.val := by
    intro i h_ai h_sz
    rw [flowBracketBalance_compose tokens a i (i + 1) h_ai (by omega)]
    have hlen : i < tokens.toList.length := by rw [Array.length_toList]; exact h_sz
    rw [flowBracketBalance_single tokens i hlen]
    have h1 : tokens.toList[i]'hlen = tokens[i] := Array.getElem_toList h_sz
    have h2 : tokens[i] = tokens[i]! := (getElem!_pos tokens i h_sz).symm
    rw [h1, h2]
  have h_k1 : flowBracketBalance tokens a (k + 1)
      = flowBracketBalance tokens a k + flowBracketDelta tokens[k]!.val :=
    step k h_ak (by omega)
  have h_k2 : flowBracketBalance tokens a (k + 2)
      = flowBracketBalance tokens a (k + 1) + flowBracketDelta tokens[k + 1]!.val :=
    step (k + 1) (by omega) h_k1_size
  rw [h_balk, h_key] at h_k1
  rw [h_open_delta] at h_k2
  omega

/-- **`MapGrammarFacts''` RE-BASING under a GATE (R553)** — the matching-close-pinned analog of
    `mapGrammarFacts_rebase'` (`:469`), and the artifact the two R551/R552 kernels were built to
    serve.  On a sub-window `[a,b) ⊆ [loS,hiS)` re-seated to the enclosing map's top level
    (`flowBracketBalance tokens loS a = 0`), the corrected facts follow from the ENCLOSING window's
    corrected facts — BUT only with two hypotheses the single-prime rebase did not need:

      * **a GATE** `h_gate : MapTypedInterior tokens a b` (R549/R551 predicted).  The single-prime
        conjuncts 5/6 are FLAT (`∀ k j, … → j < b → …`): the close `j` arrives as a parameter with
        `j < b` GIVEN, so `rebase'` never LOCATES the close.  The `''` conjuncts 5/6 (`:365`) are
        EXISTENTIAL — they must PRODUCE `∃ j, … ∧ j < b ∧ …`, relocating the enclosing witness
        `j < hiS` down to `j < b`.  That relocation is FALSE without a gate (a bracket opened in
        `[a,b)` could close past `b`); `mapBracketClose_lt_of_gate` (`:595`) confines it using the
        gate's balance `flowBracketBalance tokens a b = 0` (`h_gate.1`) and the enclosing
        existential's own Dyck floor.
      * **a SIZE bound** `h_hiS_size : hiS ≤ tokens.size` (R552).  Producing the depth-`1` opener
        fact `h_open : flowBracketBalance tokens a (k+2) = 1` reads the trigger's δ`0` and the
        bracket-start's δ`+1` individually via `mapBracketOpen_balance_one` (`:647`), which needs
        `k + 1 < tokens.size` — sourced HERE from `k + 1 < j < hiS ≤ tokens.size`.

    **Structure.**  Conjuncts 1–4 are the `mapGrammarFacts_rebase'` conjuncts VERBATIM (the `''`
    conjuncts 1–4 are byte-identical to the robust ones — escapes + balance-rebase by
    `flowBracketBalance_compose`, no gate, no size).  Conjuncts 5/6: re-base the trigger balance to
    `loS`, fire the enclosing existential conjunct, and — on the genuine `k + 1 < b` arm — derive the
    δ facts from `htok`/`hbr` (`tokens[k]!.val = .key`/`.value` ⟹ δ`0`; `tokens[k+1]!.val =
    seqStart/mapStart` ⟹ δ`+1`), call `mapBracketOpen_balance_one` for `h_open`, then
    `mapBracketClose_lt_of_gate` for the relocated `j < b`, reusing the enclosing existential's
    matching-close witness / close-balance / Dyck floor verbatim and collapsing the successor escape
    `hiS ≤ j+1` down to `b ≤ j+1` exactly as `rebase'` does.

    This is the map twin of the seq carrier's `bodySuccFact_rebase`/`noTrailingSepFact_rebase` pair
    for the CORRECTED existential facts, and the pre-condition for the eventual
    `mapInteriorSeparators''_of_enclosing_provider` assembler (the `''` mirror of `:698`).  It is the
    mechanism the strict `MapGrammarFacts` could never support (R540) and the single-prime
    `MapGrammarFacts'` supported only because its 5/6 were the wrong, flat shape (R547).

    INHABITATION-DEBT discipline ([[ref-inhabitation-debt-validate-target-defs]], rule 3 — probe the
    composition's HYPOTHESES are PRODUCIBLE on real data before consumers build on it): probed in
    `Tests/Reflections/MapCarrierRobustInhabitation.lean` (R553) by `mapGrammarFacts_rebase''_bracketVal`
    and `mapGrammarFacts_rebase''_mixed`, which route the GENUINE map bodies of `{a:[1],b:2}` and
    `{a:[1],[2]:3}` — gate (`mapTypedInterior_bracketVal`/`_mixed`), size bound (`decide`), and
    enclosing facts (`mapGrammarFacts''_bracketVal`/`_mixed`) all producible off real emission —
    through this rebase, recovering the corrected facts with conjunct 6 (bracketVal) and BOTH
    conjuncts 5 and 6 (mixed) firing the kernel composition (close-relocation `7 < 13`, then the
    mixed pair).  The probes are the identity rebase (`loS = a`, `hiS = b`) — the only map-typed
    window these single-level fixtures admit — but the conjunct-5/6 close-relocation still routes
    fully through both kernels; a strictly-narrowing rebase would need a nested-map fixture (a deeper
    future probe).  Verified-but-unconsumed (the `''` provider/assembler it feeds does not exist yet);
    references no sorry site; frontier sorry count unchanged at 4. -/
theorem mapGrammarFacts_rebase'' (tokens : Array (Positioned YamlToken)) (loS a b hiS : Nat)
    (h_loS_a : loS ≤ a) (h_b_hiS : b ≤ hiS)
    (h_hiS_size : hiS ≤ tokens.size)
    (h_bal0 : flowBracketBalance tokens loS a = 0)
    (h_gate : MapTypedInterior tokens a b)
    (h_enc : MapGrammarFacts'' tokens loS hiS) :
    MapGrammarFacts'' tokens a b := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h_enc
  have h_gate_bal : flowBracketBalance tokens a b = 0 := h_gate.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- conjunct 1: key → content at k+1  (verbatim from `mapGrammarFacts_rebase'`)
  · intro k hak hkb hbalk htok
    have hk_hiS : k < hiS := Nat.lt_of_lt_of_le hkb h_b_hiS
    have hbal_enc : flowBracketBalance tokens loS k = 0 := by
      have hc := flowBracketBalance_compose tokens loS a k h_loS_a (by omega)
      rw [h_bal0, hbalk] at hc; omega
    rcases e1 k (Nat.le_trans h_loS_a hak) hk_hiS hbal_enc htok with h | ⟨_, hQ⟩
    · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge (k + 1) b with hb | hb
      · exact Or.inr ⟨hb, hQ⟩
      · exact Or.inl (by omega)
  -- conjunct 2: key + scalar → value at k+2  (verbatim)
  · intro k hak hkb hbalk htok hsc
    have hk_hiS : k < hiS := Nat.lt_of_lt_of_le hkb h_b_hiS
    have hbal_enc : flowBracketBalance tokens loS k = 0 := by
      have hc := flowBracketBalance_compose tokens loS a k h_loS_a (by omega)
      rw [h_bal0, hbalk] at hc; omega
    rcases e2 k (Nat.le_trans h_loS_a hak) hk_hiS hbal_enc htok hsc with h | ⟨_, hQ⟩
    · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge (k + 2) b with hb | hb
      · exact Or.inr ⟨hb, hQ⟩
      · exact Or.inl (by omega)
  -- conjunct 3: value → content at k+1  (verbatim)
  · intro k hak hkb hbalk htok
    have hk_hiS : k < hiS := Nat.lt_of_lt_of_le hkb h_b_hiS
    have hbal_enc : flowBracketBalance tokens loS k = 0 := by
      have hc := flowBracketBalance_compose tokens loS a k h_loS_a (by omega)
      rw [h_bal0, hbalk] at hc; omega
    rcases e3 k (Nat.le_trans h_loS_a hak) hk_hiS hbal_enc htok with h | ⟨_, hQ⟩
    · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge (k + 1) b with hb | hb
      · exact Or.inr ⟨hb, hQ⟩
      · exact Or.inl (by omega)
  -- conjunct 4: value + scalar → flowEntry/mapEnd at k+2  (verbatim)
  · intro k hak hkb hbalk htok hsc
    have hk_hiS : k < hiS := Nat.lt_of_lt_of_le hkb h_b_hiS
    have hbal_enc : flowBracketBalance tokens loS k = 0 := by
      have hc := flowBracketBalance_compose tokens loS a k h_loS_a (by omega)
      rw [h_bal0, hbalk] at hc; omega
    rcases e4 k (Nat.le_trans h_loS_a hak) hk_hiS hbal_enc htok hsc with h | ⟨_, hinner⟩
    · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge (k + 1) b with hb | hb
      · refine Or.inr ⟨by omega, ?_⟩
        rcases hinner with hfe | ⟨hme, heq⟩
        · exact Or.inl hfe
        · exact Or.inr ⟨hme, by omega⟩
      · exact Or.inl (by omega)
  -- conjunct 5: key + bracket-start → ∃ j matching close, value successor  (NEW: opener+close kernels)
  · intro k hak hkb hbalk htok hbr
    have hk_hiS : k < hiS := Nat.lt_of_lt_of_le hkb h_b_hiS
    have hbal_enc : flowBracketBalance tokens loS k = 0 := by
      have hc := flowBracketBalance_compose tokens loS a k h_loS_a (by omega)
      rw [h_bal0, hbalk] at hc; omega
    rcases e5 k (Nat.le_trans h_loS_a hak) hk_hiS hbal_enc htok hbr with
      hesc | ⟨j, hj1, hj2, hmatch, hbalj, hsucc, hdyck⟩
    · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge (k + 1) b with hkb_lt | hkb_ge
      · -- k+1 < b: PRODUCE the existential via the opener then the close kernel
        have h_open : flowBracketBalance tokens a (k + 2) = 1 :=
          mapBracketOpen_balance_one tokens a k hak (by omega) hbalk
            (by rw [htok]; decide) (by rcases hbr with h | h <;> rw [h] <;> decide)
        have h_jb : j < b :=
          mapBracketClose_lt_of_gate tokens a b k j hak (by omega) h_gate_bal h_open hdyck
        refine Or.inr ⟨j, hj1, h_jb, hmatch, hbalj, ?_, hdyck⟩
        rcases hsucc with h | ⟨_, hval⟩
        · exact Or.inl (by omega)
        · rcases Nat.lt_or_ge (j + 1) b with hjb_lt | hjb_ge
          · exact Or.inr ⟨hjb_lt, hval⟩
          · exact Or.inl (by omega)
      · exact Or.inl hkb_ge
  -- conjunct 6: value + bracket-start → ∃ j matching close, flowEntry/mapEnd successor  (NEW)
  · intro k hak hkb hbalk htok hbr
    have hk_hiS : k < hiS := Nat.lt_of_lt_of_le hkb h_b_hiS
    have hbal_enc : flowBracketBalance tokens loS k = 0 := by
      have hc := flowBracketBalance_compose tokens loS a k h_loS_a (by omega)
      rw [h_bal0, hbalk] at hc; omega
    rcases e6 k (Nat.le_trans h_loS_a hak) hk_hiS hbal_enc htok hbr with
      hesc | ⟨j, hj1, hj2, hmatch, hbalj, hsucc, hdyck⟩
    · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge (k + 1) b with hkb_lt | hkb_ge
      · have h_open : flowBracketBalance tokens a (k + 2) = 1 :=
          mapBracketOpen_balance_one tokens a k hak (by omega) hbalk
            (by rw [htok]; decide) (by rcases hbr with h | h <;> rw [h] <;> decide)
        have h_jb : j < b :=
          mapBracketClose_lt_of_gate tokens a b k j hak (by omega) h_gate_bal h_open hdyck
        refine Or.inr ⟨j, hj1, h_jb, hmatch, hbalj, ?_, hdyck⟩
        rcases hsucc with h | ⟨_, hinner⟩
        · exact Or.inl (by omega)
        · refine Or.inr ⟨by omega, ?_⟩
          rcases hinner with hfe | ⟨hme, heq⟩
          · exact Or.inl hfe
          · exact Or.inr ⟨hme, by omega⟩
      · exact Or.inl hkb_ge

/-- **The map ASSEMBLE half — `MapInteriorSeparators'` from a `provider`** (the boundary-robust map
    twin of `seqInteriorSeparators_of_enclosing_provider`, `:2224`). The FIRST consumer of
    `mapGrammarFacts_rebase'` (`:322`): it reduces the robust carrier — with NO further grammar
    analysis — to a `provider` that, at every gated sub-window `[a,b)`, hands back the *enclosing* map
    body `[loS,hiS) ⊇ [a,b)` re-seated at `a`'s depth (`flowBracketBalance tokens loS a = 0`), together
    with the enclosing window's bundled robust facts `MapGrammarFacts' tokens loS hiS`. The single
    bundled rebase replaces the seq side's two separate rebases (`bodySuccFact_rebase` /
    `noTrailingSepFact_rebase`) — the window-close escape is exactly what makes the rebase, and hence
    this assembler, possible (the strict `MapGrammarFacts` could NOT support it, R540).

    This is the parametric-assembler-extraction move ([[ref-parametric-assembler-extraction]]) on the
    map axis: lift the locate-the-enclosing-window reasoning into a `∀ window, gate → ∃ enclosing, …`
    hypothesis and discharge the *assemble* now (one `obtain` + one bundled rebase), splitting the map
    residual into ASSEMBLE (done, here) vs PRODUCE the `provider` (the map locator — the next brick,
    `mapEnclosingFacts'_provider_of_located` for the balance-`0` branch + a descent locator, mirroring
    `seqEnclosingFacts_provider_of_located` / `seqDescent_provider_of_located`).

    The provider HYPOTHESIS shape is satisfiable, not a trap
    ([[ref-inhabitation-debt-validate-target-defs]] rule 3 — a hypothesis with no producer is the
    alarm): `Tests/Reflections/MapCarrierRobustInhabitation.lean`'s
    `mapInteriorSeparators'_of_enclosing_provider_unit` feeds the assembler a concrete (identity)
    provider on the unit span and recovers the inhabited carrier, so the assembler is non-vacuous.
    Verified-but-unconsumed until the map `provider` lands: composes only `mapGrammarFacts_rebase'`,
    references no sorry site, frontier sorry count unchanged at 4. -/
theorem mapInteriorSeparators'_of_enclosing_provider
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (provider : ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → MapTypedInterior tokens a b →
      ∃ loS hiS, loS ≤ a ∧ b ≤ hiS ∧ flowBracketBalance tokens loS a = 0 ∧
        MapGrammarFacts' tokens loS hiS) :
    MapInteriorSeparators' tokens lo hi := by
  intro a b ha hab hb hgate
  obtain ⟨loS, hiS, h_loS_a, h_b_hiS, h_bal0, h_enc⟩ := provider a b ha hab hb hgate
  exact mapGrammarFacts_rebase' tokens loS a b hiS h_loS_a h_b_hiS h_bal0 h_enc

/-- **The map ASSEMBLE half, matching-close-pinned — `MapInteriorSeparators''` from a `provider` (R554)**
    — the `''` mirror of `mapInteriorSeparators'_of_enclosing_provider` (`:850`) and the FIRST consumer
    of the gated rebase `mapGrammarFacts_rebase''` (`:722`).  It reduces the corrected carrier — with NO
    further grammar analysis — to a `provider` that, at every gated sub-window `[a,b)`, hands back the
    *enclosing* map body `[loS,hiS) ⊇ [a,b)` re-seated at `a`'s depth
    (`flowBracketBalance tokens loS a = 0`) together with the enclosing window's corrected facts
    `MapGrammarFacts'' tokens loS hiS`.

    **Two new burdens the `''` provider carries over the single-prime one**, both forced by the gated
    rebase's extra hypotheses (R553):

      * a **SIZE conjunct** `hiS ≤ tokens.size` ADDED to the provider's existential.  The rebase'' reads
        the depth-`1` opener fact via `mapBracketOpen_balance_one`, which needs `k+1 < tokens.size`,
        sourced from `k+1 < j < hiS ≤ tokens.size`.  So the located enclosing window must be bounded by
        the array — which it always is at the recursion root (`hi ≤ tokens.size`), and the descent
        locator threads down.  This is the ONE shape-difference from the `'` provider, and it is exactly
        why the single-prime probe held for ALL `tokens` while the `''` probe needs the window inside the
        array (see the de-risk below).
      * the **GATE** `MapTypedInterior tokens a b`, which the rebase'' also requires — but this is FREE:
        it is the carrier's OWN domain hypothesis (`hgate`), already in scope at the assemble site, NOT
        an extra provider burden.  The assembler simply forwards it.

    Discharge is the same single `obtain` + single bundled rebase as the `'` assembler — the rebase'' does
    all the conjunct-5/6 close-relocation work internally.  This is the parametric-assembler-extraction
    move ([[ref-parametric-assembler-extraction]]) on the `''` axis: ASSEMBLE is DONE here; PRODUCE the
    `provider` (now also obliged to bound `hiS` by the array) is the next brick
    (`mapEnclosingFacts''_provider_of_located` + the descent locator).

    INHABITATION-DEBT discipline ([[ref-inhabitation-debt-validate-target-defs]] rule 3 — a hypothesis
    with no producer is the alarm; here the provider hypothesis with its NEW size conjunct):
    `Tests/Reflections/MapCarrierRobustInhabitation.lean`'s
    `mapInteriorSeparators''_of_enclosing_provider_unit` feeds the assembler a concrete IDENTITY provider
    on a unit span `[lo, lo+1)` under the precondition `lo+1 ≤ tokens.size` — which is precisely what
    discharges the new `hiS ≤ tokens.size` conjunct (`hiS = b ≤ lo+1 ≤ tokens.size`) — and recovers the
    inhabited `''` carrier, so the provider shape (size conjunct included) is satisfiable, not a trap.
    The real-data producibility of that size bound is already grounded one level down by the R553 rebase
    probes (`mapGrammarFacts_rebase''_bracketVal`, `13 ≤ 15` off real emission).  The explicit `lo+1 ≤
    tokens.size` precondition — absent from the single-prime probe — is the honest record of the one new
    obligation, NOT hidden behind a vacuous generalization.  Verified-but-unconsumed (its `''`
    provider/dispatcher do not exist yet); references no sorry site; frontier sorry count unchanged at 4. -/
theorem mapInteriorSeparators''_of_enclosing_provider
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (provider : ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → MapTypedInterior tokens a b →
      ∃ loS hiS, loS ≤ a ∧ b ≤ hiS ∧ hiS ≤ tokens.size ∧ flowBracketBalance tokens loS a = 0 ∧
        MapGrammarFacts'' tokens loS hiS) :
    MapInteriorSeparators'' tokens lo hi := by
  intro a b ha hab hb hgate
  obtain ⟨loS, hiS, h_loS_a, h_b_hiS, h_hiS_size, h_bal0, h_enc⟩ := provider a b ha hab hb hgate
  exact mapGrammarFacts_rebase'' tokens loS a b hiS h_loS_a h_b_hiS h_hiS_size h_bal0 hgate h_enc

/-- **The map enclosing-facts `provider`, ASSEMBLED from a LOCATED enclosing map** — the
    [[ref-parametric-assembler-extraction]] split of the R542 provider's locate boundary, the
    boundary-robust map twin of `seqEnclosingFacts_provider_of_located` (`:1121`).  Lift the locator's
    eventual output as hypotheses — a located enclosing map body `[loS, hiS)` with the gated window
    re-seated at its top level (`flowBracketBalance tokens loS a = 0`), enclosing the window
    (`loS ≤ a`, `b ≤ hiS`), and its bundled robust facts `MapGrammarFacts' tokens loS hiS` — and the
    provider's existential is discharged in ONE step: package the witnesses.  No locate analysis here:
    that is isolated as the residual.

    This factors the whole `provider` into ASSEMBLE (here, trivial packaging) vs LOCATE+leaf (the
    residual), and is where the landed LOCATE half plugs in: R538's `mapEnclosingOpener_of_gate`
    (`:749`) supplies the enclosing opener `p` (so `loS = p + 1`) with `flowBracketBalance tokens loS a = 0`,
    and R539's `mapClose_of_located_and_enclosing` (`:886`) supplies the matching close `hiS` with the
    containment bounds `a ≤ hiS` / `b ≤ hiS` — exactly `loS ≤ a` (via `loS = p + 1 ≤ a` from `p < a`),
    `b ≤ hiS`, and the re-seat.  So after this brick the ONLY residual on the balance-`0` branch is the
    LEAF `MapGrammarFacts' loS hiS` from the located complete enclosing map body — the map analog of
    `seqEnclosingFacts_of_windowed_safebodyunit` (`:1082`) — with the LOCATE wiring fully landed.

    Unlike the seq twin (which takes a windowed `SafeBodyUnit` and CONVERTS it to the three facts via
    `seqEnclosingFacts_of_windowed_safebodyunit`), this map version takes the bundled `MapGrammarFacts'`
    directly: the robust carrier needs the SIX bundled facts, and the conversion-from-body-structure is
    precisely the leaf residual, kept out of the assembler.

    Non-vacuity (inhabitation-debt rule 3, [[ref-inhabitation-debt-validate-target-defs]]): the lifted
    `MapGrammarFacts'` hypothesis IS satisfiable — `Tests/Reflections/MapCarrierRobustInhabitation.lean`'s
    `mapInteriorSeparators'_via_provider_of_located_unit` builds the R542 provider on a unit span by
    calling THIS assembler with the identity enclosing window (`loS = a`, `hiS = b`, robust facts via
    `mapGrammarFacts'_degenerate`/`_empty`) and recovers the inhabited carrier through the real
    ASSEMBLE→provider-of-located path.  Verified-but-unconsumed (its consumers — a future
    `mapRoot_mapInteriorSeparators'` root seed and the descent provider — do not exist yet); references
    no sorry site; frontier sorry count unchanged at 4. -/
theorem mapEnclosingFacts'_provider_of_located
    (tokens : Array (Positioned YamlToken)) (a b loS hiS : Nat)
    (h_loS_a : loS ≤ a) (h_b_hiS : b ≤ hiS)
    (h_bal0 : flowBracketBalance tokens loS a = 0)
    (h_facts : MapGrammarFacts' tokens loS hiS) :
    ∃ loS hiS, loS ≤ a ∧ b ≤ hiS ∧ flowBracketBalance tokens loS a = 0 ∧
      MapGrammarFacts' tokens loS hiS :=
  ⟨loS, hiS, h_loS_a, h_b_hiS, h_bal0, h_facts⟩

/-- **The `''` map enclosing-facts `provider`, ASSEMBLED from a LOCATED enclosing map (R555)** — the
    `''` mirror of `mapEnclosingFacts'_provider_of_located` (`:941`) and the SECOND link of the
    matching-close-pinned carrier chain, feeding the R554 ASSEMBLE half
    `mapInteriorSeparators''_of_enclosing_provider` (`:900`).  Lift the locator's eventual output as
    hypotheses — a located enclosing map body `[loS, hiS)` with the gated window re-seated at its top
    level (`flowBracketBalance tokens loS a = 0`), enclosing the window (`loS ≤ a`, `b ≤ hiS`), bounded
    by the array (`hiS ≤ tokens.size`), and its bundled corrected facts `MapGrammarFacts'' tokens loS hiS`
    — and the provider's existential is discharged in ONE step: package the witnesses.  No locate
    analysis here: that is isolated as the residual.

    **The SIZE conjunct is the ONLY shape-difference from the `'` twin**
    ([[ref-additive-field-cost-by-keying]] — an additive carrier field's per-arm cost is arm ROLE ×
    field KEYING).  This is a CONSTRUCTING arm packaging a WINDOW-ABSOLUTE field: the `hiS ≤ tokens.size`
    bound the R554 ASSEMBLE half added to the provider existential (forced by the gated rebase's
    `mapBracketOpen_balance_one` size need) is here lifted verbatim as the new hypothesis `h_hiS_size`
    and forwarded into the tuple unchanged — NO re-establishment, because `hiS` is the located window's
    absolute right edge, not a walking cursor.  Everything else — `loS ≤ a`, `b ≤ hiS`, the re-seat, the
    facts — transports byte-for-byte from the `'` packaging.  So the brick's whole cost is +1 lifted
    hypothesis, +1 existential conjunct: the SIZE burden the chain must now thread, stated at exactly the
    link that packages it (and which the still-owed dispatcher/root-seed must each source — at the root
    from `hi ≤ tokens.size`, down the descent from the locator).

    INHABITATION-DEBT discipline ([[ref-inhabitation-debt-validate-target-defs]] rule 3 — a hypothesis
    with no producer is the alarm; here BOTH the lifted `MapGrammarFacts''` facts AND the NEW size bound):
    `Tests/Reflections/MapCarrierRobustInhabitation.lean`'s
    `mapInteriorSeparators''_via_provider_of_located_unit` builds the R554 provider on a unit span by
    calling THIS assembler with the identity enclosing window (`loS = a`, `hiS = b`, corrected facts via
    `mapGrammarFacts''_degenerate`/`_empty`, size bound from `b ≤ lo+1 ≤ tokens.size` under the explicit
    `lo+1 ≤ tokens.size` precondition) and recovers the inhabited `''` carrier through the real
    ASSEMBLE→provider-of-located path — confirming the lifted facts AND the size bound are JOINTLY
    satisfiable, not a trap.  The explicit precondition is the honest record of the one new obligation
    (absent from the `'` twin's all-`tokens` probe), not a vacuous generalization.  Verified-but-unconsumed
    (its consumers — the `''` dispatcher and root seed — do not exist yet); references no sorry site;
    frontier sorry count unchanged at 4. -/
theorem mapEnclosingFacts''_provider_of_located
    (tokens : Array (Positioned YamlToken)) (a b loS hiS : Nat)
    (h_loS_a : loS ≤ a) (h_b_hiS : b ≤ hiS) (h_hiS_size : hiS ≤ tokens.size)
    (h_bal0 : flowBracketBalance tokens loS a = 0)
    (h_facts : MapGrammarFacts'' tokens loS hiS) :
    ∃ loS hiS, loS ≤ a ∧ b ≤ hiS ∧ hiS ≤ tokens.size ∧ flowBracketBalance tokens loS a = 0 ∧
      MapGrammarFacts'' tokens loS hiS :=
  ⟨loS, hiS, h_loS_a, h_b_hiS, h_hiS_size, h_bal0, h_facts⟩

/-- **The per-window map DISPATCHER** — the boundary-robust map twin of
    `seqInteriorSeparators_of_safebody_and_descent` (`:2343`): the `dite` case-split that reduces ONE
    map window's `MapInteriorSeparators' tokens lo hi` to two suppliers — the window's OWN robust facts
    `MapGrammarFacts' tokens lo hi` and a DESCENT provider `desc` for its strictly-nested gated
    sub-windows.

    The R542 assembler `mapInteriorSeparators'_of_enclosing_provider` (`:433`) demands, at every gated
    sub-window `[a,b)`, an enclosing map body `[loS,hiS) ⊇ [a,b)` re-seated at `a`'s depth.  Those
    windows split on the **top-level discriminator** `flowBracketBalance tokens lo a = 0`:

    * `= 0` — `a` is at `[lo,hi)`'s OWN top level, so its enclosing map IS `[lo,hi)` itself; the
      provider is satisfied by `⟨lo, hi, …⟩` directly from the window's robust facts via R543's
      `mapEnclosingFacts'_provider_of_located` (`:474`) at `loS = lo`, `hiS = hi`.  This is the
      abstract, recursion-window form of the (still-owed) `mapRoot_mapInteriorSeparators'` root seed.
    * `≠ 0` — `a` is nested strictly deeper; the enclosing map is an inner bracket the recursion must
      locate, supplied by the `desc` hypothesis (the map twin of the seq driver's
      `seqDescent_provider_of_located`, the backward enclosing-opener locator consuming the
      width-recursion IH).

    **Two structural simplifications over the seq twin.**  Where seq passes a windowed `SafeBodyUnit`
    substrate `h_safe` and CONVERTS it to its three facts inside the located provider, the map located
    provider R543 takes the bundled `MapGrammarFacts'` *directly* — so (a) `h_facts` is the window's
    robust facts, not a substrate, and (b) the seq twin's `h_hi : hi ≤ tokens.size` hypothesis is GONE
    (the facts-direct provider needs no size bound).  The substrate→facts conversion is precisely the
    deferred leaf (`mapEnclosingFacts'_of_windowed_X`), kept out of the dispatcher.

    The split is exhaustive and decidable (`Int` equality on the balance), so the dispatch is a pure
    `dite` — the INVERSE of the classify unifier ([[ref-fold-consumer-chain-to-producer-contract]] at
    the dispatch layer): it folds the per-window provider into the two typed residuals the driver must
    source — the window's own robust facts (the leaf / `mapRoot_mapGrammarFacts'` at the root) and the
    `desc` locator — leaving only the strong-width fixpoint that threads them across the window edges.

    Non-vacuity (inhabitation-debt rule 3, [[ref-inhabitation-debt-validate-target-defs]]): the NEW
    `desc` hypothesis shape IS satisfiable and the dispatcher is non-vacuous —
    `Tests/Reflections/MapCarrierRobustInhabitation.lean`'s `mapInteriorSeparators'_via_dispatcher_unit`
    feeds it `h_facts := mapGrammarFacts'_degenerate` and a concrete identity `desc` on a unit span
    `[lo, lo+1)`, exercises BOTH branches of the `dite` (the `= 0` branch via `h_facts`, the `≠ 0`
    branch via `desc`), and recovers the inhabited carrier through the real dispatch path.

    Verified-but-unconsumed: its consumer `mapRoot_mapInteriorSeparators'` (the root seed) and the
    `desc` producer (the map descent locator) do not exist yet; references no sorry site; frontier
    sorry count unchanged at 4. -/
theorem mapInteriorSeparators'_of_safebody_and_descent
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_facts : MapGrammarFacts' tokens lo hi)
    (desc : ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → flowBracketBalance tokens lo a ≠ 0 →
      MapTypedInterior tokens a b →
      ∃ loS hiS, loS ≤ a ∧ b ≤ hiS ∧ flowBracketBalance tokens loS a = 0 ∧
        MapGrammarFacts' tokens loS hiS) :
    MapInteriorSeparators' tokens lo hi :=
  mapInteriorSeparators'_of_enclosing_provider tokens lo hi (fun a b ha hab hb hgate =>
    if h : flowBracketBalance tokens lo a = 0 then
      mapEnclosingFacts'_provider_of_located tokens a b lo hi ha hb h h_facts
    else
      desc a b ha hab hb h hgate)

/-- **Strict → robust map-facts weakening (R545)** — the first sub-brick of the still-deferred leaf
    `mapEnclosingFacts'_of_windowed_X`.  Every window where the STRICT `MapGrammarFacts` holds (a
    GENUINE complete map body, where each marker's content is truly interior) also satisfies the
    boundary-ROBUST `MapGrammarFacts'`: the robust form only ever *adds* a window-close escape disjunct
    `b ≤ <position>` to each fragile conjunct, so a strict witness lands in the strict-interior arm
    (`Or.inr`) of conjuncts 1/2/3/4/5, and conjunct 6 is verbatim-identical (already robust, reused as
    `e6`).  The plan is: the windowed-map separator lemmas (the leaf proper) produce STRICT facts at a
    complete body — where strict is genuinely TRUE — and this connector weakens them to robust just
    before handing them to the R543 `mapEnclosingFacts'_provider_of_located` assembler.

    INHABITATION-DEBT discipline ([[ref-inhabitation-debt-validate-target-defs]], rule 2): this
    connector was DEFERRED at R543 because its INPUT type `MapGrammarFacts` is boundary-FRAGILE — R540
    refuted it at the window-close cut, and a connector whose domain is only ever empty is a vacuous
    function.  It lands now, paired (in `Tests/Reflections/MapCarrierRobustInhabitation.lean`) with the
    FIRST non-degenerate `MapGrammarFacts` witness — a concrete `{a:1}` complete-window body where
    conjuncts 1–4 genuinely FIRE — so the connector is probed on a real inhabitant of its domain
    (`Or.inr`, not the empty-domain trap), and the produced robust fact is read back through the
    strict-interior arm (the escape disjunct refuted), confirming non-vacuity.  Pure ∧/∨ plumbing;
    axiom-clean.  Verified-but-unconsumed until the windowed-map separator lemmas feed it; frontier
    sorry count unchanged at 4. -/
theorem mapGrammarFacts'_of_mapGrammarFacts (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h : MapGrammarFacts tokens a b) : MapGrammarFacts' tokens a b := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, e6⟩
  · intro k hak hkb hbal htok
    exact Or.inr (e1 k hak hkb hbal htok)
  · intro k hak hkb hbal htok hsc
    exact Or.inr (e2 k hak hkb hbal htok hsc)
  · intro k hak hkb hbal htok
    exact Or.inr (e3 k hak hkb hbal htok)
  · intro k hak hkb hbal htok hsc
    exact Or.inr (e4 k hak hkb hbal htok hsc)
  · intro k j hak hkb hbal htok hkj hjb hdelta hbalj
    exact Or.inr (e5 k j hak hkb hbal htok hkj hjb hdelta hbalj)

/-- **Robust → strict map-facts STRENGTHENING at a complete body (R546)** — the genuine INVERSE of the
    R545 connector `mapGrammarFacts'_of_mapGrammarFacts` (`:559`), and the `b = hi` bridge the R513 block
    named (`:235`).  Where strict → robust is FREE (the robust form only *adds* an escape disjunct, so
    every strict witness weakens unconditionally), the converse robust → strict is BOUNDARY-FRAGILE: it
    holds only where each fragile conjunct's window-close escape `b ≤ <position>` can be REFUTED — i.e. on
    a GENUINE complete map body, where no marker hugs the close.  Those refutations are the genuine leaf,
    lifted here as the five `hk1`/`hk2`/`hv1`/`hv2`/`hk5` hypotheses
    ([[ref-parametric-assembler-extraction]]): each asserts that a marker's required successor lands
    STRICTLY inside the window (the "no `.key`/`.value` marker immediately precedes the close" emission
    fact).  Given them, the bridge is pure: each robust conjunct's INTERIOR arm IS the strict conclusion
    verbatim (read off `MapGrammarFacts'` `:256` vs `MapGrammarFacts` `:166`), so the proof `rcases`-es
    each escape-vs-interior disjunct, refutes the escape via its lifted bound (`absurd … (by omega)`,
    axiom-clean per [[ref-omega-nonarith-goal-pulls-classical]] — `omega` proves only the arithmetic
    negation, `False.elim` fills the strict goal), and returns the interior arm.  Conjunct 6 is already
    robust `=` strict and needs no refuter.

    On the CRITICAL PATH: the existing strict-facts consumer (`mapProducers_of_mapRoot` `:734`, feeding
    `flowSubrangesOk_of_window_producers`) queries genuine-close producer windows where the strict facts
    hold; the R542–R545 chain produces the boundary-ROBUST carrier (the strict carrier being
    uninhabitable, R540); this bridge re-strengthens robust facts to strict precisely at those genuine
    closes, leaving the close-structure refuters as the named residual (the emission leaf still owed).

    INHABITATION-DEBT discipline ([[ref-inhabitation-debt-validate-target-defs]]):
    `Tests/Reflections/MapCarrierRobustInhabitation.lean`'s `mapGrammarFacts_strict_roundtrip` PROBES this
    non-vacuously by a full strict → robust → strict ROUND-TRIP on the `{a:1}` complete body `[1,5)`: it
    feeds the R545 connector's robust output back through this bridge, supplying the five refuters proved
    INDEPENDENTLY off the concrete fixture (rule 3 — the lifted hypotheses have a real producer at the
    genuine close, not a trap), and recovers the strict witness `mapGrammarFacts_complete_window`.
    Verified-but-unconsumed until the windowed-map separator leaf produces the refuters off emission;
    frontier sorry count unchanged at 4; pure ∧/∨ plumbing, axiom-clean. -/
theorem mapGrammarFacts_of_mapGrammarFacts' (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h_rob : MapGrammarFacts' tokens a b)
    (hk1 : ∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .key →
      k + 1 < b)
    (hk2 : ∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .key →
      (∃ c s, tokens[k + 1]!.val = .scalar c s) → k + 2 < b)
    (hv1 : ∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .value →
      k + 1 < b)
    (hv2 : ∀ k, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .value →
      (∃ c s, tokens[k + 1]!.val = .scalar c s) → k + 2 ≤ b)
    (hk5 : ∀ k j, a ≤ k → k < b → flowBracketBalance tokens a k = 0 → tokens[k]!.val = .key →
      k + 1 < j → j < b → flowBracketDelta tokens[j]!.val = -1 →
      flowBracketBalance tokens a (j + 1) = 0 → j + 1 < b) :
    MapGrammarFacts tokens a b := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h_rob
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hak hkb hbalk htok
    rcases c1 k hak hkb hbalk htok with hesc | hint
    · exact absurd (hk1 k hak hkb hbalk htok) (by omega)
    · exact hint
  · intro k hak hkb hbalk htok hsc
    rcases c2 k hak hkb hbalk htok hsc with hesc | hint
    · exact absurd (hk2 k hak hkb hbalk htok hsc) (by omega)
    · exact hint
  · intro k hak hkb hbalk htok
    rcases c3 k hak hkb hbalk htok with hesc | hint
    · exact absurd (hv1 k hak hkb hbalk htok) (by omega)
    · exact hint
  · intro k hak hkb hbalk htok hsc
    rcases c4 k hak hkb hbalk htok hsc with hesc | hint
    · exact absurd (hv2 k hak hkb hbalk htok hsc) (by omega)
    · exact hint
  · intro k j hak hkb hbalk htok hkj hjb hdelta hbalj
    rcases c5 k j hak hkb hbalk htok hkj hjb hdelta hbalj with hesc | hint
    · exact absurd (hk5 k j hak hkb hbalk htok hkj hjb hdelta hbalj) (by omega)
    · exact hint
  · intro k j hak hkb hbalk htok hkj hjb hdelta hbalj
    exact c6 k j hak hkb hbalk htok hkj hjb hdelta hbalj

/-! ### The map gate, reconstructed in place from the window opener (R514)

The map carrier `MapInteriorSeparators tokens lo hi` (`:187`) carries the gate `MapTypedInterior` as a
PREMISE.  Its eventual consumer — `mapGrammarFacts_of_mapRoot`, the map twin of the seq projection —
will instantiate the carrier at `a := lo, b := hi` and must therefore SUPPLY that gate.  The gate's
`btFold`-top conjunct (`(btFold (some []) (tokens.toList.take a)).bind (·.head?) = some false`) is a
fact about the PREFIX `[0,a)`, not the window interior, so it is not a projection of any interior
predicate — it must be RECONSTRUCTED at the window from its boundary opener
([[ref-reconstruct-in-place-over-relocate]] / [[ref-prefix-gate-reconstructed-from-boundary]]).

These two lemmas are the `some false`/`.flowMappingStart` DUAL of the seq pair
`enclosingMark_true_of_opener` (`:1310`) / `seqTypedInterior_of_opener` (`:1335`).  They are the
genuine "real work" the R513 brick named for `mapGrammarFacts_of_mapRoot`.  The mirror sheds NO
machinery — it is a pure two-symbol text-swap (`.flowSequenceStart → .flowMappingStart`,
`some true → some false`) resting on the single `btStep` fact that a `{` pushes `false` where a `[`
pushes `true` (`WellBracketed.lean:1540-1541`).  Verified-but-unconsumed (R514): the consumer
`mapGrammarFacts_of_mapRoot` does not exist yet; references no sorry site, frontier sorry count
unchanged at 4; axioms `[propext, Quot.sound]`, byte-identical to the seq pair. -/

/-- MAP mirror of `enclosingMark_true_of_opener` (`:1310`): a `.flowMappingStart` opener at `q` pushes
    `false` onto the typed bracket stack (`btStep`, `WellBracketed.lean:1541`), so the stack top after
    the opener prefix `[0, q+1)` is `some false` — the gate's enclosing-`{` conjunct, reconstructed
    from the boundary. -/
theorem enclosingMark_false_of_opener
    (tokens : Array (Positioned YamlToken)) (q : Nat) (h_q : q < tokens.size)
    (s : List Bool) (h_pre : btFold (some []) (tokens.toList.take q) = some s)
    (h_open : tokens[q]!.val = .flowMappingStart) :
    (btFold (some []) (tokens.toList.take (q + 1))).bind (·.head?) = some false := by
  have h_q' : q < tokens.toList.length := by rwa [Array.length_toList]
  have h_split : tokens.toList.take (q + 1)
      = tokens.toList.take q ++ [tokens.toList[q]'h_q'] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h_q']; rfl
  have h_val : (tokens.toList[q]'h_q').val = .flowMappingStart := by
    have hb : tokens.toList[q]'h_q' = tokens[q]! := by
      rw [Array.getElem_toList, getElem!_pos tokens q h_q]
    rw [hb]; exact h_open
  have hstep : btStep (tokens.toList[q]'h_q') s = some (false :: s) := by
    simp only [btStep, h_val]
  have hfold : btFold (some s) [tokens.toList[q]'h_q'] = btStep (tokens.toList[q]'h_q') s := rfl
  rw [h_split, btFold_append, h_pre, hfold, hstep]; rfl

/-- **The full map-typed gate, discharged from the window opener** — the consume-site corollary
    `mapGrammarFacts_of_mapRoot` will feed `MapInteriorSeparators`.  The `some false` mirror of
    `seqTypedInterior_of_opener` (`:1335`): given the opener at `q` is a `.flowMappingStart`, the
    pre-opener prefix folds to `some s`, the body `[q+1, hi)` is depth-`0`-balanced and locally floored,
    the gate `MapTypedInterior tokens (q+1) hi` holds — so the carrier's body is extractable at this
    window with no second guard. -/
theorem mapTypedInterior_of_opener
    (tokens : Array (Positioned YamlToken)) (q hi : Nat) (h_q : q < tokens.size)
    (s : List Bool) (h_pre : btFold (some []) (tokens.toList.take q) = some s)
    (h_open : tokens[q]!.val = .flowMappingStart)
    (h_bal : flowBracketBalance tokens (q + 1) hi = 0)
    (h_floor : ∀ i, q + 1 ≤ i → i ≤ hi → flowBracketBalance tokens (q + 1) i ≥ 0) :
    MapTypedInterior tokens (q + 1) hi :=
  ⟨h_bal, enclosingMark_false_of_opener tokens q h_q s h_pre h_open, h_floor⟩

/-! ### The map root projection — carrier ⊕ gate bridge ⇒ the six grammar facts (R515)

`mapGrammarFacts_of_mapRoot` is the map twin of the seq root projection (the
`seqInteriorSeparators_of_safebody_provider` / `seqSeparatorFacts_of_recseqbody` direction): it CLOSES
the carrier→facts step for the map axis.  Given the root carrier `MapInteriorSeparators tokens lo' hi'`
(R513) it instantiates at one map window `[q+1, hi) ⊆ [lo', hi')` whose opener is the `.flowMappingStart`
at `q`, discharges the gate `MapTypedInterior tokens (q+1) hi` through R514's `mapTypedInterior_of_opener`,
and projects out `MapGrammarFacts tokens (q+1) hi` — exactly the six adjacency facts the final consumer
`flowSubrangesOk_of_window_producers` (`NonemptyStructure.lean:10434+`) wants as `h_key_content` …
`h_value_bracket_succ`, re-keyed `lo→q+1`.

Per [[ref-fold-consumer-chain-to-producer-contract]] / [[ref-guarded-universal-fold-relocates-guard]] the
TWO inputs the gate bridge still needs beyond the consumer's own premises — the pre-opener prefix witness
`btFold (some []) (take q) = some s` and the body FLOOR `∀ i, q+1 ≤ i → i ≤ hi → flowBracketBalance .. ≥ 0`
— are folded as HYPOTHESES, naming the producer's remaining contract precisely.  At the consume site they
come from, respectively, `WellTyped_prefix_some` (`WellBracketed.lean:1790`, the same source the seq path
uses) and a `flowBracketBalance_interior_dyck` re-base (`WellBracketed.lean:2118/2142`, exactly the floor
`flowBracketBalance_matching_close_map` already extracts at a located map interior).  The opener premise
`tokens[q]!.val = .flowMappingStart` and the body balance are the consumer's OWN premises (its
`tokens[lo-1]!.val = .flowMappingStart` with `lo = q+1`).

Verified-but-unconsumed (R515): its consumer — a future `flowSubrangesOk_of_seqRoot_and_mapRoot`
reconciliation (the map twin of R512) — does not exist yet; references no sorry site; frontier sorry count
unchanged at 4; axioms `[propext, Quot.sound]`, inherited verbatim through the R514 gate bridge. -/

/-- **The map root projection**: from the root carrier `MapInteriorSeparators tokens lo' hi'` and the
    window opener at `q` (`.flowMappingStart`), the six `MapGrammarFacts tokens (q+1) hi` at the map body
    window `[q+1, hi)`.  A one-step composition: the gate bridge `mapTypedInterior_of_opener` (R514)
    supplies the carrier's `MapTypedInterior` premise; the carrier delivers the facts.  The prefix witness
    `h_pre` and body floor `h_floor` are the producer's remaining contract (folded as hypotheses). -/
theorem mapGrammarFacts_of_mapRoot
    (tokens : Array (Positioned YamlToken)) (lo' hi' q hi : Nat)
    (h_carrier : MapInteriorSeparators tokens lo' hi')
    (h_q : q < tokens.size)
    (h_lo' : lo' ≤ q + 1) (h_qhi : q + 1 ≤ hi) (h_hi' : hi ≤ hi')
    (s : List Bool) (h_pre : btFold (some []) (tokens.toList.take q) = some s)
    (h_open : tokens[q]!.val = .flowMappingStart)
    (h_bal : flowBracketBalance tokens (q + 1) hi = 0)
    (h_floor : ∀ i, q + 1 ≤ i → i ≤ hi → flowBracketBalance tokens (q + 1) i ≥ 0) :
    MapGrammarFacts tokens (q + 1) hi :=
  h_carrier (q + 1) hi h_lo' h_qhi h_hi'
    (mapTypedInterior_of_opener tokens q hi h_q s h_pre h_open h_bal h_floor)

/-! ### The carrier → six grammar producers collapse (R520, brick (3) core)

`flowSubrangesOk_of_window_producers` (`NonemptyStructure.lean:10434+`) demands the six MAP grammar
producers as `h_key_content` … `h_value_bracket_succ`, each a per-window universal `∀ lo hi, <8 guards>
→ <inner body>`.  R519 (`mapGrammarFacts_false_window`) showed the original SEVEN-guard slots are FALSE
on a cross-matched window, so the Dyck-gated map root carrier `MapInteriorSeparators` cannot fire on
them; the redirect was to add the interior Dyck floor `∀ i ∈ [lo,hi], balance lo i ≥ 0` as the EIGHTH
guard to those six slots (now landed — they match `h_seq_rec`/`h_map_rec`).  These two lemmas are the
map twin of the seq carrier→producer collapse `seqHRec_of_root_and_emit` does for `h_seq_rec`: they
turn the single carrier (plus whole-stream fold-totality) into all six producers.

`mapGrammarFacts_window_of_root` is the per-window step.  It re-keys R515's `mapGrammarFacts_of_mapRoot`
from the opener position `q` to the producer's window start `lo` (`q := lo - 1`, so `q + 1 = lo` via
`Nat.sub_add_cancel` since `2 ≤ lo`), supplies the pre-opener prefix witness from `h_fold_total`, and
projects `MapGrammarFacts tokens lo hi`.  It uses the producer's `h_open`/`h_bal`/`h_floor` directly and
DISCARDS the `.flowMappingEnd` closer guard — the marker-free carrier identifies the interior by its
`some false` enclosure, not the closer (the R513 finding).  Crucially the producer slot's NON-strict
`lo ≤ hi` is honoured (the empty nested `{}` window `lo = hi` makes the six universals vacuous, and the
R515 route needs only `q + 1 ≤ hi`, no `lo < hi` — unlike the `FlowBodyWindow`-keyed
`mapWindow_grammarFacts` route which would demand strict).

`mapProducers_of_mapRoot` bundles the six producers by projecting the matching `MapGrammarFacts`
conjunct (`.1` … `.2.2.2.2.2`) at every guarded window.  This is exactly the carrier mirror of R512's
seq asymmetry: feeding these six into `flowSubrangesOk_of_window_producers` collapses six of the seven
map slots onto the root carrier, leaving only `h_map_rec` (the `RecMapBody` recursion, brick (2)) raw.

Verified-but-unconsumed (R225): the consumer — a future `flowSubrangesOk_of_seqRoot_and_mapRoot`
reconciliation (R512's map twin) — does not exist yet; references no sorry site; frontier sorry count
unchanged at 4.  Axioms inherit through R515's `mapGrammarFacts_of_mapRoot` (`[propext, Quot.sound]`):
the carrier is taken as a hypothesis, so no `sorryAx` enters here ([[ref-mirror-inherits-dependency-axioms]]
R518 — taint tracks the dependency, and an ASSUMED carrier is clean). -/

/-- **The per-window carrier→facts projection at a producer window** (R520).  From the map root carrier
    and whole-stream fold-totality, the six `MapGrammarFacts tokens lo hi` at a producer window `[lo,hi)`,
    given the producer's own structural guards (opener `tokens[lo-1] = .flowMappingStart`, body balance,
    interior Dyck floor) and `2 ≤ lo`.  A re-key of `mapGrammarFacts_of_mapRoot` (R515) from `q` to
    `q + 1 = lo`; the closer guard is not needed. -/
theorem mapGrammarFacts_window_of_root
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_carrier : MapInteriorSeparators tokens 2 (tokens.size - 2))
    (h_fold_total : ∀ m, ∃ s, btFold (some []) (tokens.toList.take m) = some s)
    (h_lo2 : 2 ≤ lo) (h_lo_hi : lo ≤ hi)
    (h_hi2 : hi ≤ tokens.size - 2) (h_hi_sz : hi < tokens.size)
    (h_open : tokens[lo - 1]!.val = .flowMappingStart)
    (h_bal : flowBracketBalance tokens lo hi = 0)
    (h_floor : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) :
    MapGrammarFacts tokens lo hi := by
  obtain ⟨s, h_pre⟩ := h_fold_total (lo - 1)
  have h_lo_eq : lo - 1 + 1 = lo := Nat.sub_add_cancel (by omega)
  have h := mapGrammarFacts_of_mapRoot tokens 2 (tokens.size - 2) (lo - 1) hi
    h_carrier (by omega) (by omega) (by omega) h_hi2 s h_pre h_open
    (by rw [h_lo_eq]; exact h_bal)
    (by rw [h_lo_eq]; exact h_floor)
  rwa [h_lo_eq] at h

/-- **The six MAP grammar producers, collapsed onto the root carrier** (R520, brick (3) core).  Given
    the map root carrier `MapInteriorSeparators tokens 2 (size-2)` and whole-stream fold-totality,
    delivers all six floor-bearing per-window producers `flowSubrangesOk_of_window_producers` demands —
    the map mirror of `seqHRec_of_root_and_emit`'s `h_seq_rec`.  Each producer projects the matching
    `MapGrammarFacts` conjunct of `mapGrammarFacts_window_of_root`; the `.flowMappingEnd` closer guard is
    discarded at every slot. -/
theorem mapProducers_of_mapRoot
    (tokens : Array (Positioned YamlToken))
    (h_carrier : MapInteriorSeparators tokens 2 (tokens.size - 2))
    (h_fold_total : ∀ m, ∃ s, btFold (some []) (tokens.toList.take m) = some s) :
    (∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .key →
        k + 1 < hi ∧ isFlowContentStart tokens[k + 1]!.val) ∧
    (∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .key →
        (∃ c s, tokens[k + 1]!.val = .scalar c s) →
        k + 2 < hi ∧ tokens[k + 2]!.val = .value) ∧
    (∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .value →
        k + 1 < hi ∧ isFlowContentStart tokens[k + 1]!.val) ∧
    (∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .value →
        (∃ c s, tokens[k + 1]!.val = .scalar c s) →
        k + 2 ≤ hi ∧
        (tokens[k + 2]!.val = .flowEntry ∨
         (tokens[k + 2]!.val = .flowMappingEnd ∧ k + 2 = hi))) ∧
    (∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      ∀ k j, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .key →
        k + 1 < j → j < hi →
        flowBracketDelta tokens[j]!.val = -1 →
        flowBracketBalance tokens lo (j + 1) = 0 →
        j + 1 < hi ∧ tokens[j + 1]!.val = .value) ∧
    (∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      ∀ k j, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .value →
        k + 1 < j → j < hi →
        flowBracketDelta tokens[j]!.val = -1 →
        flowBracketBalance tokens lo (j + 1) = 0 →
        j + 1 ≤ hi ∧
        (tokens[j + 1]!.val = .flowEntry ∨
         (tokens[j + 1]!.val = .flowMappingEnd ∧ j + 1 = hi))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro lo hi h_lo2 h_lo_hi h_hi2 h_hi_sz _h_close h_bal h_open h_floor
  · exact (mapGrammarFacts_window_of_root tokens lo hi h_carrier h_fold_total
      h_lo2 h_lo_hi h_hi2 h_hi_sz h_open h_bal h_floor).1
  · exact (mapGrammarFacts_window_of_root tokens lo hi h_carrier h_fold_total
      h_lo2 h_lo_hi h_hi2 h_hi_sz h_open h_bal h_floor).2.1
  · exact (mapGrammarFacts_window_of_root tokens lo hi h_carrier h_fold_total
      h_lo2 h_lo_hi h_hi2 h_hi_sz h_open h_bal h_floor).2.2.1
  · exact (mapGrammarFacts_window_of_root tokens lo hi h_carrier h_fold_total
      h_lo2 h_lo_hi h_hi2 h_hi_sz h_open h_bal h_floor).2.2.2.1
  · exact (mapGrammarFacts_window_of_root tokens lo hi h_carrier h_fold_total
      h_lo2 h_lo_hi h_hi2 h_hi_sz h_open h_bal h_floor).2.2.2.2.1
  · exact (mapGrammarFacts_window_of_root tokens lo hi h_carrier h_fold_total
      h_lo2 h_lo_hi h_hi2 h_hi_sz h_open h_bal h_floor).2.2.2.2.2

/-! ### The map descent LOCATE half — the `some false`/`{` dual of the seq locate (R538)

The seq root-carrier descent provider's LOCATE half is fully landed (`flowBracketBalance_pos_of_seqTypedInterior`
`:697`, `seqEnclosingOpener_of_gate` `:726`, `seqOpenerType_of_located_and_gate` `:754`).  The map root
carrier has the FOUNDATION (gate `MapTypedInterior`, `MapGrammarFacts`, the carrier, its edges, and the
carrier→facts projection `mapGrammarFacts_of_mapRoot` R515) but NO descent chain at all — its `desc`
provider is the still-open mirror the frontier-status names as the genuine open math alongside the seq
`desc`.  This block lands the map descent's LOCATE half, the recursion-FREE entry point any future
`mapDescent_provider_of_located` / `mapDescent_provider_of_gate` consumes wholesale.

The three bricks are the FAITHFUL `some true → some false` / `.flowSequenceStart → .flowMappingStart` dual
of the seq trio, exactly as the seq docstrings PROMISED ("Type-agnostic core: the map mirror reads the
gate's `= some false` top, gets `balance 0 a ≥ 1` from the same `flowBracketBalance_pos_of_btFold_head`,
and calls the identical backward locator"; "the map mirror reads the gate's `= some false` and concludes
`.flowMappingStart` by the identical argument with `b = false`").  The mirror sheds NO machinery — the
backward scan `flowBracketBalance_backward_open_locate` is BRACKET-TYPE-AGNOSTIC (it reads only the
balance), and `flowBracketBalance_pos_of_btFold_head` is already GENERIC in the head bit `hd : Bool`, so
bricks (1)/(2) are a one-symbol swap (`true → false`).  Brick (3) is the only one with proof content
beyond a swap, and even there the cost is exactly the [[ref-mirror-reads-conjunct-not-projection]]
two-symbol delta plus a single BRANCH-VACUITY FLIP: the `flowBracketDelta = 1` dispatch's seq-opener and
map-opener cases swap which one discharges the typed-conclusion implication and which one is killed as
absurd ([[ref-converse-forward-invariant-asymmetry]] read as opener-bit exclusivity) — the located
opener's pushed bit `b` is forced `= false` by the gate's `some false` head, pinning `tokens[p]` to a `{`.

Verified-but-unconsumed (R538): its consumer — `mapDescent_provider_of_located` / `mapDescent_provider_of_gate`
/ `mapRoot_mapInteriorSeparators` — does not exist yet; references no sorry site; frontier sorry count
unchanged at 4.  Axioms are byte-identical to the seq twins (verified): brick (1)
`flowBracketBalance_pos_of_mapTypedInterior` `[propext, Quot.sound]`; bricks (2)/(3) `mapEnclosingOpener_of_gate`
/ `mapOpenerType_of_located_and_gate` `[propext, Classical.choice, Quot.sound]` (the backward locator and
the frame-inverse thread `Classical.choice`) — [[ref-mirror-inherits-dependency-axioms]]. -/

/-- **The gate makes the map backward locator INVOKABLE** — the `some false` dual of
    `flowBracketBalance_pos_of_seqTypedInterior` (`:697`).  At any gated window `[a,b)` the gate
    `MapTypedInterior tokens a b` carries a `btFold`-top `= some false` after the prefix `[0,a)` (its
    second conjunct: the enclosing bracket is a MAPPING).  A non-empty typed stack forces
    `flowBracketBalance tokens 0 a ≥ 1` (`flowBracketBalance_pos_of_btFold_head`, GENERIC in the head bit
    — here instantiated at `false`) — exactly the hypothesis of `flowBracketBalance_backward_open_locate`.
    So the same pure-balance backward enclosing-opener locator the seq path uses is invokable at every
    nested gated map window. -/
theorem flowBracketBalance_pos_of_mapTypedInterior
    (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h : MapTypedInterior tokens a b) :
    flowBracketBalance tokens 0 a ≥ 1 :=
  flowBracketBalance_pos_of_btFold_head tokens a false h.2.1

/-- **The map gate LOCATES the enclosing opener with the exact facts the descent assembler reads** — the
    `some false` dual of `seqEnclosingOpener_of_gate` (`:726`), the LOCATE half of the map `desc` descent
    driver ([[ref-from-located-assembler-direction]]: the LOCATE; a future `mapDescent_provider_of_located`
    is the assemble).

    At any nested gated map window `[a, b)` the gate `MapTypedInterior tokens a b` carries
    `flowBracketBalance tokens 0 a ≥ 1` (`flowBracketBalance_pos_of_mapTypedInterior` — its `btFold`-top
    `= some false` forces a non-empty typed stack), exactly the hypothesis that makes the pure-balance
    backward scan `flowBracketBalance_backward_open_locate` invokable.  That scan returns the innermost
    unmatched opener `p < a` together with the THREE locator facts — `flowBracketDelta tokens[p]! = 1`,
    `flowBracketBalance tokens (p+1) a = 0`, and the interior floor `∀ i ∈ [p+1, a], balance (p+1) i ≥ 0`.
    Those four outputs are *definitionally* the four opener hypotheses a `mapDescent_provider_of_located`
    will consume — the descent's LOCATE half needs **no fresh backward fixpoint**, the backward scan runs
    its own `Nat.strongRecOn` internally ([[ref-backward-locator-mirrors-forward]]).  The backward scan is
    BRACKET-TYPE-AGNOSTIC, so this is term-for-term the seq locator with the `some false` positivity
    source swapped in. -/
theorem mapEnclosingOpener_of_gate
    (tokens : Array (Positioned YamlToken)) (a b : Nat) (h_a_sz : a ≤ tokens.size)
    (h_gate : MapTypedInterior tokens a b) :
    ∃ p, p < a ∧ flowBracketDelta tokens[p]!.val = 1 ∧
      flowBracketBalance tokens (p + 1) a = 0 ∧
      (∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) :=
  flowBracketBalance_backward_open_locate tokens a h_a_sz
    (flowBracketBalance_pos_of_mapTypedInterior tokens a b h_gate)

/-- **The located map opener is a `{`** — the `some false` dual of `seqOpenerType_of_located_and_gate`
    (`:754`).  Given the backward locator's full output at the gated window start `a` — an opener `p` with
    `flowBracketDelta tokens[p]! = 1` (so `tokens[p]` is `[` or `{`), the body balance
    `flowBracketBalance tokens (p+1) a = 0`, and the interior floor over `(p, a]` — PLUS the gate's
    `btFold`-top `= some false` after the prefix `[0,a)`, the located opener `tokens[p]` is a
    `.flowMappingStart`.

    The proof is the seq argument with `b = false`: the typed stack after `[0,p+1)` is `b :: s_p` where
    `b` is the bit `tokens[p]` pushes (`b = true ↔ seqStart`, `b = false ↔ mapStart`).  The interior body
    `(take a).drop (p+1)` has relative balance `0` and floor `≥ 0`, so it NEVER pops `b` and returns the
    stack to `b :: s_p` at `a` (`btFold_frame_inv`).  Its head is `b`, which the gate fixes to `false`,
    forcing `tokens[p]` to be the map opener.  The `flowBracketDelta = 1` dispatch's two cases SWAP roles
    versus the seq proof: the map-opener case now discharges the conclusion (`b = false → mapStart`) and
    the seq-opener case is killed as absurd (`true = false`) — opener-bit exclusivity
    ([[ref-converse-forward-invariant-asymmetry]]).  Every other line is byte-identical to the seq twin. -/
theorem mapOpenerType_of_located_and_gate
    (tokens : Array (Positioned YamlToken)) (a p : Nat)
    (h_pa : p < a) (h_a_sz : a ≤ tokens.size)
    (h_delta : flowBracketDelta tokens[p]!.val = 1)
    (h_bal : flowBracketBalance tokens (p + 1) a = 0)
    (h_floor : ∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0)
    (h_mark : (btFold (some []) (tokens.toList.take a)).bind (·.head?) = some false) :
    tokens[p]!.val = .flowMappingStart := by
  have h_p_sz : p < tokens.size := by omega
  have h_p_T : p < tokens.toList.length := by rw [Array.length_toList]; exact h_p_sz
  -- (1) the gate forces the whole `take a` fold to `some S` with head `false`.
  obtain ⟨S, hS⟩ : ∃ S, btFold (some []) (tokens.toList.take a) = some S := by
    cases hc : btFold (some []) (tokens.toList.take a) with
    | none => rw [hc] at h_mark; simp at h_mark
    | some S => exact ⟨S, rfl⟩
  rw [hS] at h_mark
  -- (2) `take a = take (p+1) ++ interior`, interior the body slice.
  obtain ⟨interior, hint⟩ :
      ∃ I, I = (tokens.toList.drop (p + 1)).take (a - (p + 1)) := ⟨_, rfl⟩
  have h_split : tokens.toList.take a = tokens.toList.take (p + 1) ++ interior := by
    rw [hint, ← List.take_add]; congr 1; omega
  -- (3) the prefix `take p` folds to `some s_p`.
  have h_split_p : tokens.toList.take (p + 1)
      = tokens.toList.take p ++ [tokens.toList[p]'h_p_T] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h_p_T]; rfl
  obtain ⟨s_p, hsp⟩ : ∃ s_p, btFold (some []) (tokens.toList.take p) = some s_p :=
    btFold_some_prefix (tokens.toList.take p) ([tokens.toList[p]'h_p_T] ++ interior) S (by
      rw [← List.append_assoc, ← h_split_p, ← h_split]; exact hS)
  -- (4) the stack just after the opener is `b :: s_p`.
  have hTp : tokens.toList[p]'h_p_T = tokens[p]! := by
    rw [Array.getElem_toList, getElem!_pos tokens p h_p_sz]
  have h_after : btFold (some []) (tokens.toList.take (p + 1)) = btStep tokens[p]! s_p := by
    rw [h_split_p, btFold_append, hsp]
    have : btFold (some s_p) [tokens.toList[p]'h_p_T] = btStep (tokens.toList[p]'h_p_T) s_p := rfl
    rw [this, hTp]
  -- (5) the opener is a `[` or `{` (delta = 1); get the pushed bit `b`.  The map case discharges the
  --     conclusion; the seq case is absurd (the gate head is `false`, so `b` will be forced `false`).
  obtain ⟨b, hbpush, hb_map⟩ :
      ∃ b, btStep tokens[p]! s_p = some (b :: s_p) ∧
        (b = false → tokens[p]!.val = .flowMappingStart) := by
    rcases (flowBracketDelta_eq_one_iff _).mp h_delta with hseq | hmap
    · exact ⟨true, by simp [btStep, hseq], fun h => absurd h (by decide)⟩
    · exact ⟨false, by simp [btStep, hmap], fun _ => hmap⟩
  -- (6) the whole `take a` fold equals the interior fold from `b :: s_p`.
  have hfold : btFold (some (b :: s_p)) interior = some S := by
    have h1 : btFold (some []) (tokens.toList.take (p + 1)) = some (b :: s_p) := by
      rw [h_after, hbpush]
    rw [h_split, btFold_append, h1] at hS; exact hS
  -- (7) frame-inverse over `interior` with base `[]`, extra `b :: s_p`.
  have h_int_len : interior.length = a - (p + 1) := by
    rw [hint, List.length_take, List.length_drop, Array.length_toList]; omega
  have hfloor' : ∀ k, k ≤ interior.length →
      0 ≤ (([] : List Bool).length : Int) + pbalance (interior.take k) := by
    intro k hk
    have hk' : k ≤ a - (p + 1) := by rw [h_int_len] at hk; exact hk
    have htk : interior.take k = (tokens.toList.drop (p + 1)).take k := by
      rw [hint, List.take_take]; congr 1; omega
    have hbridge : flowBracketBalance tokens (p + 1) (p + 1 + k)
        = pbalance ((tokens.toList.drop (p + 1)).take k) := by
      rw [flowBracketBalance_eq_pbalance tokens (p + 1) (p + 1 + k) (by omega)]; congr 2; omega
    have hfl : (0 : Int) ≤ pbalance ((tokens.toList.drop (p + 1)).take k) := by
      rw [← hbridge]; exact h_floor (p + 1 + k) (by omega) (by omega)
    rw [htk]; simpa using hfl
  obtain ⟨m, hm, hSm⟩ := btFold_frame_inv interior [] (b :: s_p) S hfloor'
    (by rw [List.nil_append]; exact hfold)
  -- (8) interior balance 0 ⟹ m = [].
  have hint_bal : pbalance interior = 0 := by
    have he : flowBracketBalance tokens (p + 1) a = pbalance interior := by
      rw [hint, flowBracketBalance_eq_pbalance tokens (p + 1) a (by omega)]
    rw [← he]; exact h_bal
  have hm_len : (m.length : Int) = 0 := by
    have hl := btFold_length interior [] m hm
    simp only [List.length_nil] at hl
    rw [hl]; simpa using hint_bal
  have hm_nil : m = [] := List.eq_nil_of_length_eq_zero (by exact_mod_cast hm_len)
  rw [hm_nil, List.nil_append] at hSm
  -- (9) S = b :: s_p ⟹ head = b; gate head = false ⟹ b = false ⟹ mapStart.
  rw [hSm] at h_mark
  simp only [List.head?_cons, Option.bind_some] at h_mark
  exact hb_map (Option.some.inj h_mark)

/-- **The forward CLOSE of the located enclosing map** — the `some false`/`{` axis-dual of
    `seqClose_of_located_and_enclosing` (`:1027`), the matching-close brick of the MAP descent.  Given
    the located enclosing opener `p` — now PROVEN a `.flowMappingStart` (`mapOpenerType_of_located_and_gate`,
    R538) at depth `0` of the enclosing recursion window `[lo, hi)` (the discriminator
    `flowBracketBalance tokens lo p = 0`, [[ref-root-seed-discriminator-not-from-gate]]) — locate its
    matching close `hiS = j` and deliver the bounds the map enclosing-facts provider needs.

    Per [[ref-axis-dual-from-typeagnostic-core]] this dual is a near-verbatim text-swap of the seq twin.
    The matching-close locator is GENERIC in the bracket type: the `_map` specialisation
    `flowBracketBalance_matching_close_map` (`WellBracketed.lean:2122`) bundles the typed `.flowMappingEnd`
    exactly as the `_seq` one bundles `.flowSequenceEnd` (both push `[true]`/`[false]` internally and pop
    via `btStep_pop_eq_{seq,map}End`).  The entire two-floor relay that recovers the containment bounds
    `a ≤ j`, `b ≤ j` is TYPE-AGNOSTIC — it reads only `flowBracketDelta tokens[j]!.val = -1` (true of
    `.flowMappingEnd` as of `.flowSequenceEnd`, `ParserGrammableBase.lean:508`) and balances, never the
    bracket type.  So the ONLY proof-text difference from the seq twin is the THREE tokens
    (`flowBracketBalance_matching_close_seq → _map`, `.flowSequenceStart → .flowMappingStart`,
    `.flowSequenceEnd → .flowMappingEnd`); the proof body is byte-identical (no branch-vacuity flip here —
    that was spent at R538's opener-type dispatch; the close has no bit-consuming dispatch of its own).

    Delivered as the shape the map enclosing-facts provider consumes: `hiS = j` with `a ≤ hiS`,
    `b ≤ hiS`, `hiS ≤ tokens.size`, `flowBracketBalance tokens (p+1) hiS = 0` (the body `[p+1, j)`
    balances — feeds the map child's window) and the typed close `.flowMappingEnd`.

    The two containment bounds come for free from the two floors (this is why R514's gate floor was
    load-bearing): the close at `j` makes the next step underflow, refuted by the **locator floor**
    (`h_loc_floor` over `[p+1, a]`) for `a ≤ j`, then by the **gate floor** (`h_gate_floor` over `[a, b]`)
    for `b ≤ j` — the [[ref-two-floor-relay-close-bound]] relay, type-agnostic.

    Verified-but-unconsumed (R539): its consumer — `mapDescent_provider_of_located` /
    `mapEnclosingFacts_provider_of_located` — does not exist yet; references no sorry site; frontier sorry
    count holds at 4.  Axioms byte-identical to the seq twin (the dual threads the same dependencies via
    `flowBracketBalance_matching_close_map`, [[ref-mirror-inherits-dependency-axioms]]). -/
theorem mapClose_of_located_and_enclosing
    (tokens : Array (Positioned YamlToken)) (a b lo p hi : Nat)
    (h_lo_p : lo ≤ p) (h_pa : p < a) (h_ab : a ≤ b) (h_b_hi : b ≤ hi)
    (h_hi_sz : hi ≤ tokens.size)
    (h_p_depth : flowBracketBalance tokens lo p = 0)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_win_floor : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_open : tokens[p]!.val = .flowMappingStart)
    (h_body_bal : flowBracketBalance tokens (p + 1) a = 0)
    (h_loc_floor : ∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0)
    (h_gate_floor : ∀ i, a ≤ i → i ≤ b → flowBracketBalance tokens a i ≥ 0)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo)) :
    ∃ hiS, a ≤ hiS ∧ b ≤ hiS ∧ hiS ≤ tokens.size ∧
      flowBracketBalance tokens (p + 1) hiS = 0 ∧
      tokens[hiS]!.val = .flowMappingEnd := by
  have h_p_hi : p < hi := by omega
  -- Matching close + typed close in one call (base `lo`, opener `k := p`).  The `_map` locator is the
  -- only token that differs from the seq close brick.
  obtain ⟨j, h_pj, h_jhi, h_jclose, h_inner, _⟩ :=
    flowBracketBalance_matching_close_map tokens lo p hi h_lo_p h_p_hi h_hi_sz
      h_p_depth h_open h_total h_win_floor h_wt
  have h_jdelta : flowBracketDelta tokens[j]!.val = -1 := by rw [h_jclose]; rfl
  -- One-step balance recurrence at `j` over any base `≤ j` (type-agnostic, verbatim from the seq twin).
  have step : ∀ base, base ≤ j →
      flowBracketBalance tokens base (j + 1)
        = flowBracketBalance tokens base j + flowBracketDelta tokens[j]!.val := by
    intro base hbase
    have h_j_sz : j < tokens.size := by omega
    have hlen : j < tokens.toList.length := by rw [Array.length_toList]; exact h_j_sz
    rw [flowBracketBalance_compose tokens base j (j + 1) hbase (by omega),
        flowBracketBalance_single tokens j hlen]
    have h1 : tokens.toList[j]'hlen = tokens[j] := Array.getElem_toList h_j_sz
    have h2 : tokens[j] = tokens[j]! := (getElem!_pos tokens j h_j_sz).symm
    rw [h1, h2]
  -- (1) `a ≤ j` from the locator floor at `j + 1`.
  have h_a_j : a ≤ j := by
    rcases Nat.lt_or_ge j a with h | h
    · have h_floor := h_loc_floor (j + 1) (by omega) (by omega)
      rw [step (p + 1) (by omega), h_inner, h_jdelta] at h_floor
      omega
    · exact h
  -- (2) `balance a j = 0` by composition over `[p+1, a, j]`.
  have h_aj_bal : flowBracketBalance tokens a j = 0 := by
    have hc := flowBracketBalance_compose tokens (p + 1) a j (by omega) h_a_j
    rw [h_inner, h_body_bal] at hc; omega
  -- (3) `b ≤ j` from the GATE floor at `j + 1`.
  have h_b_j : b ≤ j := by
    rcases Nat.lt_or_ge j b with h | h
    · have h_floor := h_gate_floor (j + 1) (by omega) (by omega)
      rw [step a h_a_j, h_aj_bal, h_jdelta] at h_floor
      omega
    · exact h
  exact ⟨j, h_a_j, h_b_j, by omega, h_inner, h_jclose⟩

/-- `ContentStartTok` (the head predicate of a seq body's unit entries) never holds of a `.flowEntry`:
    it is a scalar / `[` / `{`, never the separator `,`.  This is the `hQ` the no-trailing-comma
    substrate lemma needs to refute a lone-separator unit. -/
theorem ContentStartTok_ne_flowEntry : ∀ v, ContentStartTok v → v ≠ .flowEntry := by
  rintro v (⟨c, st, rfl⟩ | rfl | rfl) <;> simp

/-- **Both separator facts from a windowed `SafeBodyUnit`** — the per-window discharge the root seed
    `(i'-b-descend-root)` consumes at every reached seq level.  The seq body producer delivers, over
    each seq-typed body window `[a,b)`, a `SafeBodyUnit ContentStartTok ((tokens.toList.take b).drop a)`
    (directly from emission — `emitList_body_filtered_characterization` / `RecSeqBody.toSafeBodyUnit`,
    NOT circular through the not-yet-built recursion output).  This single substrate yields BOTH of the
    carrier's asserted facts:

    * `bodySuccFact` — values are comma-separated — via `SafeBodyUnit_array_succ_window` (value-end
      successor, the panic-indexing bridge identical to `seqBodyProps_of_windowed_safebody`'s
      `h_body_succ` branch);
    * `noTrailingSepFact` — no trailing comma — via `SafeBodyUnit_array_last_not_sep_window`
      *vacuously*: it refutes a depth-`0` `.flowEntry` at the window's last position, so the premise is
      contradictory and `isFlowContentStart` follows by `absurd`.

    So the carrier's body is dischargeable from the producer's OWN deliverable: the root seed need only
    establish `SafeBodyUnit` at each seq level, with no separate Part 7 producing lemma. -/
theorem seqSeparatorFacts_of_windowed_safebodyunit
    (tokens : Array (Positioned YamlToken)) (a b : Nat) (h_b : b ≤ tokens.size)
    (h : SafeBodyUnit ContentStartTok ((tokens.toList.take b).drop a)) :
    bodySuccFact tokens a b ∧ noTrailingSepFact tokens a b := by
  refine ⟨?_, ?_⟩
  · -- `bodySuccFact` ← value-end successor
    intro k h_lo h_klt h_bal h_nfe
    have hk_sz : k < tokens.size := Nat.lt_of_lt_of_le h_klt h_b
    rw [getElem!_pos tokens k hk_sz] at h_nfe
    rcases SafeBodyUnit_array_succ_window tokens a b h_b h k h_lo h_klt h_bal h_nfe with
      h_end | ⟨hk1, h_fe⟩
    · exact Or.inl h_end
    · refine Or.inr ⟨hk1, ?_⟩
      have hk1_sz : k + 1 < tokens.size := Nat.lt_of_lt_of_le hk1 h_b
      rw [getElem!_pos tokens (k + 1) hk1_sz]; exact h_fe
  · -- `noTrailingSepFact` ← no-trailing-comma, vacuously (the premise `tokens[k]! = .flowEntry` is refuted)
    intro k h_lo hk1 h_fe _h_bal
    exact absurd h_fe (SafeBodyUnit_array_last_not_sep_window
      ContentStartTok_ne_flowEntry tokens a b h_b h k h_lo hk1 _h_bal)

/-- **Both separator facts from a window's OWN `RecSeqBody`** — the merge-deciding de-risk of
    `(i'-b-B2b-desc-merge)`.  At a DESCENDED seq window `[a,b)` the merged width recursion's IH delivers
    `RecSeqBody ((tokens.toList.take b).drop a)` (the window's own genuine seq body); this lemma shows
    that single deliverable reconstructs BOTH of the carrier's separator facts on `[a,b)` — with NO
    appeal to a pre-built root carrier `SeqInteriorSeparators tokens 2 (size-2)`.

    It is exactly the composition `RecSeqBody.toSafeBodyUnit` ▸ `seqSeparatorFacts_of_windowed_safebodyunit`:
    the IH's `RecSeqBody` projects to the windowed `SafeBodyUnit ContentStartTok ((take b).drop a)` that
    the latter consumes.  The composition type-checks gap-free for ANY window (in particular the
    descend-at-root `[3,5)` of `[[1,2],9]` and the advance-then-descend `[5,8)` of `[1,[2,3]]`), so the
    merge is a CLEAN STRENGTHENING: the carrier's per-window demand is satisfiable from the recursion's
    own output, and `seqRoot_seqInteriorSeparators` need NOT thread the root carrier as an ambient.
    `desc` becomes a corollary at the located enclosing window, fed `seqEnclosed_succ_of_located_opener`
    (R324) for the `h_q_succ` and the located close for the fourth `G`-conjunct. -/
theorem seqSeparatorFacts_of_recseqbody
    (tokens : Array (Positioned YamlToken)) (a b : Nat) (h_b : b ≤ tokens.size)
    (h : RecSeqBody ((tokens.toList.take b).drop a)) :
    bodySuccFact tokens a b ∧ noTrailingSepFact tokens a b :=
  seqSeparatorFacts_of_windowed_safebodyunit tokens a b h_b h.toSafeBodyUnit

/-- **A `Q`-headed `EntryUnit` is an `EntrySafe`** — the per-entry half of the `SafeBodyUnit → SafeBody`
    coercion below.  `EntryUnit` strengthens `EntrySafe` everywhere EXCEPT the head: `EntryUnit`'s
    `≥ 1` interior condition is stated for *proper nonempty* prefixes (`0 < i`), so it already gives
    `EntrySafe`'s `.flowEntry`-at-balance-`≥ 1` obligation at every `i > 0`; only the `i = 0` head case
    is open.  A `Q`-head with `hQ : Q v → v ≠ .flowEntry` closes it: the head cannot BE a `.flowEntry`,
    so the `i = 0` obligation is vacuous.  (Without the head hypothesis a lone-`.flowEntry` IS an
    `EntryUnit` but not an `EntrySafe`, so `hQ` is genuinely needed.) -/
theorem EntryUnit_entrySafe {Q : YamlToken → Prop} (hQ : ∀ v, Q v → v ≠ .flowEntry)
    {e : List (Positioned YamlToken)} (h_ne : e ≠ []) (h_unit : EntryUnit e)
    (h_head : Q (e.head h_ne).val) : EntrySafe e := by
  refine ⟨h_unit.1, fun i h_i h_fe => ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · -- i = 0: the head would be a `.flowEntry`, contradicting the `Q`-head via `hQ`.
    rw [List.head_eq_getElem] at h_head
    exact absurd h_fe (hQ _ h_head)
  · -- i > 0: `EntryUnit`'s proper-prefix condition gives the `≥ 1` balance directly.
    exact h_unit.2 i hipos h_i

/-- **`SafeBodyUnit Q → SafeBody Q`** (given `hQ : ∀ v, Q v → v ≠ .flowEntry`).  Both inductives share
    their shape (nonempty `Q`-headed entries separated by single `.flowEntry`s); they differ only in the
    per-entry refinement (`EntryUnit` vs `EntrySafe`), and `EntryUnit_entrySafe` bridges that for each
    `Q`-headed entry.  So a windowed `SafeBodyUnit ContentStartTok` body — the single substrate the
    enclosing-facts provider keys on — also satisfies the WEAKER `SafeBody`, unlocking the existing
    `SafeBody_array_flowEntry_window` (post-separator content-start) wrapper for the `feContentStart`
    fact below WITHOUT a second producer deliverable.  (The producer's `RecSeqBody` projects to both via
    `RecSeqBody.toSafeBody`/`.toSafeBodyUnit`; this coercion lets the consume side stay keyed on ONE
    `SafeBodyUnit`, per `ref-fold-consumer-chain-to-producer-contract`.) -/
theorem SafeBodyUnit_safeBody {Q : YamlToken → Prop} (hQ : ∀ v, Q v → v ≠ .flowEntry)
    {body : List (Positioned YamlToken)} (h : SafeBodyUnit Q body) : SafeBody Q body := by
  induction h with
  | single e h_ne h_unit h_head =>
      exact SafeBody.single e h_ne (EntryUnit_entrySafe hQ h_ne h_unit h_head) h_head
  | cons e fe rest h_ne h_unit h_head h_fe h_rest ih =>
      exact SafeBody.cons e fe rest h_ne (EntryUnit_entrySafe hQ h_ne h_unit h_head) h_head h_fe ih

/-- **The interior `feContentStart` fact from a windowed `SafeBodyUnit`** — the ONE new sub-fact of the
    enclosing bundle `(i'-b-encfacts)` (`bodySuccFact`/`noTrailingSepFact` were already done by
    `seqSeparatorFacts_of_windowed_safebodyunit`).  At every INTERIOR depth-`0` separator `k` of the
    window `[a,b)` (`a ≤ k`, `k+1 < b`, `tokens[k]! = .flowEntry`, `flowBracketBalance tokens a k = 0`),
    the successor token is flow-content-start.  This is the comma→content alternation of a seq body: a
    depth-`0` `.flowEntry` is a separator BETWEEN units, and the unit that follows starts with a
    `ContentStartTok` head.

    The proof coerces the `SafeBodyUnit` to a `SafeBody` (`SafeBodyUnit_safeBody`) and applies the
    existing post-separator wrapper `SafeBody_array_flowEntry_window`, whose `Q`-successor conclusion is
    `ContentStartTok (tokens[k+1]).val` — definitionally `isFlowContentStart (tokens[k+1]).val`.  The
    only glue is the `getElem!`↔`getElem` panic-index bridge.  De-risked on `[[1, 2], 9]`: at the
    enclosing seqs `[3,6)`/`[2,9)` the interior commas at `4`/`7` are followed by content at `5`/`8`. -/
theorem seqInteriorFeContentStart_of_windowed_safebodyunit
    (tokens : Array (Positioned YamlToken)) (a b : Nat) (h_b : b ≤ tokens.size)
    (h : SafeBodyUnit ContentStartTok ((tokens.toList.take b).drop a)) :
    ∀ k, a ≤ k → k + 1 < b →
      tokens[k]!.val = .flowEntry → flowBracketBalance tokens a k = 0 →
      isFlowContentStart tokens[k + 1]!.val := by
  intro k h_lo h_klt h_fe h_bal
  have hk_sz : k < tokens.size := by omega
  rw [getElem!_pos tokens k hk_sz] at h_fe
  obtain ⟨hk1, hQ⟩ := SafeBody_array_flowEntry_window tokens a b h_b
    (SafeBodyUnit_safeBody ContentStartTok_ne_flowEntry h) k h_lo (by omega) h_fe h_bal
  have hk1_sz : k + 1 < tokens.size := Nat.lt_of_lt_of_le hk1 h_b
  rw [getElem!_pos tokens (k + 1) hk1_sz]
  exact hQ

/-- **The THREE-fact enclosing bundle from ONE windowed `SafeBodyUnit`** — the per-window deliverable
    `(i'-b-encfacts)` that the `provider` of `seqInteriorSeparators_of_enclosing_provider` must supply
    at each located enclosing seq `[loS,hiS)`.  A single windowed
    `SafeBodyUnit ContentStartTok ((tokens.toList.take b).drop a)` — which the seq-body producer delivers
    at every genuine seq body (`RecSeqBody.toSafeBodyUnit`, no recursion through the not-yet-built
    output) — yields ALL THREE facts the two rebases consume:

    * `bodySuccFact tokens a b` (`bodySuccFact_rebase`'s source) and
    * `noTrailingSepFact tokens a b` (`noTrailingSepFact_rebase`'s no-trailing source) — both from
      `seqSeparatorFacts_of_windowed_safebodyunit`;
    * the interior depth-`0` `feContentStart` (`noTrailingSepFact_rebase`'s `h_enc_fe` source) — from
      `seqInteriorFeContentStart_of_windowed_safebodyunit`.

    So the provider's deliverable at a located enclosing seq is *exactly* a windowed `SafeBodyUnit`;
    `(i'-b-encfacts)` is closed and the residual narrows to `(i'-b-locator)` — recover the enclosing
    `.flowSequenceStart`/matching-close and its windowed `SafeBodyUnit` (the `btFold`-top → opener
    converse of `enclosingMark_true_of_opener`, reusing `recseqentry_seqbracket_oracle`). -/
theorem seqEnclosingFacts_of_windowed_safebodyunit
    (tokens : Array (Positioned YamlToken)) (a b : Nat) (h_b : b ≤ tokens.size)
    (h : SafeBodyUnit ContentStartTok ((tokens.toList.take b).drop a)) :
    bodySuccFact tokens a b ∧
    (∀ k, a ≤ k → k + 1 < b →
      tokens[k]!.val = .flowEntry → flowBracketBalance tokens a k = 0 →
      isFlowContentStart tokens[k + 1]!.val) ∧
    noTrailingSepFact tokens a b := by
  obtain ⟨h_bs, h_nts⟩ := seqSeparatorFacts_of_windowed_safebodyunit tokens a b h_b h
  exact ⟨h_bs, seqInteriorFeContentStart_of_windowed_safebodyunit tokens a b h_b h, h_nts⟩

/-- **The enclosing-facts `provider`, ASSEMBLED from a LOCATED enclosing seq** — the
    [[ref-parametric-assembler-extraction]] split of the provider's locate boundary, serving BOTH the
    root seed and the descent.  Lift the locator's eventual output as hypotheses — a located enclosing
    seq body `[loS, hiS)` with the gated window re-seated at its top level
    (`flowBracketBalance tokens loS a = 0`), enclosing the window (`loS ≤ a`, `b ≤ hiS`), and its
    windowed `SafeBodyUnit` — and the provider's existential is discharged in ONE line via
    `seqEnclosingFacts_of_windowed_safebodyunit`.  No locate analysis here: that is isolated as the
    residual (the `SafeBodyUnit` + the bounds are exactly what the locator produces).

    This factors the whole provider into ASSEMBLE (here, trivial) vs LOCATE (the residual):

    * the **root** instance specialises `loS = 2`, `hiS = size - 2`, with the `SafeBodyUnit` from
      `seqRoot_safeBodyUnit` (emission, no recursion) — `seqEnclosingFacts_provider_root` below is now
      this lemma at the outer window;
    * the **descent** instance, at a nested gated window where the top-level discriminator
      `flowBracketBalance tokens 2 a = 0` FAILS, locates the innermost enclosing seq via the backward
      enclosing-opener scan and recovers its `SafeBodyUnit` from the recursion
      (`recseqentry_seqbracket_oracle` / `RecSeqBody.toSafeBodyUnit`) — the owed residual.

    **De-risk (`#guard`-backed, `Tests/Guards/Proofs/SeqDescentLocatorProbe.lean`, on `[[1, 2], 9]`).**
    The lifted hypotheses are SATISFIABLE on NESTED gated windows (per
    [[ref-probe-provider-satisfiable-before-assembler]]): at the nested window `[3, 6)`
    (`flowBracketBalance tokens 2 3 = 1`, so the root discriminator fails) the backward scan locates
    `loS = 3`, `hiS = 6` with `flowBracketBalance tokens loS a = 0`, `loS ≤ a`, `b ≤ hiS`, and the
    located enclosing IS a seq (the gate's `btFold`-top at `loS` is `some true`, matching the opener
    `tokens[2] = .flowSequenceStart`) whose `SafeBodyUnit` is the inner seq's — so the assembler is not
    vacuous and the residual (the locator) is genuine.  The split mirrors the consumer-side factoring of
    `seqInteriorSeparators_of_enclosing_provider` ([[ref-reduction-by-import]]). -/
theorem seqEnclosingFacts_provider_of_located
    (tokens : Array (Positioned YamlToken)) (a b loS hiS : Nat)
    (h_loS_a : loS ≤ a) (h_b_hiS : b ≤ hiS) (h_hiS : hiS ≤ tokens.size)
    (h_bal0 : flowBracketBalance tokens loS a = 0)
    (h_safe : SafeBodyUnit ContentStartTok ((tokens.toList.take hiS).drop loS)) :
    ∃ loS hiS, loS ≤ a ∧ b ≤ hiS ∧ flowBracketBalance tokens loS a = 0 ∧
      bodySuccFact tokens loS hiS ∧
      (∀ k, loS ≤ k → k + 1 < hiS →
        tokens[k]!.val = .flowEntry → flowBracketBalance tokens loS k = 0 →
        isFlowContentStart tokens[k + 1]!.val) ∧
      noTrailingSepFact tokens loS hiS :=
  ⟨loS, hiS, h_loS_a, h_b_hiS, h_bal0,
    seqEnclosingFacts_of_windowed_safebodyunit tokens loS hiS h_hiS h_safe⟩

/-- **The ROOT instance of the enclosing-facts `provider`** — `(i'-b-locator)` base case, per
    [[ref-universal-producer-root-seed-first]].  At the outermost seq `[2, size-2)` of a concrete
    flow-sequence output `"[" ++ emitList items ++ "]"`, `seqRoot_safeBodyUnit` delivers the windowed
    `SafeBodyUnit` *directly from emission*, with NO recursion through nested seq windows.  Feeding it
    through `seqEnclosingFacts_of_windowed_safebodyunit` gives the three enclosing facts at
    `loS = 2`, `hiS = size - 2`, so for any gated sub-window `[a,b)` whose enclosing seq IS the outer
    one — characterised by the **top-level discriminator** `flowBracketBalance tokens 2 a = 0`
    (the window starts at the outer seq's depth, not nested deeper) — the provider's existential is
    satisfied by `⟨2, size-2, …⟩`.

    This pins `provider` at the root: the bounds `2 ≤ a`, `b ≤ size-2` and the discriminator are
    exactly `loS ≤ a`, `b ≤ hiS`, `flowBracketBalance tokens loS a = 0`, passed through; the three
    enclosing facts come from the outer-seq `SafeBodyUnit`.  The `loS - 1 = 1` opener is the outer
    `[` — no `recseqentry_seqbracket_oracle` descent is consulted (the descent supplies the SAME
    existential at nested levels, the inductive step owed separately).  The discriminator
    `flowBracketBalance tokens 2 a = 0` is what the locator's descent establishes for root-level
    windows (the gate `SeqTypedInterior` alone admits deeper-nested windows too, so it cannot be
    derived here — it is the root case's hypothesis). -/
theorem seqEnclosingFacts_provider_root
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v) :
    ∀ a b, 2 ≤ a → a ≤ b → b ≤ tokens.size - 2 → flowBracketBalance tokens 2 a = 0 →
      ∃ loS hiS, loS ≤ a ∧ b ≤ hiS ∧ flowBracketBalance tokens loS a = 0 ∧
        bodySuccFact tokens loS hiS ∧
        (∀ k, loS ≤ k → k + 1 < hiS →
          tokens[k]!.val = .flowEntry → flowBracketBalance tokens loS k = 0 →
          isFlowContentStart tokens[k + 1]!.val) ∧
        noTrailingSepFact tokens loS hiS := by
  intro a b ha hab hb hbal
  exact seqEnclosingFacts_provider_of_located tokens a b 2 (tokens.size - 2)
    ha hb (by omega) hbal (seqRoot_safeBodyUnit items tokens h_scan h_ne h_all)

/-- **The gate makes the backward locator INVOKABLE** — `(i'-b-locator-glue-gate-bridge)`.  At any
    gated window `[a,b)` the gate `SeqTypedInterior tokens a b` carries a `btFold`-top `= some true`
    after the prefix `[0,a)` (its second conjunct: the enclosing bracket is a seq).  A non-empty typed
    stack forces `flowBracketBalance tokens 0 a ≥ 1` (`flowBracketBalance_pos_of_btFold_head`) — exactly
    the hypothesis of `flowBracketBalance_backward_open_locate`.  So the pure-balance backward
    enclosing-opener locator can be invoked at every nested gated window, the FIRST glue brick of the
    descent.  (Type-agnostic: the map mirror's `= some false` gate feeds the same core lemma verbatim.) -/
theorem flowBracketBalance_pos_of_seqTypedInterior
    (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h : SeqTypedInterior tokens a b) :
    flowBracketBalance tokens 0 a ≥ 1 :=
  flowBracketBalance_pos_of_btFold_head tokens a true h.2.1

/-- **The gate LOCATES the enclosing opener with the exact facts the descent assembler reads** —
    `(i'-b-B2a-locator-glue)`, the locator half of the `desc` descent driver
    ([[ref-from-located-assembler-direction]]: factor the descent's locate boundary; this is the
    LOCATE, `seqDescent_provider_of_located` is the assemble).

    At any nested gated window `[a, b)` the gate `SeqTypedInterior tokens a b` carries
    `flowBracketBalance tokens 0 a ≥ 1` (`flowBracketBalance_pos_of_seqTypedInterior` — its `btFold`-top
    `= some true` forces a non-empty typed stack), exactly the hypothesis that makes the pure-balance
    backward scan `flowBracketBalance_backward_open_locate` invokable.  That scan returns the innermost
    unmatched opener `p < a` together with the THREE locator facts — `flowBracketDelta tokens[p]! = 1`,
    `flowBracketBalance tokens (p+1) a = 0`, and the interior floor `∀ i ∈ [p+1, a], balance (p+1) i ≥ 0`.

    **De-risk finding (the B2 split, this brick's whole point).** Those four outputs are *definitionally*
    the four opener hypotheses `seqDescent_provider_of_located` consumes (`h_pa`, `h_delta`,
    `h_body_bal`, `h_loc_floor`) — verified term-for-term.  So the descent's LOCATE half needs **no fresh
    backward fixpoint**: the backward scan already runs its own `Nat.strongRecOn` internally
    ([[ref-backward-locator-mirrors-forward]]).  The only residual of the `desc` driver (B2b) is then the
    recursion-window plumbing — supplying `[p, hi)` as a `FlowBodyWindow`/`Deep`/`Content` plus the width
    IH — which consumes the EXISTING outer `RecSeqBody` width recursion's IH, not a new one.  This brick
    lands the locate glue decoupled, isolating B2b as the single remaining seq residual.

    Type-agnostic core: the map mirror reads the gate's `= some false` top, gets `balance 0 a ≥ 1` from
    the same `flowBracketBalance_pos_of_btFold_head`, and calls the identical backward locator. -/
theorem seqEnclosingOpener_of_gate
    (tokens : Array (Positioned YamlToken)) (a b : Nat) (h_a_sz : a ≤ tokens.size)
    (h_gate : SeqTypedInterior tokens a b) :
    ∃ p, p < a ∧ flowBracketDelta tokens[p]!.val = 1 ∧
      flowBracketBalance tokens (p + 1) a = 0 ∧
      (∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) :=
  flowBracketBalance_backward_open_locate tokens a h_a_sz
    (flowBracketBalance_pos_of_seqTypedInterior tokens a b h_gate)

/-- **The located opener is a `[`** — `(i'-b-locator-glue-opener-type)`, the second glue brick of the
    descent (after `flowBracketBalance_pos_of_seqTypedInterior` makes the backward locator invokable).
    Given the backward locator's full output at the gated window start `a` — an opener `p` with
    `flowBracketDelta tokens[p]! = 1` (so `tokens[p]` is `[` or `{`), the body balance
    `flowBracketBalance tokens (p+1) a = 0`, and the **interior floor** `flowBracketBalance tokens (p+1) i ≥ 0`
    over `(p, a]` (R311's restored conjunct) — PLUS the gate's `btFold`-top `= some true` after the
    prefix `[0,a)`, the located opener `tokens[p]` is a `.flowSequenceStart`.

    **Why the floor is load-bearing.** R311's minimal pair (`[{}, ["9"]]`) showed the bare existential
    admits a spurious map-opener; the floor is the discriminator that pins `p` to the INNERMOST opener.
    Mechanically (the head-preservation route): the typed stack after `[0,p+1)` is `b :: s_p` where `b`
    is the bit `tokens[p]` pushes (`b = true ↔ seqStart`).  The interior body `(take a).drop (p+1)` has
    relative balance `0` and floor `≥ 0`, so it NEVER pops `b` and returns the stack to `b :: s_p` at `a`
    — proved by `btFold_frame_inv` (the converse of `btFold_frame`): with base `[]` and extra `b :: s_p`,
    the interior fold from `[]` is well-typed (length `0` by `btFold_length` + balance `0`), so the whole
    stack at `a` is `b :: s_p`.  Its head is `b`, which the gate fixes to `true`, forcing `tokens[p]` to
    be the seq opener.  The gate supplies definedness of the whole `take a` fold; the floor supplies that
    `b` survives.  Type-agnostic substrate: the map mirror reads the gate's `= some false` and concludes
    `.flowMappingStart` by the identical argument with `b = false`. -/
theorem seqOpenerType_of_located_and_gate
    (tokens : Array (Positioned YamlToken)) (a p : Nat)
    (h_pa : p < a) (h_a_sz : a ≤ tokens.size)
    (h_delta : flowBracketDelta tokens[p]!.val = 1)
    (h_bal : flowBracketBalance tokens (p + 1) a = 0)
    (h_floor : ∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0)
    (h_mark : (btFold (some []) (tokens.toList.take a)).bind (·.head?) = some true) :
    tokens[p]!.val = .flowSequenceStart := by
  have h_p_sz : p < tokens.size := by omega
  have h_p_T : p < tokens.toList.length := by rw [Array.length_toList]; exact h_p_sz
  -- (1) the gate forces the whole `take a` fold to `some S` with head `true`.
  obtain ⟨S, hS⟩ : ∃ S, btFold (some []) (tokens.toList.take a) = some S := by
    cases hc : btFold (some []) (tokens.toList.take a) with
    | none => rw [hc] at h_mark; simp at h_mark
    | some S => exact ⟨S, rfl⟩
  rw [hS] at h_mark
  -- (2) `take a = take (p+1) ++ interior`, interior the body slice.
  obtain ⟨interior, hint⟩ :
      ∃ I, I = (tokens.toList.drop (p + 1)).take (a - (p + 1)) := ⟨_, rfl⟩
  have h_split : tokens.toList.take a = tokens.toList.take (p + 1) ++ interior := by
    rw [hint, ← List.take_add]; congr 1; omega
  -- (3) the prefix `take p` folds to `some s_p`.
  have h_split_p : tokens.toList.take (p + 1)
      = tokens.toList.take p ++ [tokens.toList[p]'h_p_T] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h_p_T]; rfl
  obtain ⟨s_p, hsp⟩ : ∃ s_p, btFold (some []) (tokens.toList.take p) = some s_p :=
    btFold_some_prefix (tokens.toList.take p) ([tokens.toList[p]'h_p_T] ++ interior) S (by
      rw [← List.append_assoc, ← h_split_p, ← h_split]; exact hS)
  -- (4) the stack just after the opener is `b :: s_p`.
  have hTp : tokens.toList[p]'h_p_T = tokens[p]! := by
    rw [Array.getElem_toList, getElem!_pos tokens p h_p_sz]
  have h_after : btFold (some []) (tokens.toList.take (p + 1)) = btStep tokens[p]! s_p := by
    rw [h_split_p, btFold_append, hsp]
    have : btFold (some s_p) [tokens.toList[p]'h_p_T] = btStep (tokens.toList[p]'h_p_T) s_p := rfl
    rw [this, hTp]
  -- (5) the opener is a `[` or `{` (delta = 1); get the pushed bit `b`.
  obtain ⟨b, hbpush, hb_seq⟩ :
      ∃ b, btStep tokens[p]! s_p = some (b :: s_p) ∧
        (b = true → tokens[p]!.val = .flowSequenceStart) := by
    rcases (flowBracketDelta_eq_one_iff _).mp h_delta with hseq | hmap
    · exact ⟨true, by simp [btStep, hseq], fun _ => hseq⟩
    · exact ⟨false, by simp [btStep, hmap], fun h => absurd h (by decide)⟩
  -- (6) the whole `take a` fold equals the interior fold from `b :: s_p`.
  have hfold : btFold (some (b :: s_p)) interior = some S := by
    have h1 : btFold (some []) (tokens.toList.take (p + 1)) = some (b :: s_p) := by
      rw [h_after, hbpush]
    rw [h_split, btFold_append, h1] at hS; exact hS
  -- (7) frame-inverse over `interior` with base `[]`, extra `b :: s_p`.
  have h_int_len : interior.length = a - (p + 1) := by
    rw [hint, List.length_take, List.length_drop, Array.length_toList]; omega
  have hfloor' : ∀ k, k ≤ interior.length →
      0 ≤ (([] : List Bool).length : Int) + pbalance (interior.take k) := by
    intro k hk
    have hk' : k ≤ a - (p + 1) := by rw [h_int_len] at hk; exact hk
    have htk : interior.take k = (tokens.toList.drop (p + 1)).take k := by
      rw [hint, List.take_take]; congr 1; omega
    have hbridge : flowBracketBalance tokens (p + 1) (p + 1 + k)
        = pbalance ((tokens.toList.drop (p + 1)).take k) := by
      rw [flowBracketBalance_eq_pbalance tokens (p + 1) (p + 1 + k) (by omega)]; congr 2; omega
    have hfl : (0 : Int) ≤ pbalance ((tokens.toList.drop (p + 1)).take k) := by
      rw [← hbridge]; exact h_floor (p + 1 + k) (by omega) (by omega)
    rw [htk]; simpa using hfl
  obtain ⟨m, hm, hSm⟩ := btFold_frame_inv interior [] (b :: s_p) S hfloor'
    (by rw [List.nil_append]; exact hfold)
  -- (8) interior balance 0 ⟹ m = [].
  have hint_bal : pbalance interior = 0 := by
    have he : flowBracketBalance tokens (p + 1) a = pbalance interior := by
      rw [hint, flowBracketBalance_eq_pbalance tokens (p + 1) a (by omega)]
    rw [← he]; exact h_bal
  have hm_len : (m.length : Int) = 0 := by
    have hl := btFold_length interior [] m hm
    simp only [List.length_nil] at hl
    rw [hl]; simpa using hint_bal
  have hm_nil : m = [] := List.eq_nil_of_length_eq_zero (by exact_mod_cast hm_len)
  rw [hm_nil, List.nil_append] at hSm
  -- (9) S = b :: s_p ⟹ head = b; gate head = true ⟹ b = true ⟹ seqStart.
  rw [hSm] at h_mark
  simp only [List.head?_cons, Option.bind_some] at h_mark
  exact hb_seq (Option.some.inj h_mark)

/-- **The forward CLOSE of the located enclosing seq** — `(i'-b-locator-glue-close)`, brick (3) of
    the descent.  Given the located enclosing opener `p` — now PROVEN a `.flowSequenceStart`
    (`seqOpenerType_of_located_and_gate`) at depth `0` of the enclosing recursion window `[lo, hi)`
    (the discriminator `flowBracketBalance tokens lo p = 0`, [[ref-root-seed-discriminator-not-from-gate]]) —
    locate its matching close `hiS = j` and deliver the bounds the enclosing-facts provider needs.

    The enclosing window is well-bracketed: `flowBracketBalance tokens lo hi = 0` with the window Dyck
    floor `∀ i ∈ [lo, hi], balance lo i ≥ 0` (the recursion carries both for the parent seq body), and
    `WellTyped` of its slice.  So `flowBracketBalance_matching_close_seq` (base `lo`, `k := p`) yields a
    `j` with `p < j < hi`, the typed close `tokens[j]!.val = .flowSequenceEnd`, and `balance (p+1) j = 0`
    — matching-close AND close-type in one call.

    **The two containment bounds come for free from the two floors** (this is why R313's gate floor was
    load-bearing).  The close at `j` makes the next step underflow: `balance β (j+1) = balance β j +
    flowBracketDelta tokens[j]!.val = balance β j - 1`.

    * `a ≤ j` — else `j + 1 ≤ a`, so the **locator floor** (`h_loc_floor` over `[p+1, a]`) at `j + 1`
      forces `balance (p+1) (j+1) ≥ 0`, contradicting `balance (p+1) j - 1 = -1`.
    * `b ≤ j` — else `j + 1 ≤ b`; with `a ≤ j` (hence `a ≤ j + 1`) the **GATE floor** (`h_gate_floor`
      over `[a, b]`) at `j + 1` forces `balance a (j+1) ≥ 0`, contradicting `balance a j - 1 = -1`
      (`balance a j = 0` by composition: `balance (p+1) j = balance (p+1) a + balance a j = 0 + balance a j`).

    Delivered as the shape `seqEnclosingFacts_provider_of_located` consumes: `hiS = j` with `a ≤ hiS`,
    `b ≤ hiS`, `hiS ≤ tokens.size` (from `j < hi ≤ size`), `flowBracketBalance tokens (p+1) hiS = 0`
    (the body `[p+1, j)` balances — feeds brick (4)'s `SafeBodyUnit` window) and the typed close.
    De-risked on `[[1, 2], 9]` and `[[1], [2]]` (`Tests/Guards/Proofs/SeqCloseLocateProbe.lean`): the
    matching-close hypotheses hold at `p` and the two floor contradictions produce `a ≤ j`, `b ≤ j`. -/
theorem seqClose_of_located_and_enclosing
    (tokens : Array (Positioned YamlToken)) (a b lo p hi : Nat)
    (h_lo_p : lo ≤ p) (h_pa : p < a) (h_ab : a ≤ b) (h_b_hi : b ≤ hi)
    (h_hi_sz : hi ≤ tokens.size)
    (h_p_depth : flowBracketBalance tokens lo p = 0)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_win_floor : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_open : tokens[p]!.val = .flowSequenceStart)
    (h_body_bal : flowBracketBalance tokens (p + 1) a = 0)
    (h_loc_floor : ∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0)
    (h_gate_floor : ∀ i, a ≤ i → i ≤ b → flowBracketBalance tokens a i ≥ 0)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo)) :
    ∃ hiS, a ≤ hiS ∧ b ≤ hiS ∧ hiS ≤ tokens.size ∧
      flowBracketBalance tokens (p + 1) hiS = 0 ∧
      tokens[hiS]!.val = .flowSequenceEnd := by
  have h_p_hi : p < hi := by omega
  -- Matching close + typed close in one call (base `lo`, opener `k := p`).
  obtain ⟨j, h_pj, h_jhi, h_jclose, h_inner, _⟩ :=
    flowBracketBalance_matching_close_seq tokens lo p hi h_lo_p h_p_hi h_hi_sz
      h_p_depth h_open h_total h_win_floor h_wt
  have h_jdelta : flowBracketDelta tokens[j]!.val = -1 := by rw [h_jclose]; rfl
  -- One-step balance recurrence at `j` over any base `≤ j` (mirrors `matching_close`'s `step`).
  have step : ∀ base, base ≤ j →
      flowBracketBalance tokens base (j + 1)
        = flowBracketBalance tokens base j + flowBracketDelta tokens[j]!.val := by
    intro base hbase
    have h_j_sz : j < tokens.size := by omega
    have hlen : j < tokens.toList.length := by rw [Array.length_toList]; exact h_j_sz
    rw [flowBracketBalance_compose tokens base j (j + 1) hbase (by omega),
        flowBracketBalance_single tokens j hlen]
    have h1 : tokens.toList[j]'hlen = tokens[j] := Array.getElem_toList h_j_sz
    have h2 : tokens[j] = tokens[j]! := (getElem!_pos tokens j h_j_sz).symm
    rw [h1, h2]
  -- (1) `a ≤ j` from the locator floor at `j + 1`.
  have h_a_j : a ≤ j := by
    rcases Nat.lt_or_ge j a with h | h
    · have h_floor := h_loc_floor (j + 1) (by omega) (by omega)
      rw [step (p + 1) (by omega), h_inner, h_jdelta] at h_floor
      omega
    · exact h
  -- (2) `balance a j = 0` by composition over `[p+1, a, j]`.
  have h_aj_bal : flowBracketBalance tokens a j = 0 := by
    have hc := flowBracketBalance_compose tokens (p + 1) a j (by omega) h_a_j
    rw [h_inner, h_body_bal] at hc; omega
  -- (3) `b ≤ j` from the GATE floor at `j + 1`.
  have h_b_j : b ≤ j := by
    rcases Nat.lt_or_ge j b with h | h
    · have h_floor := h_gate_floor (j + 1) (by omega) (by omega)
      rw [step a h_a_j, h_aj_bal, h_jdelta] at h_floor
      omega
    · exact h
  exact ⟨j, h_a_j, h_b_j, by omega, h_inner, h_jclose⟩

/-- **The child `SafeBodyUnit` at a located genuine seq body** — `(i'-b-child-safebodyunit)`, brick
    (4) of the descent.  Once `seqClose_of_located_and_enclosing` (3) has located the enclosing seq's
    matching close `j`, the body `[p+1, j)` is a GENUINE emitted seq interior, and the last hypothesis
    `seqEnclosingFacts_provider_of_located` consumes — `SafeBodyUnit ContentStartTok` of that interior
    slice — follows directly.  Per [[ref-near-leaf-mirror-sheds-machinery]] this is the PRODUCER-side
    simplification of the locate boundary: the `SafeBodyUnit` route R303 killed for ARBITRARY gated
    windows (a separator-headed window passes a head-blind gate but cannot inhabit a `SafeBodyUnit`) is
    VALID here precisely because `[p+1, j)` is the interior of a real `[ … ]` whose opener sits at the
    window head `p`.

    The route is the seq-bracket oracle already in hand.  With the enclosing recursion window `[p, hi)`
    a `FlowBodyWindow`/`FlowBodyContentDeep`/`FlowBodyContent` whose head `tokens[p]` is the
    `.flowSequenceStart` opener, `recseqentry_seqbracket_oracle` — fed the close facts (the typed close
    `tokens[j]! = .flowSequenceEnd`, the interior balance `balance (p+1) j = 0`, and the matched-bracket
    interior floor `∀ i ∈ (p, j], balance p i ≥ 1`, all the matching-close locator's own output) and the
    width-recursion IH — returns `RecSeqBody ((tokens.toList.take j).drop (p+1))` (its first conjunct;
    the second, the trailing separator, is brick (3)'s concern).  `RecSeqBody.toSafeBodyUnit` projects
    that to the windowed `SafeBodyUnit ContentStartTok` verbatim.

    So brick (4) is a thin producer wrapper: the genuine residual it isolates is brick (5), which must
    (a) instantiate the IH via `windowWidth_strongRecOn`, and (b) establish the located window's
    `FlowBodyContentDeep`/`FlowBodyContent` and supply `j` + the interior floor from
    `flowBracketBalance_matching_close`.  De-risked (`Tests/Guards/Proofs/SeqChildSafeBodyProbe.lean`)
    on `[[1, 2], 9]` (inner body `[3, 6)`, opener `p = 2`, close `j = 6`) and `[[1], [2]]` (inner bodies
    `[3, 4)` / `[7, 8)`): the interior floor `≥ 1` over `(p, j]` and the inner balance `= 0` — the
    oracle's witness-dependent hypotheses — hold at each located child, so the wrapper is not vacuous
    ([[ref-probe-provider-satisfiable-before-assembler]]). -/
theorem seqChild_safeBodyUnit (tokens : Array (Positioned YamlToken)) (p hi j : Nat)
    (h_window : FlowBodyWindow tokens p hi)
    (h_deep : FlowBodyContentDeep tokens p hi)
    (h_content : FlowBodyContent tokens p hi)
    (h_open : tokens[p]!.val = .flowSequenceStart)
    (Q : Nat → Prop) (h_q_succ : Q (p + 1))
    (h_ih : ∀ lo' hi', hi' - lo' < hi - p → p ≤ lo' → hi' ≤ hi →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' → Q lo' →
        tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo'))
    (h_pj : p < j) (h_jhi : j < hi) (h_jclose : tokens[j]!.val = .flowSequenceEnd)
    (h_inner : flowBracketBalance tokens (p + 1) j = 0)
    (h_floor : ∀ i, p < i → i ≤ j → flowBracketBalance tokens p i ≥ 1) :
    SafeBodyUnit ContentStartTok ((tokens.toList.take j).drop (p + 1)) :=
  ((recseqentry_seqbracket_oracle tokens p hi h_window h_deep h_content h_open Q h_q_succ h_ih)
    j h_pj h_jhi h_jclose h_inner h_floor).1.toSafeBodyUnit

/-- **The seq child `SafeBodyUnit`, `FlowBodyContentDeepSeq`-keyed** — `(i'-b-B2c-(d)-seq-child)`, R494:
    the `_seq`-family twin of `seqChild_safeBodyUnit` (above), the next consumer-chain link of the
    `_seq` re-thread ([[ref-rethread-stays-in-weaker-twin-family]]) below the width-enc LIFT
    `seqWidthEnc_of_recIH_seq` (R493).  Once the producer side delivers `h_widthEnc` keyed on the
    root-TRUE `FlowBodyContentDeepSeq` ([[ref-root-seed-needs-root-true-guard]]), the consumer
    `seqLocalCarrier_of_widthEnc` extracts the weaker `h_deep : FlowBodyContentDeepSeq tokens p hiE` and
    must feed it down `seqDescent_provider_of_located → seqChild_safeBodyUnit → recseqentry_seqbracket_oracle`.
    The strong chain is strong-keyed at the bottom (`seqChild_safeBodyUnit` transports `h_deep` into
    `recseqentry_seqbracket_oracle`, whose `_seq` twin R415 already landed), so every link needs a `_seq`
    twin; this is the bottom-most missing one.

    **A transporting LIFT, but its re-key cost is #(guard-keyed child names) PLUS the child twin's
    DROPPED-DERIVATION premise** — the sharpening of [[ref-lift-rekeys-by-guard-keyed-child-names]]
    (R493: `cost = #guard-keyed child names`).  `seqChild_safeBodyUnit`'s body reads NO deep field — it is
    one call to `recseqentry_seqbracket_oracle` then `.1.toSafeBodyUnit`, a pure transport
    ([[ref-transporting-lemma-twin-zero-body-edits]]).  So the body cost is the ONE guard-keyed child name
    swapped to its twin (`recseqentry_seqbracket_oracle ↦ recseqentry_seqbracket_oracle_seq`).  But the
    LEAF twin has a STRICTLY LARGER signature: it takes an extra `h_ne : tokens[lo+1]! ≠ .flowSequenceEnd`
    because the strong `FlowBodyContentDeep.openerContentStart` (firing at EVERY delta-`1` opener)
    SELF-DERIVED interior non-emptiness, whereas the weaker `FlowBodyContentDeepSeq.openerContentStart` is
    GUARDED by that very non-emptiness ([[ref-window-absolute-gate-subset-restriction]]) so it cannot.
    That dropped self-derivation becomes a THREADED premise the lift must FORWARD — `h_ne` here is a new
    hypothesis of this twin, passed straight to the oracle twin.

    **The leaf cannot SOURCE `h_ne`; it climbs.**  The empty seq `[]` (`j = p+1`,
    `tokens[p+1]! = .flowSequenceEnd`) satisfies EVERY hypothesis of `seqChild_safeBodyUnit` — `h_pj`
    (`p < p+1`), `h_jclose`, `h_inner` (`balance (p+1) (p+1) = 0`), `h_floor`
    (`balance p (p+1) = 1 ≥ 1`).  So no local fact refutes it; `h_ne` is genuinely un-derivable at the leaf
    and must be supplied by an ancestor that knows the body is a GENUINE (gated, non-empty) seq — the
    [[ref-prefix-gate-reconstructed-from-boundary]] / [[ref-restored-arm-already-in-classify]] pattern:
    the dropped-derivation premise propagates up the lift chain until sourced.

    cost(re-key a LIFT) = #(guard-keyed child names) + #(child-twin premises the weaker guard FORCED
                          that this lift must forward).            [R494: 1 keyed name + 1 forwarded `h_ne`]

    Verified-but-unconsumed until `seqDescent_provider_of_located_seq` (next) consumes it: composes only
    landed lemmas (the R415 oracle twin), references no sorry site, frontier sorry count unchanged at 4. -/
theorem seqChild_safeBodyUnit_seq (tokens : Array (Positioned YamlToken)) (p hi j : Nat)
    (h_window : FlowBodyWindow tokens p hi)
    (h_deep : FlowBodyContentDeepSeq tokens p hi)
    (h_content : FlowBodyContent tokens p hi)
    (h_open : tokens[p]!.val = .flowSequenceStart)
    (h_ne : tokens[p + 1]!.val ≠ .flowSequenceEnd)
    (Q : Nat → Prop) (h_q_succ : Q (p + 1))
    (h_ih : ∀ lo' hi', hi' - lo' < hi - p → p ≤ lo' → hi' ≤ hi →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeepSeq tokens lo' hi' → Q lo' →
        tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo'))
    (h_pj : p < j) (h_jhi : j < hi) (h_jclose : tokens[j]!.val = .flowSequenceEnd)
    (h_inner : flowBracketBalance tokens (p + 1) j = 0)
    (h_floor : ∀ i, p < i → i ≤ j → flowBracketBalance tokens p i ≥ 1) :
    SafeBodyUnit ContentStartTok ((tokens.toList.take j).drop (p + 1)) :=
  ((recseqentry_seqbracket_oracle_seq tokens p hi h_window h_deep h_content h_open h_ne
      Q h_q_succ h_ih)
    j h_pj h_jhi h_jclose h_inner h_floor).1.toSafeBodyUnit

/-- **The seq child `SafeBody` (full, not unit), `FlowBodyContentDeepSeq`-keyed** —
    `(i'-b-B2c-(d)-seq-child-body)`, R499: the `SafeBody`-projecting SIBLING of `seqChild_safeBodyUnit_seq`
    (R494).  Same located child `[p+1, j)`, same oracle call, but projects the child's `RecSeqBody` through
    `.toSafeBody` instead of `.toSafeBodyUnit`.

    **Why a SECOND projection is needed — the weaker guard's UNIFIED consumer residual forces it.**  The
    `_seq` `FlowBodyContent` assembler `flowBodyContent_of_deepSeq` (R393) demands the separator obligation
    as ONE field `h_feContent : ∀ k, lo ≤ k → k < hi → tokens[k]! = .flowEntry → balance lo k = 0 →
    isFlowContentStart tokens[k+1]!` — EVERY interior depth-`0` separator is followed by content.  The strong
    `flowBodyContent_of_deep` SPLIT that obligation, sourcing the interior from
    `FlowBodyContentDeep.feContentStart` (the all-depth field) and only the BOUNDARY (last position) as a
    `noTrailingSepFact`.  But the weaker `FlowBodyContentDeepSeq.feContentStart` is GUARDED by a `≠ .key`
    premise the descend site cannot discharge locally, so R393 UNIFIED both grains into the single
    `h_feContent` ([[ref-unified-residual-routes-through-one-invariant]]).

    That unification re-prices the producer's projection demand.  The unit projection (`.toSafeBodyUnit`,
    R494) supplies only `bodySuccFact` + `noTrailingSepFact` — and `noTrailingSepFact` covers the LAST
    position ONLY (`k + 1 = b`), discharged vacuously (`seqSeparatorFacts_of_windowed_safebodyunit`).  The
    UNIFIED `h_feContent` ranges over EVERY interior `k`, which `SafeBody_array_flowEntry_window` delivers —
    it fires content-start after every depth-`0` `.flowEntry` — but only off the FULL `SafeBody`, not the
    unit form.  So the SAME child `RecSeqBody` must be projected BOTH ways: `bodySucc` off `.toSafeBodyUnit`
    (R494), the all-interior `feContent` off `.toSafeBody` (here).  This lemma is the second projection the
    weaker-guard's unified residual forced — the strong `flowBodyContent_descend`, whose split residual asked
    only `noTrailingSepFact`, never needed it.  Proof-irrelevant: `RecSeqBody` is a `Prop`, so re-invoking the
    oracle for the second projection costs only proof-term size, nothing semantic ([[ref-complete-projection-family-for-new-member]]).

    Verified-but-unconsumed until `flowBodyContent_descend_seq` (the `_seq` `FlowBodyContent` descend edge)
    consumes it alongside R494: composes only landed lemmas (the R415 oracle twin + `RecSeqBody.toSafeBody`),
    references no sorry site, frontier sorry count unchanged at 4; axiom-clean. -/
theorem seqChild_safeBody_seq (tokens : Array (Positioned YamlToken)) (p hi j : Nat)
    (h_window : FlowBodyWindow tokens p hi)
    (h_deep : FlowBodyContentDeepSeq tokens p hi)
    (h_content : FlowBodyContent tokens p hi)
    (h_open : tokens[p]!.val = .flowSequenceStart)
    (h_ne : tokens[p + 1]!.val ≠ .flowSequenceEnd)
    (Q : Nat → Prop) (h_q_succ : Q (p + 1))
    (h_ih : ∀ lo' hi', hi' - lo' < hi - p → p ≤ lo' → hi' ≤ hi →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeepSeq tokens lo' hi' → Q lo' →
        tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo'))
    (h_pj : p < j) (h_jhi : j < hi) (h_jclose : tokens[j]!.val = .flowSequenceEnd)
    (h_inner : flowBracketBalance tokens (p + 1) j = 0)
    (h_floor : ∀ i, p < i → i ≤ j → flowBracketBalance tokens p i ≥ 1) :
    SafeBody ContentStartTok ((tokens.toList.take j).drop (p + 1)) :=
  ((recseqentry_seqbracket_oracle_seq tokens p hi h_window h_deep h_content h_open h_ne
      Q h_q_succ h_ih)
    j h_pj h_jhi h_jclose h_inner h_floor).1.toSafeBody

/-- **The DESCEND edge for `FlowBodyContent`** — `(i'-b-B2b-desc-merge)`, the load-bearing brick of the
    carrier-elimination merge and the descend twin of `flowBodyContent_advance` (NonemptyStructure).
    `seqWindow_flowBodyContent`'s doc records that there is "deliberately no `flowBodyContent_descend`":
    under the old framing the descend edge was routed through the AMBIENT root carrier
    (`SeqInteriorSeparators tokens 2 (size-2)` narrowed in place), because `bodySucc` has no all-depth
    balance-free form so the child's separator facts cannot be re-based from the parent's (R296).

    The B2b de-risk (R325/R326) found that routing is dispensable: at a DESCENDED seq window `[p+1, j)`
    the child's two separator facts come from the child's OWN `SafeBodyUnit` — already produced
    carrier-free by `seqChild_safeBodyUnit` (the seq oracle drawing its interior `RecSeqBody` from the
    `windowWidth_strongRecOn` IH) — via `seqSeparatorFacts_of_windowed_safebodyunit` (R299), and the
    child's `FlowBodyContentDeep` is the parent's restricted (`flowBodyContentDeep_descend`).
    `flowBodyContent_of_deep` then assembles the child `FlowBodyContent`.  So the descend edge IS a
    theorem — it just consumes the IH (it is genuinely recursive, unlike the pure-rebasing advance edge),
    exactly the [[ref-converse-forward-invariant-asymmetry]] split the deep content guard already
    exhibited.

    This is what lets the `RecSeqBody` producer thread `FlowBodyContent` through its guard `G`
    (root-seeded from emission via `seqRoot_safeBodyUnit`, propagated by THIS edge at descend and
    `flowBodyContent_advance` at advance) INSTEAD of the ambient carrier — breaking the carrier↔producer
    circularity ([[ref-recursive-producer-mirrors-flat-over-shared-induction]] consume-side dual).
    Verified-but-unconsumed until the carrier-free producer is rewired (R225): composes only landed
    lemmas, references no sorry site, frontier sorry count unchanged. -/
theorem flowBodyContent_descend (tokens : Array (Positioned YamlToken)) (p hi j : Nat)
    (h_window : FlowBodyWindow tokens p hi)
    (h_deep : FlowBodyContentDeep tokens p hi)
    (h_content : FlowBodyContent tokens p hi)
    (h_open : tokens[p]!.val = .flowSequenceStart)
    (Q : Nat → Prop) (h_q_succ : Q (p + 1))
    (h_ih : ∀ lo' hi', hi' - lo' < hi - p → p ≤ lo' → hi' ≤ hi →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' → Q lo' →
        tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo'))
    (h_pj : p < j) (h_jhi : j < hi) (h_jclose : tokens[j]!.val = .flowSequenceEnd)
    (h_inner : flowBracketBalance tokens (p + 1) j = 0)
    (h_floor : ∀ i, p < i → i ≤ j → flowBracketBalance tokens p i ≥ 1) :
    FlowBodyContent tokens (p + 1) j := by
  -- Opener delta and interior non-emptiness `p + 1 < j` (the child head is content, the close is not).
  have h_hi_sz : hi < tokens.size := h_window.hi_lt
  have h_open_delta : flowBracketDelta tokens[p]!.val = 1 := by
    rw [h_open]; exact flowBracketDelta_flowSequenceStart
  have h_p1_hi : p + 1 < hi := by omega
  have h_head_cs : isFlowContentStart tokens[p + 1]!.val :=
    h_deep.openerContentStart p (Nat.le_refl p) h_p1_hi h_open_delta
  have h_p1_ne : tokens[p + 1]!.val ≠ .flowSequenceEnd := by
    intro h; rw [h] at h_head_cs; simp [isFlowContentStart] at h_head_cs
  have h_p1_j : p + 1 < j := by
    rcases Nat.lt_or_ge (p + 1) j with h | h
    · exact h
    · exfalso; have h_eq : j = p + 1 := by omega
      rw [h_eq] at h_jclose; exact h_p1_ne h_jclose
  -- The child `SafeBodyUnit` (carrier-free, from the seq oracle's IH) gives both separator facts.
  have h_safe : SafeBodyUnit ContentStartTok ((tokens.toList.take j).drop (p + 1)) :=
    seqChild_safeBodyUnit tokens p hi j h_window h_deep h_content h_open Q h_q_succ h_ih
      h_pj h_jhi h_jclose h_inner h_floor
  obtain ⟨h_bs, h_nts⟩ :=
    seqSeparatorFacts_of_windowed_safebodyunit tokens (p + 1) j
      (Nat.le_of_lt (by omega : j < tokens.size)) h_safe
  -- The child `FlowBodyContentDeep` is the parent's restricted to `[p+1, j)`.
  have h_deep' : FlowBodyContentDeep tokens (p + 1) j :=
    flowBodyContentDeep_descend tokens p p j hi h_deep (Nat.le_refl p) h_open_delta h_p1_j
      (Nat.le_of_lt h_jhi)
  exact flowBodyContent_of_deep tokens (p + 1) j h_deep' h_bs h_nts

/-- **The DESCEND edge for `FlowBodyContent`, `FlowBodyContentDeepSeq`-keyed** —
    `(i'-b-B2b-desc-merge-seq)`, R500: the `_seq` twin of `flowBodyContent_descend` (above), threading
    `FlowBodyContent` as a CARRIER-FREE `G`-conjunct down the descend edge over the root-TRUE weak guard
    ([[ref-rethread-stays-in-weaker-twin-family]], [[ref-root-seed-needs-root-true-guard]]).  At a
    descended seq window `[p+1, j)` it produces the child `FlowBodyContent` from (i) the child's own
    carrier-free `SafeBodyUnit` (R494 `seqChild_safeBodyUnit_seq`, the seq oracle drawing its interior
    `RecSeqBody` from the `windowWidth_strongRecOn` IH) and (ii) the child's `FlowBodyContentDeepSeq`
    (`flowBodyContentDeepSeq_descend`), assembled by the UNIFIED `flowBodyContent_of_deepSeq` (R393).
    Two `_seq`-family differences from the strong twin, exactly as predicted:

    * **`h_ne` is FORWARDED, not derived.**  The strong twin reads interior non-emptiness
      `tokens[p+1] ≠ .flowSequenceEnd` off `FlowBodyContentDeep.openerContentStart` (the all-depth field).
      The weak guard's same field is non-emptiness-gated and cannot self-derive it
      ([[ref-window-absolute-gate-subset-restriction]]), so `h_ne` is a forwarded hypothesis
      ([[ref-lift-forwards-dropped-derivation-premise]]) — passed straight to `seqChild_safeBodyUnit_seq`
      and `flowBodyContentDeepSeq_descend`, and used locally to refute the empty close `j = p+1`.
    * **The assembler UNIFIES** where the strong one SPLIT.  `flowBodyContent_of_deepSeq` demands one
      `h_feContent` over EVERY interior `k < j` (the weak `feContentStart` is `≠ .key`-gated, unprojectable
      at the descend site, [[ref-unified-residual-routes-through-one-invariant]]).

    **The R499 prediction OVER-FIRED: the unit projection alone serves the unified residual.**  R499 read
    the unification and predicted a SECOND, fuller projection of the child `RecSeqBody`
    (`seqChild_safeBody_seq`, `.toSafeBody`) was FORCED, reasoning that `SafeBody_array_flowEntry_window`
    delivers the interior `feContentStart` only off the full `SafeBody`.  Building the edge refutes that:
    the unified `h_feContent` splits into INTERIOR (`k+1 < j`) and BOUNDARY (`k+1 = j`), and BOTH come from
    the ONE windowed `SafeBodyUnit` via the EXISTING `seqEnclosingFacts_of_windowed_safebodyunit` —
    interior through `seqInteriorFeContentStart_of_windowed_safebodyunit`, which already COERCES
    `SafeBodyUnit → SafeBody` internally (`SafeBodyUnit_safeBody ContentStartTok_ne_flowEntry`) before
    calling `SafeBody_array_flowEntry_window`, and boundary through `noTrailingSepFact` VACUOUSLY.  So the
    "fuller projection" R499 thought was forced is recovered from the unit projection by a head-conditioned
    COERCION already packaged in the consumer — a *forced second projection dissolves when the weaker
    projection coerces to the fuller one* ([[ref-coercion-dissolves-forced-projection]]).  R499's
    minimal-pair demo (`unitProj [true,false]` holds, `GoalAll` fails) modeled the WRONG regime: its
    abstract `unitProj` was deliberately NON-coercible to `fullProj`, whereas the real `SafeBodyUnit` IS
    coercible to `SafeBody` given the `ContentStartTok` head.  `seqChild_safeBody_seq` (R499) therefore
    stays a valid verified-but-unconsumed sibling, but is NOT on this edge's critical path.

    Consumes only landed lemmas (R494 + the windowed-`SafeBodyUnit` enclosing-facts bundle + the R393
    assembler + `flowBodyContentDeepSeq_descend`); references no sorry site, frontier sorry count unchanged
    at 4; axiom-clean.  Threaded alongside the `_seq` root seed and advance edge, this is the descend half
    of the carrier-free `FlowBodyContent` `G`-conjunct the JOINT `windowWidth_strongRecOn` co-construction
    consumes ([[ref-recursive-producer-mirrors-flat-over-shared-induction]] consume-side dual). -/
theorem flowBodyContent_descend_seq (tokens : Array (Positioned YamlToken)) (p hi j : Nat)
    (h_window : FlowBodyWindow tokens p hi)
    (h_deep : FlowBodyContentDeepSeq tokens p hi)
    (h_content : FlowBodyContent tokens p hi)
    (h_open : tokens[p]!.val = .flowSequenceStart)
    (h_ne : tokens[p + 1]!.val ≠ .flowSequenceEnd)
    (Q : Nat → Prop) (h_q_succ : Q (p + 1))
    (h_ih : ∀ lo' hi', hi' - lo' < hi - p → p ≤ lo' → hi' ≤ hi →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeepSeq tokens lo' hi' → Q lo' →
        tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo'))
    (h_pj : p < j) (h_jhi : j < hi) (h_jclose : tokens[j]!.val = .flowSequenceEnd)
    (h_inner : flowBracketBalance tokens (p + 1) j = 0)
    (h_floor : ∀ i, p < i → i ≤ j → flowBracketBalance tokens p i ≥ 1) :
    FlowBodyContent tokens (p + 1) j := by
  have h_hi_sz : hi < tokens.size := h_window.hi_lt
  -- Interior non-emptiness `p + 1 < j` from the SUPPLIED `h_ne` (the weak guard can't self-derive it).
  have h_p1_j : p + 1 < j := by
    rcases Nat.lt_or_ge (p + 1) j with h | h
    · exact h
    · exfalso; have h_eq : j = p + 1 := by omega
      rw [h_eq] at h_jclose; exact h_ne h_jclose
  -- The child `SafeBodyUnit` (carrier-free, from the seq oracle's IH — R494 unit projection).
  have h_safe : SafeBodyUnit ContentStartTok ((tokens.toList.take j).drop (p + 1)) :=
    seqChild_safeBodyUnit_seq tokens p hi j h_window h_deep h_content h_open h_ne Q h_q_succ h_ih
      h_pj h_jhi h_jclose h_inner h_floor
  -- The THREE enclosing facts from the ONE windowed `SafeBodyUnit`: `bodySucc`, the INTERIOR
  -- `feContentStart` (`SafeBodyUnit → SafeBody` coerced internally), and `noTrailingSep`.
  obtain ⟨h_bs, h_fe_int, h_nts⟩ :=
    seqEnclosingFacts_of_windowed_safebodyunit tokens (p + 1) j
      (Nat.le_of_lt (by omega : j < tokens.size)) h_safe
  -- The child `FlowBodyContentDeepSeq` (the parent's restricted to `[p+1, j)`), fed the forwarded `h_ne`.
  have h_deep' : FlowBodyContentDeepSeq tokens (p + 1) j :=
    flowBodyContentDeepSeq_descend tokens p p j hi h_deep (Nat.le_refl p) h_open h_ne h_p1_j
      (Nat.le_of_lt h_jhi)
  -- Assemble via the UNIFIED `_seq` assembler.  `h_feContent` = INTERIOR (`k+1<j`) ∪ BOUNDARY (`k+1=j`):
  -- the unit projection serves BOTH, so R499's `.toSafeBody` second projection is not needed here.
  refine flowBodyContent_of_deepSeq tokens (p + 1) j h_deep' h_bs ?_
  intro k hk1 hk2 hfe hbal
  rcases Nat.lt_or_ge (k + 1) j with h | h
  · exact h_fe_int k hk1 h hfe hbal
  · exact h_nts k hk1 (by omega) hfe hbal

/-- **The descent `provider` at a located enclosing seq** — `(i'-b-descent-assembly)`, brick (5), the
    LAST seq residual of the R303 direct-discharge route.  At a NESTED gated window `[a, b)` (the root
    discriminator `flowBracketBalance tokens lo a = 0` FAILS, so the root seed
    `seqEnclosingFacts_provider_root` does not apply), produce the provider existential
    `∃ loS hiS, …` that `seqInteriorSeparators_of_enclosing_provider` consumes, by CHAINING the landed
    descent bricks.

    Per [[ref-parametric-assembler-extraction]] this is the ASSEMBLE half of the descent's locate
    boundary: it LIFTS the facts the recursion driver supplies — the located enclosing opener `p` with
    its locator output (`flowBracketDelta tokens[p]! = 1`, `balance (p+1) a = 0`, the locator floor
    over `(p, a]`), and the enclosing recursion window `[p, hi)` as a
    `FlowBodyWindow`/`FlowBodyContentDeep`/`FlowBodyContent` with the width-recursion IH — and
    discharges the existential with NO locate analysis.  The residual it isolates is exactly the
    recursion driver (`windowWidth_strongRecOn`): SOURCE `p` (the backward enclosing-opener scan made
    invokable by `flowBracketBalance_pos_of_seqTypedInterior`) and the `[p, hi)` window facts + IH,
    reaching `p` by advancing/descending until it is the current window's head.

    The chain (all pieces landed):

    1. `seqOpenerType_of_located_and_gate` — the gate's `btFold`-top `= some true` plus the locator
       floor pin `tokens[p]` to `.flowSequenceStart`;
    2. `flowBracketBalance_matching_close` (the GENERIC locator, at `lo = k = p` over `[p, hi)`) —
       returns `j` with `j < hi`, `balance (p+1) j = 0`, and crucially the interior floor
       `∀ i ∈ (p, j], balance p i ≥ 1` that `seqChild_safeBodyUnit` needs (brick (3)'s seq-specialized
       locator DROPS it — [[ref-downstream-derisk-restores-upstream]], so the descent re-runs the
       generic primitive rather than reusing `seqClose_of_located_and_enclosing`);
    3. `matching_close_typed_core` + `btStep_pop_eq_seqEnd` — the typed close
       `tokens[j]! = .flowSequenceEnd` (the opener pushes `[true]`, the matching close pops it);
    4. the two containment bounds `a ≤ j`, `b ≤ j` — the [[ref-two-floor-relay-close-bound]] relay:
       one underflow witness at `j + 1`, refuted by the locator floor (for `a`) then the gate floor
       (for `b`);
    5. `seqChild_safeBodyUnit` — the windowed `SafeBodyUnit ContentStartTok` of the genuine seq body
       `[p+1, j)`;
    6. `seqEnclosingFacts_provider_of_located` — the existential, `loS = p+1`, `hiS = j`.

    **De-risk (`#guard`-backed, `Tests/Guards/Proofs/SeqDescentProviderProbe.lean`)** per
    [[ref-probe-provider-satisfiable-before-assembler]]: the lifted hypotheses are satisfiable at
    nested gated windows on two witnesses exercising the residual driver's two reach modes —
    `[[1, 2], 9]` (DESCEND-AT-ROOT: `p = 2` IS the outer body head) and `[1, [2, 3]]`
    (ADVANCE-THEN-DESCEND: `p = 4` is reached only after advancing past the first entry).  So the
    assembler is not vacuous and the residual genuinely needs both recursion edges. -/
theorem seqDescent_provider_of_located
    (tokens : Array (Positioned YamlToken)) (a b p hi : Nat)
    (h_pa : p < a) (h_ab : a ≤ b) (h_b_hi : b ≤ hi)
    (h_delta : flowBracketDelta tokens[p]!.val = 1)
    (h_body_bal : flowBracketBalance tokens (p + 1) a = 0)
    (h_loc_floor : ∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0)
    (h_gate : SeqTypedInterior tokens a b)
    (h_window : FlowBodyWindow tokens p hi)
    (h_deep : FlowBodyContentDeep tokens p hi)
    (h_content : FlowBodyContent tokens p hi)
    (Q : Nat → Prop) (h_q_succ : Q (p + 1))
    (h_ih : ∀ lo' hi', hi' - lo' < hi - p → p ≤ lo' → hi' ≤ hi →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' → Q lo' →
        tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo')) :
    ∃ loS hiS, loS ≤ a ∧ b ≤ hiS ∧ flowBracketBalance tokens loS a = 0 ∧
      bodySuccFact tokens loS hiS ∧
      (∀ k, loS ≤ k → k + 1 < hiS →
        tokens[k]!.val = .flowEntry → flowBracketBalance tokens loS k = 0 →
        isFlowContentStart tokens[k + 1]!.val) ∧
      noTrailingSepFact tokens loS hiS := by
  -- Window projections (the parent recursion's well-bracketedness).
  have h_p_hi : p < hi := h_window.lo_lt_hi
  have h_hi_sz : hi ≤ tokens.size := Nat.le_of_lt h_window.hi_lt
  have h_total : flowBracketBalance tokens p hi = 0 := h_window.balanced
  have h_dyck : ∀ i, p ≤ i → i ≤ hi → flowBracketBalance tokens p i ≥ 0 := h_window.dyck
  have h_wt : WellTyped ((tokens.toList.take hi).drop p) := h_window.wellTyped
  have h_a_sz : a ≤ tokens.size := Nat.le_trans (Nat.le_trans h_ab h_b_hi) h_hi_sz
  -- (1) the located opener is a `.flowSequenceStart` (from the gate's mark + the locator floor).
  have h_open : tokens[p]!.val = .flowSequenceStart :=
    seqOpenerType_of_located_and_gate tokens a p h_pa h_a_sz h_delta h_body_bal h_loc_floor h_gate.2.1
  -- (2) the GENERIC matching-close at `p` over `[p, hi)` — KEEPS the interior floor `≥ 1`.
  have h_pp : flowBracketBalance tokens p p = 0 := by simp [flowBracketBalance]
  obtain ⟨j, h_pj, h_jhi, h_jdelta, h_inner, h_pos⟩ :=
    flowBracketBalance_matching_close tokens p p hi (Nat.le_refl p) h_p_hi h_hi_sz
      h_pp h_delta h_total h_dyck
  -- (3) the typed close `tokens[j]! = .flowSequenceEnd` (opener pushes `[true]`, close pops it).
  have h_k_push : btStep tokens[p]! [] = some [true] := by unfold btStep; rw [h_open]
  have h_jclose : tokens[j]!.val = .flowSequenceEnd :=
    btStep_pop_eq_seqEnd _ (matching_close_typed_core tokens p p j hi true (Nat.le_refl p)
      h_pj h_jhi h_hi_sz h_pp h_k_push h_inner h_jdelta h_pos h_wt)
  -- (4) the containment bounds `a ≤ j`, `b ≤ j` — the two-floor relay at `j + 1`.
  have step : ∀ base, base ≤ j →
      flowBracketBalance tokens base (j + 1)
        = flowBracketBalance tokens base j + flowBracketDelta tokens[j]!.val := by
    intro base hbase
    have h_j_sz : j < tokens.size := by omega
    have hlen : j < tokens.toList.length := by rw [Array.length_toList]; exact h_j_sz
    rw [flowBracketBalance_compose tokens base j (j + 1) hbase (by omega),
        flowBracketBalance_single tokens j hlen]
    have h1 : tokens.toList[j]'hlen = tokens[j] := Array.getElem_toList h_j_sz
    have h2 : tokens[j] = tokens[j]! := (getElem!_pos tokens j h_j_sz).symm
    rw [h1, h2]
  have h_a_j : a ≤ j := by
    rcases Nat.lt_or_ge j a with h | h
    · have h_floor := h_loc_floor (j + 1) (by omega) (by omega)
      rw [step (p + 1) (by omega), h_inner, h_jdelta] at h_floor
      omega
    · exact h
  have h_aj_bal : flowBracketBalance tokens a j = 0 := by
    have hc := flowBracketBalance_compose tokens (p + 1) a j (by omega) h_a_j
    rw [h_inner, h_body_bal] at hc; omega
  have h_b_j : b ≤ j := by
    rcases Nat.lt_or_ge j b with h | h
    · have h_floor := h_gate.2.2 (j + 1) (by omega) (by omega)
      rw [step a h_a_j, h_aj_bal, h_jdelta] at h_floor
      omega
    · exact h
  -- (5) the child `SafeBodyUnit` at the located genuine seq body `[p+1, j)`.
  have h_safe : SafeBodyUnit ContentStartTok ((tokens.toList.take j).drop (p + 1)) :=
    seqChild_safeBodyUnit tokens p hi j h_window h_deep h_content h_open Q h_q_succ h_ih
      h_pj h_jhi h_jclose h_inner h_pos
  -- (6) assemble the provider existential (`loS = p+1`, `hiS = j`).
  exact seqEnclosingFacts_provider_of_located tokens a b (p + 1) j
    (by omega) h_b_j (by omega) h_body_bal h_safe

/-- **The descent provider, `FlowBodyContentDeepSeq`-keyed** — `(i'-b-B2c-desc-assembly-seq)`, R495:
    the `_seq`-family twin of `seqDescent_provider_of_located` (above), the next consumer-chain link of
    the `_seq` re-thread ([[ref-rethread-stays-in-weaker-twin-family]]) above the leaf lift
    `seqChild_safeBodyUnit_seq` (R494).  It transports `h_deep : FlowBodyContentDeepSeq tokens p hi`
    straight to the child lift — the ENTIRE preamble (window projections, located opener type, generic
    matching close `j`, typed close, the two-floor relay `a ≤ j`, `b ≤ j`) reads NO deep field, so it is
    character-identical to the strong parent ([[ref-transporting-lemma-twin-zero-body-edits]]).

    **The climbing dropped-derivation premise (R494) terminates here at a CASE SPLIT, not a discharge.**
    [[ref-dropped-derivation-premise-climbs-lift-chain]] (R494) showed the leaf twin
    `recseqentry_seqbracket_oracle_seq` takes interior non-emptiness `h_ne` as a SUPPLIED premise (the
    strong `FlowBodyContentDeep.openerContentStart` self-derived it; the weaker
    `FlowBodyContentDeepSeq.openerContentStart` is GUARDED by it), and that `seqChild_safeBodyUnit_seq`
    FORWARDS it.  The climbing premise was predicted to be SOURCED by this ancestor.  It is — but the
    actual structure is richer: because the weaker guard ADMITS the degenerate input the strong guard's
    unconditional field excluded (an empty enclosing seq `[ … [] … ]`, where the inner empty seq's gated
    window `[p+1, p+1)` has `j = p+1` and `tokens[p+1]! = .flowSequenceEnd` ⇒ `h_ne` is FALSE), that
    input reaches THIS ancestor too (the dispatcher hands `desc` windows with `a ≤ b`, NOT `a < b`).  So
    the premise cannot be sourced UNCONDITIONALLY; it terminates at a CASE SPLIT on the discriminator the
    strong guard had ENCODED — `p + 1 < j` (the enclosing seq is non-empty):

    * `p + 1 < j` — NON-EMPTY enclosing seq.  SOURCE `h_ne` from the interior floor `h_pos`: if
      `tokens[p+1]! = .flowSequenceEnd` then `balance p (p+2) = 1 + (-1) = 0`, contradicting the
      matched-bracket floor `balance p (p+2) ≥ 1` (valid since `p+2 ≤ j`).  Then the body is genuine and
      the leaf twin `seqChild_safeBodyUnit_seq` produces the child `SafeBodyUnit`; assemble as the strong
      parent does.  Cost over the strong call = ONE guard-keyed name swap
      (`seqChild_safeBodyUnit ↦ _seq`) + the SOURCED `h_ne`.
    * `¬ (p + 1 < j)` (so `j = p+1`) — EMPTY enclosing seq.  The gated window collapses to `a = b = p+1`
      (`p < a ≤ b ≤ j = p+1`); both separator facts are VACUOUS, so produce the existential `⟨p+1, p+1, …⟩`
      DIRECTLY — `flowBracketBalance loS a = 0` is `h_body_bal` verbatim, the body/no-trailing/entry facts
      close by `omega` on contradictory bounds.  The leaf oracle is BYPASSED — it could not be fed here
      (`h_ne` is false), which is exactly why the premise had to climb.

    So the dropped-derivation premise's terminus is the first ancestor that can DISTINGUISH the degenerate
    case, and distinguishing means HANDLING BOTH branches (source-in-non-degenerate + vacuous-in-degenerate),
    not a single discharge.  This sharpens [[ref-dropped-derivation-premise-climbs-lift-chain]]:
    `cost(terminating ancestor) = #(guard-keyed child names) + (source the premise on the re-discovered
    discriminator) + (produce the deliverable vacuously on the degenerate branch the weaker guard admits)`.

    Verified-but-unconsumed until `seqLocalCarrier_of_widthEnc_seq` (next) consumes it: composes only
    landed lemmas (the R494 child lift twin), references no sorry site, frontier sorry count unchanged at 4. -/
theorem seqDescent_provider_of_located_seq
    (tokens : Array (Positioned YamlToken)) (a b p hi : Nat)
    (h_pa : p < a) (h_ab : a ≤ b) (h_b_hi : b ≤ hi)
    (h_delta : flowBracketDelta tokens[p]!.val = 1)
    (h_body_bal : flowBracketBalance tokens (p + 1) a = 0)
    (h_loc_floor : ∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0)
    (h_gate : SeqTypedInterior tokens a b)
    (h_window : FlowBodyWindow tokens p hi)
    (h_deep : FlowBodyContentDeepSeq tokens p hi)
    (h_content : FlowBodyContent tokens p hi)
    (Q : Nat → Prop) (h_q_succ : Q (p + 1))
    (h_ih : ∀ lo' hi', hi' - lo' < hi - p → p ≤ lo' → hi' ≤ hi →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeepSeq tokens lo' hi' → Q lo' →
        tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo')) :
    ∃ loS hiS, loS ≤ a ∧ b ≤ hiS ∧ flowBracketBalance tokens loS a = 0 ∧
      bodySuccFact tokens loS hiS ∧
      (∀ k, loS ≤ k → k + 1 < hiS →
        tokens[k]!.val = .flowEntry → flowBracketBalance tokens loS k = 0 →
        isFlowContentStart tokens[k + 1]!.val) ∧
      noTrailingSepFact tokens loS hiS := by
  -- Window projections (the parent recursion's well-bracketedness) — identical to the strong parent.
  have h_p_hi : p < hi := h_window.lo_lt_hi
  have h_hi_sz : hi ≤ tokens.size := Nat.le_of_lt h_window.hi_lt
  have h_total : flowBracketBalance tokens p hi = 0 := h_window.balanced
  have h_dyck : ∀ i, p ≤ i → i ≤ hi → flowBracketBalance tokens p i ≥ 0 := h_window.dyck
  have h_wt : WellTyped ((tokens.toList.take hi).drop p) := h_window.wellTyped
  have h_a_sz : a ≤ tokens.size := Nat.le_trans (Nat.le_trans h_ab h_b_hi) h_hi_sz
  -- (1) the located opener is a `.flowSequenceStart` (from the gate's mark + the locator floor).
  have h_open : tokens[p]!.val = .flowSequenceStart :=
    seqOpenerType_of_located_and_gate tokens a p h_pa h_a_sz h_delta h_body_bal h_loc_floor h_gate.2.1
  -- (2) the GENERIC matching-close at `p` over `[p, hi)` — KEEPS the interior floor `≥ 1`.
  have h_pp : flowBracketBalance tokens p p = 0 := by simp [flowBracketBalance]
  obtain ⟨j, h_pj, h_jhi, h_jdelta, h_inner, h_pos⟩ :=
    flowBracketBalance_matching_close tokens p p hi (Nat.le_refl p) h_p_hi h_hi_sz
      h_pp h_delta h_total h_dyck
  -- (3) the typed close `tokens[j]! = .flowSequenceEnd`.
  have h_k_push : btStep tokens[p]! [] = some [true] := by unfold btStep; rw [h_open]
  have h_jclose : tokens[j]!.val = .flowSequenceEnd :=
    btStep_pop_eq_seqEnd _ (matching_close_typed_core tokens p p j hi true (Nat.le_refl p)
      h_pj h_jhi h_hi_sz h_pp h_k_push h_inner h_jdelta h_pos h_wt)
  -- (4) the containment bounds `a ≤ j`, `b ≤ j` — the two-floor relay at `j + 1`.
  have step : ∀ base, base ≤ j →
      flowBracketBalance tokens base (j + 1)
        = flowBracketBalance tokens base j + flowBracketDelta tokens[j]!.val := by
    intro base hbase
    have h_j_sz : j < tokens.size := by omega
    have hlen : j < tokens.toList.length := by rw [Array.length_toList]; exact h_j_sz
    rw [flowBracketBalance_compose tokens base j (j + 1) hbase (by omega),
        flowBracketBalance_single tokens j hlen]
    have h1 : tokens.toList[j]'hlen = tokens[j] := Array.getElem_toList h_j_sz
    have h2 : tokens[j] = tokens[j]! := (getElem!_pos tokens j h_j_sz).symm
    rw [h1, h2]
  have h_a_j : a ≤ j := by
    rcases Nat.lt_or_ge j a with h | h
    · have h_floor := h_loc_floor (j + 1) (by omega) (by omega)
      rw [step (p + 1) (by omega), h_inner, h_jdelta] at h_floor
      omega
    · exact h
  have h_aj_bal : flowBracketBalance tokens a j = 0 := by
    have hc := flowBracketBalance_compose tokens (p + 1) a j (by omega) h_a_j
    rw [h_inner, h_body_bal] at hc; omega
  have h_b_j : b ≤ j := by
    rcases Nat.lt_or_ge j b with h | h
    · have h_floor := h_gate.2.2 (j + 1) (by omega) (by omega)
      rw [step a h_a_j, h_aj_bal, h_jdelta] at h_floor
      omega
    · exact h
  -- A single-position balance helper (mirrors `step`, at an arbitrary in-bounds position).
  have one_step : ∀ pos, pos < tokens.size →
      flowBracketBalance tokens pos (pos + 1) = flowBracketDelta tokens[pos]!.val := by
    intro pos h_pos_sz
    have hlen : pos < tokens.toList.length := by rw [Array.length_toList]; exact h_pos_sz
    rw [flowBracketBalance_single tokens pos hlen]
    have h1 : tokens.toList[pos]'hlen = tokens[pos] := Array.getElem_toList h_pos_sz
    have h2 : tokens[pos] = tokens[pos]! := (getElem!_pos tokens pos h_pos_sz).symm
    rw [h1, h2]
  -- CASE SPLIT on `p + 1 < j` (the discriminator the strong `FlowBodyContentDeep` encoded; the weaker
  -- `FlowBodyContentDeepSeq` admits the EMPTY enclosing seq `j = p+1`, so the climbing `h_ne` premise
  -- terminates here at a case split, not an unconditional discharge — R495).
  by_cases h_pj1 : p + 1 < j
  · -- NON-EMPTY enclosing seq: SOURCE the dropped-derivation premise `h_ne` from the interior floor.
    have h_ne : tokens[p + 1]!.val ≠ .flowSequenceEnd := by
      intro h_end
      have h_floor2 := h_pos (p + 2) (by omega) (by omega)
      have e_comp := flowBracketBalance_compose tokens p (p + 1) (p + 2) (by omega) (by omega)
      have e0 := one_step p (by omega)
      have e1 := one_step (p + 1) (by omega)
      rw [e0, h_delta] at e_comp
      rw [e1, h_end, flowBracketDelta_flowSequenceEnd] at e_comp
      omega
    -- the child `SafeBodyUnit` at the located genuine seq body `[p+1, j)` (the R494 `_seq` oracle twin).
    have h_safe : SafeBodyUnit ContentStartTok ((tokens.toList.take j).drop (p + 1)) :=
      seqChild_safeBodyUnit_seq tokens p hi j h_window h_deep h_content h_open h_ne
        Q h_q_succ h_ih h_pj h_jhi h_jclose h_inner h_pos
    exact seqEnclosingFacts_provider_of_located tokens a b (p + 1) j
      (by omega) h_b_j (by omega) h_body_bal h_safe
  · -- EMPTY enclosing seq (`j = p+1`): the gated window collapses to `a = b = p+1`; both separator
    -- facts are VACUOUS, produced directly (`balance loS a = 0` is `h_body_bal`), BYPASSING the leaf.
    refine ⟨p + 1, p + 1, by omega, by omega, h_body_bal, ?_, ?_, ?_⟩
    · intro k hk1 hk2 _ _; omega
    · intro k hk1 hk2 _ _; omega
    · intro k hk1 hk2 _ _; omega

/-- **The descent provider WITH the locator internalized** — `(i'-b-B2c-desc-fold)`, the FROM-LOCATED
    fold that turns the `desc` driver's residual into the `windowWidth_strongRecOn` fixpoint's exact
    contract ([[ref-from-located-assembler-direction]]: factor the descent's locate boundary at the
    producer side; the locator is the LANDED half, this fold lifts the enclosing-facts/IH supplier as
    the sole hypothesis).

    `seqDescent_provider_of_located` (the ASSEMBLE) consumes a located opener `p` PLUS the enclosing
    recursion window `[p, hi)`'s facts (`FlowBodyWindow`/`FlowBodyContentDeep`/`FlowBodyContent`) and
    the width-recursion IH.  The locator half — recovering `p` with its four facts from the gate — is
    already in hand (`seqEnclosingOpener_of_gate`, R319/B2a, made invokable by
    `flowBracketBalance_pos_of_seqTypedInterior`).  This fold composes the two: it `obtain`s `p` from
    the locator, then hands `p` + the locator's output to the supplier hypothesis `h_enc`, then calls
    the assembler.  The result is the `desc` shape verbatim
    (`seqInteriorSeparators_of_safebody_and_descent` / `seqRoot_seqInteriorSeparators` consume it).

    **`h_enc` is the fixpoint's contract** ([[ref-fold-consumer-chain-to-producer-contract]]).  It is a
    PRODUCER-GUARDED universal `∀ p, (locator guards) → (enclosing facts ∧ IH)` whose four guards —
    `p < a`, `flowBracketDelta tokens[p]! = 1`, `flowBracketBalance (p+1) a = 0`, the locator floor —
    are EXACTLY `seqEnclosingOpener_of_gate`'s output, so the instantiation is immediate and the
    guard carries the producer's own constraint ([[ref-producer-guarded-quantifier]]: the positive
    case — a deferred ∀-premise over an internally-produced witness is dischargeable precisely because
    its guard mirrors the producer's).  What remains is to DISCHARGE `h_enc`: supply, for the located
    enclosing opener `p`, the window `[p, hi)`'s `FlowBodyWindow`/`Deep`/`Content` and the
    `RecSeqBody`-producing IH — i.e. the `windowWidth_strongRecOn` fixpoint (R318/R340's
    carrier↔recursion co-construction), the single remaining seq residual.  This fold is carrier-FREE
    (it never touches `h_root_carrier`); the carrier-circularity caution applies to the fixpoint's own
    `FlowBodyContent` source, not here.

    The descent IH's per-window predicate `Q` (which the fixpoint instantiates at `SeqEnclosed` — the
    seq-enclosure guard defined below) is kept PARAMETRIC here, mirroring `seqDescent_provider_of_located`
    / `seqChild_safeBodyUnit`'s `Q`-parametric IH interface (R322) and side-stepping the forward
    reference to `SeqEnclosed`'s `def`.

    **De-risk** ([[ref-probe-provider-satisfiable-before-assembler]]): `h_enc`'s body is exactly the
    `#guard`-backed satisfiable hypothesis bundle of `seqDescent_provider_of_located`
    (`SeqDescentProviderProbe` on `[[1, 2], 9]` / `[1, [2, 3]]`, both reach modes), so the lifted
    hypothesis is not vacuous. -/
theorem seqDescent_provider_of_gate
    (tokens : Array (Positioned YamlToken)) (a b hi : Nat)
    (h_ab : a ≤ b) (h_b_hi : b ≤ hi) (h_hi_sz : hi ≤ tokens.size)
    (h_gate : SeqTypedInterior tokens a b)
    (Q : Nat → Prop)
    (h_enc : ∀ p, p < a → flowBracketDelta tokens[p]!.val = 1 →
        flowBracketBalance tokens (p + 1) a = 0 →
        (∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) →
        FlowBodyWindow tokens p hi ∧ FlowBodyContentDeep tokens p hi ∧
        FlowBodyContent tokens p hi ∧ Q (p + 1) ∧
        (∀ lo' hi', hi' - lo' < hi - p → p ≤ lo' → hi' ≤ hi →
          FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' →
          Q lo' → tokens[hi']!.val = .flowSequenceEnd →
          RecSeqBody ((tokens.toList.take hi').drop lo'))) :
    ∃ loS hiS, loS ≤ a ∧ b ≤ hiS ∧ flowBracketBalance tokens loS a = 0 ∧
      bodySuccFact tokens loS hiS ∧
      (∀ k, loS ≤ k → k + 1 < hiS →
        tokens[k]!.val = .flowEntry → flowBracketBalance tokens loS k = 0 →
        isFlowContentStart tokens[k + 1]!.val) ∧
      noTrailingSepFact tokens loS hiS := by
  have h_a_sz : a ≤ tokens.size := Nat.le_trans (Nat.le_trans h_ab h_b_hi) h_hi_sz
  obtain ⟨p, h_pa, h_delta, h_body_bal, h_loc_floor⟩ :=
    seqEnclosingOpener_of_gate tokens a b h_a_sz h_gate
  obtain ⟨h_window, h_deep, h_content, h_q_succ, h_ih⟩ :=
    h_enc p h_pa h_delta h_body_bal h_loc_floor
  exact seqDescent_provider_of_located tokens a b p hi h_pa h_ab h_b_hi h_delta h_body_bal
    h_loc_floor h_gate h_window h_deep h_content Q h_q_succ h_ih

/-- **The gate's stack-top conjunct is RECONSTRUCTIBLE in place** — the Q2 discharge for
    `(i'-b-descend-root)`.  `SeqTypedInterior`'s second conjunct
    (`(btFold (some []) (tokens.toList.take a)).bind (·.head?) = some true`) is a fact about the
    PREFIX `[0,a)`, NOT about the window interior `[a,b)` — so it is NOT a projection of
    `FlowBodyWindow` (whose `wellTyped` field only sees the interior).  But it reconstructs from two
    boundary facts the recursion already supplies at every seq window:

    * the **opener** just before the body is a `.flowSequenceStart` (`tokens[q]` with `q = a - 1` —
      the seq oracle's `h_open : tokens[lo]!.val = .flowSequenceStart`, and the root window's outer `[`);
    * the **pre-opener prefix folds to some typed stack** `s` (from the global `WellTyped` of the
      concrete output via `WellTyped_prefix_some` — `btFold` of any prefix of a `WellTyped` list is
      `some`).

    A `.flowSequenceStart` pushes `true` (`btStep … = some (true :: s)`), so the stack top after the
    opener is `true`.  This is a [[ref-reconstruct-in-place-over-relocate]] discharge: the gate is
    reconstructed AT the window from its own boundary, not threaded as a second universal — and the
    two hypotheses below ARE the precise facts the root seed must thread per seq window. -/
theorem enclosingMark_true_of_opener
    (tokens : Array (Positioned YamlToken)) (q : Nat) (h_q : q < tokens.size)
    (s : List Bool) (h_pre : btFold (some []) (tokens.toList.take q) = some s)
    (h_open : tokens[q]!.val = .flowSequenceStart) :
    (btFold (some []) (tokens.toList.take (q + 1))).bind (·.head?) = some true := by
  have h_q' : q < tokens.toList.length := by rwa [Array.length_toList]
  have h_split : tokens.toList.take (q + 1)
      = tokens.toList.take q ++ [tokens.toList[q]'h_q'] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h_q']; rfl
  have h_val : (tokens.toList[q]'h_q').val = .flowSequenceStart := by
    have hb : tokens.toList[q]'h_q' = tokens[q]! := by
      rw [Array.getElem_toList, getElem!_pos tokens q h_q]
    rw [hb]; exact h_open
  have hstep : btStep (tokens.toList[q]'h_q') s = some (true :: s) := by
    simp only [btStep, h_val]
  have hfold : btFold (some s) [tokens.toList[q]'h_q'] = btStep (tokens.toList[q]'h_q') s := rfl
  rw [h_split, btFold_append, h_pre, hfold, hstep]; rfl

/-- **The full seq-typed gate, discharged from the window opener** (the consume-site corollary the
    root seed feeds `seqSeparatorFacts_of_windowed_safebodyunit`).  Given the opener at `q` is a
    `.flowSequenceStart`, the pre-opener prefix folds to `some s`, the body `[q+1, hi)` is
    depth-`0`-balanced, and the body is **locally Dyck** (`h_floor` — the R313 third gate conjunct,
    which at a genuine seq body comes from `flowBracketBalance_interior_dyck` re-based to the body
    level), the gate `SeqTypedInterior tokens (q+1) hi` holds — so the carrier's body is
    extractable at this window with no second guard. -/
theorem seqTypedInterior_of_opener
    (tokens : Array (Positioned YamlToken)) (q hi : Nat) (h_q : q < tokens.size)
    (s : List Bool) (h_pre : btFold (some []) (tokens.toList.take q) = some s)
    (h_open : tokens[q]!.val = .flowSequenceStart)
    (h_bal : flowBracketBalance tokens (q + 1) hi = 0)
    (h_floor : ∀ i, q + 1 ≤ i → i ≤ hi → flowBracketBalance tokens (q + 1) i ≥ 0) :
    SeqTypedInterior tokens (q + 1) hi :=
  ⟨h_bal, enclosingMark_true_of_opener tokens q h_q s h_pre h_open, h_floor⟩

/-- **The consumer fold — `SeqInteriorSeparators` reduces to a `SafeBodyUnit` provider** (the first
    landable brick of `(i'-b-descend-root)`, per `ref-universal-producer-root-seed-first` /
    `ref-fold-consumer-chain-to-producer-contract`).

    The carrier's body is, at every gated sub-window `[a,b)`, exactly the per-window discharge
    `seqSeparatorFacts_of_windowed_safebodyunit` (R299): one windowed
    `SafeBodyUnit ContentStartTok ((tokens.toList.take b).drop a)` yields BOTH separator facts. So
    proving the carrier `∀`-statement amounts to providing that `SafeBodyUnit` at every gated
    sub-window — and nothing else. This lemma folds the whole consumer chain
    (gate → windowed `SafeBodyUnit` → both facts) into ONE step whose sole hypothesis, `provider`, IS
    the producer's remaining contract: *deliver `SafeBodyUnit` at each seq-typed depth-`0`-balanced
    sub-window of `[lo,hi)`*.

    This retypes the residual from "establish the carrier" to "establish the `SafeBodyUnit`
    provider" (`ref-reduction-by-import`: the retype is the progress). What remains for
    `(i'-b-descend-root)` is exactly `provider`:

    * the **root instance** — `provider` at the outer seq window `[2, size-2)`, where emission
      (`emitList_scans_safebody` / `emitList_body_filtered_characterization`) delivers the outer
      `SafeBodyUnit` directly, no recursion (`ref-universal-producer-root-seed-first` base case);
    * the **descent** — `provider` at each nested seq level, the `btFold`/width-driven induction.

    The gate `SeqTypedInterior tokens a b` is the provider's hypothesis (it picks out exactly the
    seq-typed windows that ARE emitted seq bodies; the R297 probe confirmed `bodySucc` holds on these
    and fails on map-typed interiors, which the gate excludes). -/
theorem seqInteriorSeparators_of_safebody_provider
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat) (h_hi : hi ≤ tokens.size)
    (provider : ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → SeqTypedInterior tokens a b →
      SafeBodyUnit ContentStartTok ((tokens.toList.take b).drop a)) :
    SeqInteriorSeparators tokens lo hi := by
  intro a b ha hab hb hgate
  exact seqSeparatorFacts_of_windowed_safebodyunit tokens a b (Nat.le_trans hb h_hi)
    (provider a b ha hab hb hgate)

/-- **A `SafeBodyUnit`'s head satisfies `Q`** — the necessary precondition the `provider` deliverable
    carries that `SeqTypedInterior` does NOT supply.  In both constructors the first entry `e` is
    nonempty with a `Q`-satisfying head (`h_head : Q (e.head …).val`), and the body's head IS that
    entry's head (`e ≠ []` ⇒ `(e ++ _).head = e.head`).  So any body that is a `SafeBodyUnit Q` starts
    with a `Q`-token. -/
theorem SafeBodyUnit_head_Q {Q : YamlToken → Prop}
    {body : List (Positioned YamlToken)} (h : SafeBodyUnit Q body) (h_ne : body ≠ []) :
    Q (body.head h_ne).val := by
  cases h with
  | single e h_ne' h_unit h_head =>
      obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h_ne'
      exact h_head
  | cons e fe rest h_ne' h_unit h_head h_fe h_rest =>
      obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h_ne'
      exact h_head

/-- **A separator-headed window is NOT a `ContentStartTok` `SafeBodyUnit`** — the kernel of the
    de-risk that re-scopes `(i'-b-descend-root-provider-descent)`.  `ContentStartTok` excludes
    `.flowEntry` (`ContentStartTok_ne_flowEntry`), and a `SafeBodyUnit` forces a `ContentStartTok` head
    (`SafeBodyUnit_head_Q`); so a window whose first token is a `.flowEntry` cannot be a
    `SafeBodyUnit ContentStartTok`.

    **Why this matters for the `provider`.** The gate `SeqTypedInterior tokens a b`
    (`flowBracketBalance tokens a b = 0` ∧ enclosing-seq `btFold`-top `= some true`) places NO
    constraint on the window's head token, so it ADMITS separator-headed windows.  A `#guard`-backed
    minimal pair on the real filtered scan of `[[1, 2], 9]` (filtered tokens
    `streamStart [ [ "1" , "2" ] , "9" ] streamEnd`) confirms it: the two depth-`0` commas at indices
    `4` and `7` BOTH satisfy the gate at `[a, a+1)` (`balance = 0`, `btFold`-top `= some true`,
    enclosed by the outer seq), yet each window's slice is `[comma]`, refuted here.  Hence the
    `provider` hypothesis of `seqInteriorSeparators_of_safebody_provider` is **undischargeable at the
    spurious gated windows** the carrier's `∀ a b` ranges over.  (Content-start-alignment is necessary
    but NOT sufficient either: the gated, content-start-headed window `[3, 5)` = `"1" ,` is a
    trailing-separator slice that is also not a `SafeBodyUnit`.)  The carrier's asserted facts
    (`bodySuccFact`/`noTrailingSepFact`) remain TRUE at every gated window — they reference the
    boundary token past the slice — so the fix is to discharge the carrier's facts directly at the
    windows the future seq-producer actually instantiates (real seq-body interiors `[opener+1, close)`
    and their comma-suffix advance-tails, all genuine `SafeBodyUnit`s), NOT via a uniform per-gated-
    window `SafeBodyUnit` provider.  See Reflection 303. -/
theorem not_safeBodyUnit_of_head_flowEntry
    {body : List (Positioned YamlToken)} (h_ne : body ≠ [])
    (h_head : (body.head h_ne).val = .flowEntry) :
    ¬ SafeBodyUnit ContentStartTok body := fun h =>
  ContentStartTok_ne_flowEntry _ (SafeBodyUnit_head_Q h h_ne) h_head

/-- **`bodySuccFact` RE-BASING** — the first brick of the R303 direct-discharge route, replacing the
    undischargeable per-window `SafeBodyUnit` provider.  Given the *enclosing* seq interior's
    `bodySuccFact` over `[loS, hiS)` (its comma-separation, which the seq body producer / `RecSeqBody`
    delivers at the seq level), the SAME fact holds on any sub-window `[a, b) ⊆ [loS, hiS)` whose start
    `a` sits at the enclosing seq's TOP level — i.e. `flowBracketBalance tokens loS a = 0`.  No
    `SafeBodyUnit`, no per-window deliverable: the proof is pure balance composition.

    **Why this is the redirect.** R303 showed the per-gated-window `SafeBodyUnit` route is FALSE (a
    separator-headed gated window is no `SafeBodyUnit`), yet a `#guard`-backed probe on `[[1, 2], 9]`
    and on `[{a: 1}, 2]` confirmed `bodySuccFact` holds at EVERY gated window — including those spurious
    separator-headed ones — because the fact references the boundary token past the slice, not the
    slice's body-ness.  This lemma is the mechanism: at a window start `a` re-based to depth `0` of the
    enclosing seq, `balance loS (k+1) = balance loS a + balance a (k+1) = 0 + 0` for every interior end
    `k`, so the enclosing `bodySuccFact` fires verbatim, and its window-close disjunct `k+1 = hiS`
    collapses to `k+1 = b` exactly because `k < b ≤ hiS` pins `b = k+1` there.  The enclosing-seq gate
    (`SeqTypedInterior`'s `btFold`-top `= some true`) is what guarantees `a` is at a SEQ top level (not a
    mapping interior, where `bodySuccFact` is FALSE — a key is followed by `.value`, not a separator):
    the probe shows every `bodySuccFact`-failing window is non-gated.  Names no deliverable type, so it
    serves both axes; this is [[ref-window-absolute-gate-subset-restriction]] with the source fact (the
    enclosing seq's `bodySuccFact`) re-based across the depth-`0` re-seating rather than a local guard
    conjunct narrowed. -/
theorem bodySuccFact_rebase (tokens : Array (Positioned YamlToken)) (loS a b hiS : Nat)
    (h_loS_a : loS ≤ a) (h_b_hiS : b ≤ hiS)
    (h_bal0 : flowBracketBalance tokens loS a = 0)
    (h_enc : bodySuccFact tokens loS hiS) :
    bodySuccFact tokens a b := by
  intro k hak hkb hbalk hnfe
  have hk_hiS : k < hiS := Nat.lt_of_lt_of_le hkb h_b_hiS
  have hbal_enc : flowBracketBalance tokens loS (k + 1) = 0 := by
    have hc := flowBracketBalance_compose tokens loS a (k + 1) h_loS_a (by omega)
    rw [h_bal0, hbalk] at hc; omega
  rcases h_enc k (Nat.le_trans h_loS_a hak) hk_hiS hbal_enc hnfe with h | ⟨h', heq⟩
  · -- enclosing closes at `k+1 = hiS`; since `k < b ≤ hiS`, this forces `k+1 = b`.
    exact Or.inl (by omega)
  · -- enclosing yields a following `.flowEntry`; relocate the bound to `b`.
    rcases Nat.lt_or_ge (k + 1) b with hlt | hge
    · exact Or.inr ⟨hlt, heq⟩
    · exact Or.inl (by omega)

/-- **`noTrailingSepFact` RE-BASING** — the twin of `bodySuccFact_rebase` for the carrier's second
    fact.  On a sub-window `[a, b) ⊆ [loS, hiS)` re-based to the enclosing seq's top level
    (`flowBracketBalance tokens loS a = 0`), the no-trailing-separator fact follows from the enclosing
    seq interior's OWN facts: the only relevant position is the window's last `k = b - 1`, a depth-`0`
    (re-based) `.flowEntry`, and the token AFTER it (`tokens[b]`) must be content-start.  Two cases on
    where `b` sits relative to the enclosing close `hiS`:

    * `b < hiS` — `b - 1` is an INTERIOR depth-`0` separator of the enclosing seq, so the enclosing
      depth-`0` `feContentStart` (`h_enc_fe`, the `FlowBodyContent.feContentStart` field) gives the
      following content-start directly;
    * `b = hiS` — `b - 1 = hiS - 1` is the enclosing seq's LAST position, so the enclosing
      `noTrailingSepFact` (`h_enc_nts`) supplies it.

    Both branches re-base the depth premise by composition (`balance loS (b-1) = balance loS a +
    balance a (b-1) = 0`).  Pure case-split + composition, no `SafeBodyUnit`.  Together with
    `bodySuccFact_rebase` this discharges the full carrier body at a re-based seq-top-level window from
    the enclosing seq interior's facts — the R303 redirect, complete for the consume side. -/
theorem noTrailingSepFact_rebase (tokens : Array (Positioned YamlToken)) (loS a b hiS : Nat)
    (h_loS_a : loS ≤ a) (h_b_hiS : b ≤ hiS)
    (h_bal0 : flowBracketBalance tokens loS a = 0)
    (h_enc_fe : ∀ k, loS ≤ k → k + 1 < hiS →
        tokens[k]!.val = .flowEntry → flowBracketBalance tokens loS k = 0 →
        isFlowContentStart tokens[k + 1]!.val)
    (h_enc_nts : noTrailingSepFact tokens loS hiS) :
    noTrailingSepFact tokens a b := by
  intro k hak hkb hsep hbalk
  -- Re-base the depth premise: `balance loS k = balance loS a + balance a k = 0`.
  have hbal_enc : flowBracketBalance tokens loS k = 0 := by
    have hc := flowBracketBalance_compose tokens loS a k h_loS_a (by omega)
    rw [h_bal0, hbalk] at hc; omega
  have hk_hiS : k + 1 ≤ hiS := Nat.le_trans (Nat.le_of_eq hkb) h_b_hiS
  rcases Nat.lt_or_ge (k + 1) hiS with hlt | hge
  · -- interior separator of the enclosing seq → its `feContentStart`.
    exact h_enc_fe k (Nat.le_trans h_loS_a hak) hlt hsep hbal_enc
  · -- last position of the enclosing seq (`k + 1 = hiS`) → its `noTrailingSepFact`.
    have h_eq : k + 1 = hiS := by omega
    exact h_enc_nts k (Nat.le_trans h_loS_a hak) h_eq hsep hbal_enc

/-- **The carrier ASSEMBLES from a per-window enclosing-facts `provider`** (the second brick of the
    R303 direct-discharge route, `(i'-b-locate-enclosing)` — the [[ref-parametric-assembler-extraction]]
    split of the locate boundary).  `bodySuccFact_rebase`/`noTrailingSepFact_rebase` are pure balance
    composition, so the carrier `SeqInteriorSeparators tokens lo hi` reduces — with NO further analysis —
    to a `provider` that, at every gated sub-window `[a,b)`, hands back the *enclosing* seq interior
    `[loS,hiS)` together with the three rebase preconditions/facts:

    * the bounds + re-seating `loS ≤ a`, `b ≤ hiS`, `flowBracketBalance tokens loS a = 0` (the window
      starts at the enclosing seq's TOP level — exactly what the gate's `btFold`-top `= some true`
      witnesses, converse of `enclosingMark_true_of_opener`);
    * the enclosing seq's `bodySuccFact tokens loS hiS` (its comma-separation) — `bodySuccFact_rebase`'s
      source fact;
    * the enclosing seq's interior `feContentStart` (every interior depth-`0` separator is followed by
      content) and its `noTrailingSepFact tokens loS hiS` — `noTrailingSepFact_rebase`'s two sources.

    This is the parametric-assembler-extraction move: lift the inline locate-the-enclosing-window
    reasoning into a `∀ window, gate → ∃ enclosing, …` hypothesis and discharge the *assemble* now (one
    `obtain` + two rebases), splitting the residual into ASSEMBLE (done, here) vs PRODUCE the `provider`
    (the locator — [[ref-reduction-by-import]]).

    **De-risk (`#guard`-backed, on the R304 witness `[[1, 2], 9]`).** A probe enumerating all 12 gated
    windows confirmed that EACH has a located enclosing seq body satisfying every clause above:
    `[3,5)`/`[4,6)`/… → the inner seq `[3,6)`; `[7,9)`/`[8,9)`/… → the outer seq `[2,9)`; the
    preconditions and all enclosing facts evaluate `true` at every one, and the rebase reproduces the
    window's own `bodySuccFact`/`noTrailingSepFact`.  So the `provider` hypothesis is satisfiable — the
    residual is genuine and the assembler is not vacuous.

    **The named residual — `provider`.** Producing it is the locator: from the gate's `btFold`-top
    `= some true` at `a`, recover the innermost enclosing `.flowSequenceStart` at `loS - 1` and its
    matching close `hiS` (the existing `recseqentry_seqbracket_oracle` / `FlowBodyWindow` machinery),
    then supply the enclosing facts from that seq's `SafeBodyUnit`/`RecSeqBody`
    (`seqSeparatorFacts_of_windowed_safebodyunit` for `bodySuccFact`/`noTrailingSepFact`; the interior
    `feContentStart` is the one new sub-fact, the comma-followed-by-content of `RecSeqBody`).  The
    `SafeBodyUnit` route — FALSE for arbitrary gated windows (R303) — is VALID here because `[loS,hiS)`
    is a GENUINE seq body, the right granularity ([[ref-near-leaf-mirror-sheds-machinery]]). -/
theorem seqInteriorSeparators_of_enclosing_provider
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (provider : ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → SeqTypedInterior tokens a b →
      ∃ loS hiS, loS ≤ a ∧ b ≤ hiS ∧ flowBracketBalance tokens loS a = 0 ∧
        bodySuccFact tokens loS hiS ∧
        (∀ k, loS ≤ k → k + 1 < hiS →
          tokens[k]!.val = .flowEntry → flowBracketBalance tokens loS k = 0 →
          isFlowContentStart tokens[k + 1]!.val) ∧
        noTrailingSepFact tokens loS hiS) :
    SeqInteriorSeparators tokens lo hi := by
  intro a b ha hab hb hgate
  obtain ⟨loS, hiS, h_loS_a, h_b_hiS, h_bal0, h_bs, h_fe, h_nts⟩ := provider a b ha hab hb hgate
  exact ⟨bodySuccFact_rebase tokens loS a b hiS h_loS_a h_b_hiS h_bal0 h_bs,
         noTrailingSepFact_rebase tokens loS a b hiS h_loS_a h_b_hiS h_bal0 h_fe h_nts⟩

/-- **The per-window DISPATCHER** — `(i'-b-recursion-driver / ii-merge)` part (a), the case-split that
    reduces ONE seq window's `SeqInteriorSeparators tokens lo hi` to two suppliers: the window's OWN
    `SafeBodyUnit` and a DESCENT provider for its strictly-nested gated sub-windows.

    The `provider` `seqInteriorSeparators_of_enclosing_provider` consumes must, at every gated
    sub-window `[a,b)`, hand back an enclosing seq body `[loS,hiS) ⊇ [a,b)` re-seated at `a`'s depth.
    Those windows split on the **top-level discriminator** `flowBracketBalance tokens lo a = 0`:

    * `= 0` — `a` is at `[lo,hi)`'s OWN top level, so its enclosing seq IS `[lo,hi)` itself; the
      provider is satisfied by `⟨lo, hi, …⟩` directly from the window's `SafeBodyUnit`
      (`seqEnclosingFacts_provider_of_located` at `loS = lo`, `hiS = hi`).  This is the abstract,
      recursion-window form of `seqEnclosingFacts_provider_root` (the root specialises `lo = 2`,
      `hi = size - 2` with the emission `SafeBodyUnit`).
    * `≠ 0` — `a` is nested strictly deeper; the enclosing seq is an inner bracket the recursion must
      locate, supplied by the `desc` hypothesis (which the driver discharges via the backward
      enclosing-opener locator + `seqDescent_provider_of_located`, consuming the width-recursion IH).

    The split is exhaustive and decidable (`Int` equality on the balance), so the dispatch is a pure
    `dite` — the INVERSE of the classify unifier.  This is [[ref-fold-consumer-chain-to-producer-contract]]
    at the dispatch layer: it folds the per-window provider into the two typed residuals the driver
    must source — the window's own `SafeBodyUnit` (the `RecSeqBody` recursion / `seqRoot_safeBodyUnit`
    at the root) and the `desc` locator — leaving only the strong-width fixpoint (part (b)) that threads
    them across the `windowWidth_strongRecOn` edges (`flowBodyWindow_advance`/`flowBodyWindow_descend`).

    **De-risk (`#guard`-backed, `Tests/Guards/Proofs/SeqDispatchPartitionProbe.lean`).** On
    `[[1, 2], 9]` (`lo = 2`) and `[1, [2, 3]]` (`lo = 2`) every gated sub-window is classified by
    `flowBracketBalance tokens 2 a` into exactly one branch — the top-level windows (`= 0`) whose
    enclosing seq is the outer body `[2, 9)`, and the nested windows (`≠ 0`) whose enclosing seq is an
    inner bracket — and each branch's supplier is satisfiable there, so the dispatch is non-vacuous on
    both reach modes (descend-at-root and advance-then-descend). -/
theorem seqInteriorSeparators_of_safebody_and_descent
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat) (h_hi : hi ≤ tokens.size)
    (h_safe : SafeBodyUnit ContentStartTok ((tokens.toList.take hi).drop lo))
    (desc : ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → flowBracketBalance tokens lo a ≠ 0 →
      SeqTypedInterior tokens a b →
      ∃ loS hiS, loS ≤ a ∧ b ≤ hiS ∧ flowBracketBalance tokens loS a = 0 ∧
        bodySuccFact tokens loS hiS ∧
        (∀ k, loS ≤ k → k + 1 < hiS →
          tokens[k]!.val = .flowEntry → flowBracketBalance tokens loS k = 0 →
          isFlowContentStart tokens[k + 1]!.val) ∧
        noTrailingSepFact tokens loS hiS) :
    SeqInteriorSeparators tokens lo hi :=
  seqInteriorSeparators_of_enclosing_provider tokens lo hi (fun a b ha hab hb hgate =>
    if h : flowBracketBalance tokens lo a = 0 then
      seqEnclosingFacts_provider_of_located tokens a b lo hi ha hb h_hi h h_safe
    else
      desc a b ha hab hb h hgate)

/-- **The ROOT SEED — `SeqInteriorSeparators` at the outer span `[2, size-2)`** (Phase J, the seq
    `provider`'s base case, per [[ref-universal-producer-root-seed-first]]: the producer's FIRST
    landable brick is its root seed, not the recursion).

    This brick is the resolution of the architecture the previous revisions left ambiguous, and it
    *corrects* R317.  The full `FlowSubrangesOk` discharge funnels through the per-window `RecSeqBody`
    producer (Route A — `flowSubrangesOk_of_window_producers` consumes it directly), whose
    `windowWidth_strongRecOn` step needs, per window, a `FlowBodyContent` to drive
    `recseqentry_window_dispatch`.  `flowBodyContent_of_deep` builds that `FlowBodyContent` from the
    deep guard PLUS the two separator facts (`bodySucc` / `noTrailingSep`) — and **those separator
    facts are exactly what `SeqInteriorSeparators` carries** (instantiate the carrier at `a = lo`,
    `b = hi`).  So `SeqInteriorSeparators` is on Route A's critical path, supplying the one content
    field the deep guard cannot project (R296).

    The carrier is a *subset restriction* (`SeqInteriorSeparators_narrow`): its body is `lo`/`hi`-free
    except through the domain bounds.  Hence it is established **once, here, at the outer span**, and
    `narrow` lifts it to every B3 sub-window `[lo,hi) ⊆ [2, size-2)` for free.  This is why R317's
    plan to *re-derive* the carrier per window (via the dispatcher with a per-window `SafeBodyUnit`)
    was wrong: at a DESCENDED window the only `SafeBodyUnit` source is `RecSeqBody.toSafeBodyUnit` of
    that window's own `RecSeqBody` — which is precisely the recursion's output the step is *producing*,
    a circular dependency.  At the ROOT the `SafeBodyUnit` is **flat** — `seqRoot_safeBodyUnit`, scanned
    straight off emission, no `RecSeqBody` — so the dispatcher is invoked exactly once, here, with no
    circularity.  (The trivial B1 alias `RecSeqBody.toSafeBodyUnit` the prior next-step anticipated is
    therefore unneeded: it only fed the circular per-window route.)

    Construction: the per-window dispatcher `seqInteriorSeparators_of_safebody_and_descent` at
    `lo = 2`, `hi = size - 2`, fed the flat root `SafeBodyUnit` (`seqRoot_safeBodyUnit`) and the
    `desc` descent provider — lifted here as a hypothesis ([[ref-parametric-assembler-extraction]]),
    isolating B2 (the backward enclosing-opener locator + `seqDescent_provider_of_located`, consuming
    the width IH) as the single remaining seq residual.  `desc`'s satisfiability is already
    `#guard`-backed (`SeqDescentProviderProbe` / `SeqDispatchPartitionProbe`).  Verified-but-unconsumed
    until B2 lands: composes only landed lemmas, references no sorry site, frontier sorry count
    unchanged at 4. -/
theorem seqRoot_seqInteriorSeparators
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v)
    (desc : ∀ a b, 2 ≤ a → a ≤ b → b ≤ tokens.size - 2 →
        flowBracketBalance tokens 2 a ≠ 0 → SeqTypedInterior tokens a b →
        ∃ loS hiS, loS ≤ a ∧ b ≤ hiS ∧ flowBracketBalance tokens loS a = 0 ∧
          bodySuccFact tokens loS hiS ∧
          (∀ k, loS ≤ k → k + 1 < hiS →
            tokens[k]!.val = .flowEntry → flowBracketBalance tokens loS k = 0 →
            isFlowContentStart tokens[k + 1]!.val) ∧
          noTrailingSepFact tokens loS hiS) :
    SeqInteriorSeparators tokens 2 (tokens.size - 2) :=
  seqInteriorSeparators_of_safebody_and_descent tokens 2 (tokens.size - 2)
    (Nat.sub_le tokens.size 2)
    (seqRoot_safeBodyUnit items tokens h_scan h_ne h_all)
    desc

/-- **The seq-enclosure guard** (Phase J — `(i'-b-B3-enclosed-guard)`, the single residual `G`-conjunct
    R320 named).  `SeqEnclosed tokens lo` is the `lo`-keyed enclosing btFold-top fact: the typed
    bracket stack after the prefix `[0, lo)` has top `true` (the window sits immediately inside a flow
    SEQUENCE `[`, not a mapping `{`).  It is *definitionally* the second conjunct of `SeqTypedInterior`
    (the gate `seqWindow_flowBodyContent` consumes), and it is the one piece of that gate neither
    `FlowBodyWindow` nor `FlowBodyContentDeep` carries — both are bracket/content-shape facts blind to
    which bracket TYPE encloses the window.

    It is an *additive parallel type* ([[ref-additive-parallel-type-over-shared-edit]]) beside
    `FlowBodyWindow`, threaded as the third `G`-conjunct of the `windowWidth_strongRecOn` producer.  Its
    two preservation edges below mirror `flowBodyWindow_advance` / `flowBodyWindow_descend`, but with a
    structural asymmetry the balance guards do NOT have ([[ref-converse-forward-invariant-asymmetry]]):
    DESCEND *overwrites* the stack head (pushing an opener forces top `true` regardless of the parent's
    top), so it is parent-head-BLIND — it needs only that the parent fold is DEFINED; ADVANCE *frames*
    the head (a `WellTyped` segment returns the fold to the same stack), so it is parent-head-DEPENDENT
    — it needs the parent's top `true`.  This is the seq-specific analogue of the
    balance-overwrite-vs-rebase split that `flowBodyWindow_{descend,advance}` already exhibit. -/
def SeqEnclosed (tokens : Array (Positioned YamlToken)) (lo : Nat) : Prop :=
  (btFold (some []) (tokens.toList.take lo)).bind (·.head?) = some true

/-- **DESCEND enclosure-preservation** (Phase J — the `SeqEnclosed` companion of
    `flowBodyWindow_descend`).  When the body window's head `tokens[lo]` is a flow-sequence opener `[`,
    the recursion descends into the interior `[lo+1, j)`; this lemma re-establishes `SeqEnclosed` at the
    descended start `lo+1`.  It is the `(lo+1)`-keyed btFold-top reconstructed in place from the located
    opener ([[ref-reconstruct-in-place-over-relocate]] / [[ref-prefix-gate-reconstructed-from-boundary]]),
    exactly the option-A discharge the de-risk found `recseqentry_seqbracket_oracle`'s IH call site
    affords (the opener `lo` is in scope there).

    The proof is a single PUSH: `take (lo+1) = take lo ++ [tokens[lo]]`, the opener `[` pushes `true`
    onto whatever stack the parent fold reached, so the new top is `true`.  Crucially the parent's top
    is NEVER read — only its DEFINEDNESS (`SeqEnclosed lo ⟹ the fold is `some s`); pushing overwrites
    the head.  So this edge would hold from the weaker "parent fold defined", but `SeqEnclosed lo` is
    what the producer threads, so it is the stated hypothesis. -/
theorem seqEnclosed_descend (tokens : Array (Positioned YamlToken)) (lo : Nat)
    (h_enc : SeqEnclosed tokens lo)
    (h_lo_sz : lo < tokens.size)
    (h_open : tokens[lo]!.val = .flowSequenceStart) :
    SeqEnclosed tokens (lo + 1) := by
  unfold SeqEnclosed at h_enc ⊢
  have h_lo_len : lo < tokens.toList.length := by rw [Array.length_toList]; exact h_lo_sz
  have h_lo_val : (tokens.toList[lo]'h_lo_len).val = .flowSequenceStart := by
    rw [Array.getElem_toList, ← getElem!_pos tokens lo h_lo_sz]; exact h_open
  rw [List.take_succ_eq_append_getElem h_lo_len, btFold_append]
  cases hf : btFold (some []) (tokens.toList.take lo) with
  | none => rw [hf] at h_enc; simp at h_enc
  | some s =>
    -- PUSH the opener: `btStep` prepends `true`, so the head is `true` independent of `s`.
    rw [btFold_cons_some]
    simp only [btFold, List.foldl_nil, btStep, h_lo_val, Option.bind_some, List.head?_cons]

/-- **ADVANCE enclosure-preservation** (Phase J — the `SeqEnclosed` companion of
    `flowBodyWindow_advance`).  After the body recursion consumes the first entry, the tail recurses at
    a new start `n` reached across a `WellTyped` segment `[lo, n)` (the entry plus its depth-`0`
    `.flowEntry` separator).  This lemma transports `SeqEnclosed` from `lo` to `n`.

    The proof is a FRAME, not a push: `take n = take lo ++ (take n).drop lo`, and the segment is
    `WellTyped`, so `btFold_frame` (via `WellTyped_frame`) returns the fold to the SAME stack — the top
    is PRESERVED.  Unlike DESCEND this DOES read the parent's top (`SeqEnclosed lo`'s `true`), since the
    frame preserves rather than overwrites.  The `WellTyped` segment is supplied as a hypothesis
    ([[ref-parametric-assembler-extraction]]); the producer discharges it at the depth-`0` separator. -/
theorem seqEnclosed_advance (tokens : Array (Positioned YamlToken)) (lo n : Nat)
    (h_enc : SeqEnclosed tokens lo)
    (h_lo_n : lo ≤ n)
    (h_wt_seg : WellTyped ((tokens.toList.take n).drop lo)) :
    SeqEnclosed tokens n := by
  unfold SeqEnclosed at h_enc ⊢
  have h_split : tokens.toList.take n
      = tokens.toList.take lo ++ (tokens.toList.take n).drop lo := by
    have h := List.take_append_drop lo (tokens.toList.take n)
    rw [List.take_take, Nat.min_eq_left h_lo_n] at h
    exact h.symm
  rw [h_split, btFold_append]
  cases hf : btFold (some []) (tokens.toList.take lo) with
  | none => rw [hf] at h_enc; simp at h_enc
  | some s =>
    -- FRAME: the `WellTyped` segment returns the fold to `s`, so the head `true` is preserved.
    rw [hf] at h_enc
    rw [WellTyped_frame _ s h_wt_seg]
    exact h_enc

/-- **The MAP enclosure predicate** — the `{`-pushes-`false` mirror of `SeqEnclosed` (`:1765`).
    `MapEnclosed tokens lo` reads the TOP of the typed bracket stack after the prefix `[0, lo)` and
    asserts it is `false` — i.e. the window's IMMEDIATE enclosing opener is a flow MAPPING `{`, not a
    sequence `[` (`btStep`'s `{`-push-`false` convention, `WellBracketed.lean:1540-1541`).  This is the
    enclosure guard the future map width-recursion `mapWindowRecMapBody_map_general` (the `RecMapBody`
    analog of `seqWindowRecSeqBody_seq_general`, R415) will thread in its per-window guard `G`, exactly
    where the seq recursion threads `SeqEnclosed`.  Additive parallel primitive
    ([[ref-additive-parallel-type-over-shared-edit]]); no edit to any shared type.  Unlike the map
    context pair `mapWholeStreamWellTyped`/`mapFoldTotal_of_context` (`:6935`/`:7021`), this reads NO
    structure lemma, so it is axiom-CLEAN (`[propext, Quot.sound]` — no `sorryAx`, and not even the
    `Classical.choice` the seq `WellTyped`-plumbing edges carry).
    Verified-but-unconsumed until the map recursion lands; references no sorry site, frontier sorry count
    unchanged at 4. -/
def MapEnclosed (tokens : Array (Positioned YamlToken)) (lo : Nat) : Prop :=
  (btFold (some []) (tokens.toList.take lo)).bind (·.head?) = some false

/-- **DESCEND enclosure-preservation, MAP** — the `false`/`{` mirror of `seqEnclosed_descend` (`:1781`).
    When the window head `tokens[lo]` is a flow-mapping opener `{`, the recursion descends into the
    interior `[lo+1, j)`; this re-establishes `MapEnclosed` at the descended start `lo+1`.  A single
    PUSH: `take (lo+1) = take lo ++ [tokens[lo]]`, the opener `{` pushes `false` onto whatever stack the
    parent fold reached, so the new top is `false` — the parent's top is NEVER read, only its
    DEFINEDNESS (`MapEnclosed lo ⟹ the fold is `some s`); the push overwrites the head.  So this edge
    would hold from the weaker "parent fold defined", but `MapEnclosed lo` is what the producer threads.
    References no sorry site, frontier sorry count unchanged at 4. -/
theorem mapEnclosed_descend (tokens : Array (Positioned YamlToken)) (lo : Nat)
    (h_enc : MapEnclosed tokens lo)
    (h_lo_sz : lo < tokens.size)
    (h_open : tokens[lo]!.val = .flowMappingStart) :
    MapEnclosed tokens (lo + 1) := by
  unfold MapEnclosed at h_enc ⊢
  have h_lo_len : lo < tokens.toList.length := by rw [Array.length_toList]; exact h_lo_sz
  have h_lo_val : (tokens.toList[lo]'h_lo_len).val = .flowMappingStart := by
    rw [Array.getElem_toList, ← getElem!_pos tokens lo h_lo_sz]; exact h_open
  rw [List.take_succ_eq_append_getElem h_lo_len, btFold_append]
  cases hf : btFold (some []) (tokens.toList.take lo) with
  | none => rw [hf] at h_enc; simp at h_enc
  | some s =>
    -- PUSH the opener: `btStep` prepends `false`, so the head is `false` independent of `s`.
    rw [btFold_cons_some]
    simp only [btFold, List.foldl_nil, btStep, h_lo_val, Option.bind_some, List.head?_cons]

/-- **ADVANCE enclosure-preservation, MAP** — the `false`/`{` mirror of `seqEnclosed_advance` (`:1808`).
    After the body recursion consumes the first pair, the tail recurses at a new start `n` reached
    across a `WellTyped` segment `[lo, n)` (the pair plus its depth-`0` `.flowEntry` separator); this
    transports `MapEnclosed` from `lo` to `n`.  A FRAME, not a push: `take n = take lo ++ (take n).drop
    lo`, and the segment is `WellTyped`, so `WellTyped_frame` returns the fold to the SAME stack — the
    top `false` is PRESERVED.  Unlike DESCEND this DOES read the parent's top (`MapEnclosed lo`'s
    `false`), since the frame preserves rather than overwrites.  The `WellTyped` segment is supplied as a
    hypothesis ([[ref-parametric-assembler-extraction]]); the producer discharges it at the depth-`0`
    separator.  This is the DOMINANT edge of the map recursion's ADVANCE (every `.flowEntry`-separated
    pair stays inside the SAME `{ … }`).  References no sorry site, frontier sorry count unchanged at 4. -/
theorem mapEnclosed_advance (tokens : Array (Positioned YamlToken)) (lo n : Nat)
    (h_enc : MapEnclosed tokens lo)
    (h_lo_n : lo ≤ n)
    (h_wt_seg : WellTyped ((tokens.toList.take n).drop lo)) :
    MapEnclosed tokens n := by
  unfold MapEnclosed at h_enc ⊢
  have h_split : tokens.toList.take n
      = tokens.toList.take lo ++ (tokens.toList.take n).drop lo := by
    have h := List.take_append_drop lo (tokens.toList.take n)
    rw [List.take_take, Nat.min_eq_left h_lo_n] at h
    exact h.symm
  rw [h_split, btFold_append]
  cases hf : btFold (some []) (tokens.toList.take lo) with
  | none => rw [hf] at h_enc; simp at h_enc
  | some s =>
    -- FRAME: the `WellTyped` segment returns the fold to `s`, so the head `false` is preserved.
    rw [hf] at h_enc
    rw [WellTyped_frame _ s h_wt_seg]
    exact h_enc

/-- **The per-window MAP grammar-facts provider** — the map analog of `seqWindow_flowBodyContent_general`.
    Given the root map carrier `MapInteriorSeparators tokens lo0 hi0` and the window's structural guard,
    it narrows the carrier to the window `[lo, hi) ⊆ [lo0, hi0)` (window-absolute body,
    [[ref-window-absolute-gate-subset-restriction]]) and instantiates it at the window itself, yielding the
    six `MapGrammarFacts tokens lo hi` the final consumer wants as `h_key_content` … `h_value_bracket_succ`.

    **Strictly simpler than the seq twin.**  The seq provider reads the carrier's two-fact bundle and then
    runs `flowBodyContent_of_deep` to PROJECT a `FlowBodyContent` from a deep-content guard; the map carrier
    already delivers the six adjacency facts directly, so there is NO projection step — the carrier
    instantiation IS the deliverable.  The gate `MapTypedInterior tokens lo hi` is assembled from the
    window's own `balanced`/`dyck` plus the enclosure `MapEnclosed tokens lo` (R517), whose `btFold`-top
    `= some false` IS the gate's middle conjunct definitionally (mirroring how `SeqEnclosed` supplies the
    seq gate's enclosing-`[` mark).

    **Axiom-CLEAN** ([[ref-mirror-inherits-dependency-axioms]] R517 complement, sharpened to a CONSUMER of
    the carrier).  Its dependency closure reads only the carrier hypothesis (a pure `def` over
    `MapGrammarFacts`), `MapInteriorSeparators_narrow`, the `FlowBodyWindow` projections, and `MapEnclosed`
    — NEVER `scanFiltered_emitMap_nonempty_structure` — so it audits `[propext]` ALONE (cleaner even than
    the R517 `MapEnclosed` edges' `[propext, Quot.sound]`: a pure restriction over a `def` carrier carries
    no `Quot.sound`), no `sorryAx`, even though it is a map-axis provider.  The map producer family inherits
    `sorryAx` only once the carrier is itself PRODUCED from the structure lemma; this consumer of an
    *assumed* carrier stays clean, exactly
    as R517 predicts: taint tracks the dependency, not the axis.

    Verified-but-unconsumed (R225) until its consumers land — the map recursion's per-window step
    (`mapWindowRecMapBody_map_general`, the R415 analog) and the `flowSubrangesOk_of_seqRoot_and_mapRoot`
    reconciliation (R512's map twin, which projects these six facts into the consumer's six grammar-fact
    slots).  References no sorry site, frontier sorry count unchanged at 4. -/
theorem mapWindow_grammarFacts_general (tokens : Array (Positioned YamlToken))
    (lo0 hi0 lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_enclosed : MapEnclosed tokens lo)
    (h_carrier0 : MapInteriorSeparators tokens lo0 hi0)
    (h_lo0 : lo0 ≤ lo) (h_hi0 : hi ≤ hi0) :
    MapGrammarFacts tokens lo hi := by
  -- The enclosing carrier narrows to `[lo, hi) ⊆ [lo0, hi0)` (window-absolute body).
  have h_carrier : MapInteriorSeparators tokens lo hi :=
    MapInteriorSeparators_narrow h_lo0 h_hi0 h_carrier0
  -- The gate: balance + Dyck floor come from the window guard; the enclosing-`{` btFold-top is `MapEnclosed`.
  have h_gate : MapTypedInterior tokens lo hi :=
    ⟨h_win.balanced, h_enclosed, h_win.dyck⟩
  exact h_carrier lo hi (Nat.le_refl lo) (Nat.le_of_lt h_win.lo_lt_hi) (Nat.le_refl hi) h_gate

/-- **The root-span instance** — `lo0 := 2`, `hi0 := size-2`, bounds read off
    `FlowBodyWindow.lo_ge`/`hi_le`; the map mirror of `seqWindow_flowBodyContent`. -/
theorem mapWindow_grammarFacts (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_enclosed : MapEnclosed tokens lo)
    (h_root_carrier : MapInteriorSeparators tokens 2 (tokens.size - 2)) :
    MapGrammarFacts tokens lo hi :=
  mapWindow_grammarFacts_general tokens 2 (tokens.size - 2) lo hi
    h_win h_enclosed h_root_carrier h_win.lo_ge h_win.hi_le

/-- **The per-window MAP `MapBodyProps` provider** — the map analog of
    `seqWindow_flowBodyContent_seq_general`, one structural layer UP from `mapWindow_grammarFacts_general`.
    Where the grammar-facts provider stops at the carrier's six adjacency facts, this assembles the full
    ten-field `MapBodyProps tokens lo hi` the map pair-boundary locate consumes (it needs M9/M10 bracket
    matching to place the value separator `kv` when the key is a nested `[ … ]`/`{ … }`, not just a
    scalar).  It composes `mapWindow_grammarFacts_general` (the six carrier facts → M3 `key_content`, M4
    `key_scalar_value`, M6 `value_content`, M7 `value_scalar_succ`, and the M5/M8 bracket-successor
    feeders) with `mapBodyProps_assemble` (which builds M5/M8/M9/M10 from the window's own balance/Dyck/
    `WellTyped` via the typed locators), reading M1 `key_start` off the deep guard's `headKey`
    (`FlowBodyContentDeepMap.headKey`, the map head is a `.key`).

    **The lone non-carrier, non-guard input is M2 `after_fe` — the recorded seq/map carrier ASYMMETRY,
    here pinned to its exact entry point.**  The SEQ carrier `SeqInteriorSeparators` bundles TWO facts
    (`bodySuccFact` *and* `noTrailingSepFact`), so the seq bridge `seqWindow_flowBodyContent_seq_general`
    self-sources its comma-successor fact (`feContent`: every depth-`0` `,` is followed by content) by
    instantiating `noTrailingSepFact` on the narrowed window `[lo, k+1)`.  The MAP carrier
    `MapInteriorSeparators` bundles only the six `MapGrammarFacts` — it has NO comma-successor fact — so
    the map's dual (`after_fe`: every depth-`0` `,` is followed by a `.key`) cannot be re-sourced from
    the carrier and is taken here as a SUPPLIED hypothesis.  This is NOT the same shape as the deep
    guard's `feKey` (`FlowBodyContentDeepMap.feKey`): `feKey` is the *threading* form the recursion
    advances (`,` whose successor is *not* content ⟹ `.key`, the dual-axis gate that lets the advance
    edge re-establish the next window's `headKey` from a supplied successor without proving the
    content-exclusion), whereas `after_fe` is the *assemble* form (an unconditional universal, M2).
    The two do not interconvert without re-proving the very content-exclusion `feKey`'s premise assumes,
    so M2 is genuinely the driver/root-supplied fact ([[ref-additive-field-cost-by-keying]] — the cost
    a parallel field pays depends on which side internalizes it; here the seq carrier pays it and the
    map carrier defers it).  M1 (`headKey`) likewise comes from the deep guard on BOTH axes; only the
    comma-successor split asymmetrically.

    **Axiom profile.**  `mapWindow_grammarFacts_general` and `headKey` are clean
    ([[ref-mirror-inherits-dependency-axioms]] R517–R518: a consumer of an *assumed* carrier stays
    `[propext]`-only); `mapBodyProps_assemble`'s typed-locator machinery contributes the heavier
    `Classical.choice`/`Quot.sound` but NEVER the tainted `scanFiltered_emitMap_nonempty_structure`, so
    no `sorryAx` — the produced `MapBodyProps` is structure-lemma-free.

    Verified-but-unconsumed until the map pair-boundary locate + driver
    (`mapWindowRecMapBody_map_general`, the R415 analog) land: references no sorry site, frontier sorry
    count unchanged at 4. -/
theorem mapWindow_mapBodyProps_general (tokens : Array (Positioned YamlToken))
    (lo0 hi0 lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeepMap tokens lo hi)
    (h_enclosed : MapEnclosed tokens lo)
    (h_close : tokens[hi]!.val = .flowMappingEnd)
    (h_after_fe : ∀ k, lo ≤ k → k < hi →
      flowBracketBalance tokens lo k = 0 →
      tokens[k]!.val = .flowEntry →
      k + 1 ≤ hi ∧ tokens[k + 1]!.val = .key)
    (h_carrier0 : MapInteriorSeparators tokens lo0 hi0)
    (h_lo0 : lo0 ≤ lo) (h_hi0 : hi ≤ hi0) :
    MapBodyProps tokens lo hi := by
  -- the six adjacency facts, from the narrowed carrier instantiated at the window
  have h_facts : MapGrammarFacts tokens lo hi :=
    mapWindow_grammarFacts_general tokens lo0 hi0 lo hi h_win h_enclosed h_carrier0 h_lo0 h_hi0
  obtain ⟨h_kc, h_ksv, h_vc, h_vss, h_kbs, h_vbs⟩ := h_facts
  -- assemble: M1 from the deep guard's head-`.key`, M2 supplied, M3–M8 from the carrier facts,
  -- M5/M8/M9/M10 built inside `mapBodyProps_assemble` from the window's balance/Dyck/`WellTyped`.
  exact mapBodyProps_assemble tokens lo hi
    (Nat.le_of_lt h_win.hi_lt) h_close h_win.balanced h_win.dyck h_win.wellTyped
    (fun _ => h_deep.headKey) h_after_fe
    h_kc h_ksv h_vc h_vss h_kbs h_vbs

/-- **The root-span instance of `mapWindow_mapBodyProps_general`** — `lo0 := 2`, `hi0 := size-2`,
    bounds read off `FlowBodyWindow.lo_ge`/`hi_le`; the map mirror of `seqWindow_flowBodyContent_seq`. -/
theorem mapWindow_mapBodyProps (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeepMap tokens lo hi)
    (h_enclosed : MapEnclosed tokens lo)
    (h_close : tokens[hi]!.val = .flowMappingEnd)
    (h_after_fe : ∀ k, lo ≤ k → k < hi →
      flowBracketBalance tokens lo k = 0 →
      tokens[k]!.val = .flowEntry →
      k + 1 ≤ hi ∧ tokens[k + 1]!.val = .key)
    (h_root_carrier : MapInteriorSeparators tokens 2 (tokens.size - 2)) :
    MapBodyProps tokens lo hi :=
  mapWindow_mapBodyProps_general tokens 2 (tokens.size - 2) lo hi
    h_win h_deep h_enclosed h_close h_after_fe h_root_carrier h_win.lo_ge h_win.hi_le

/-- **The corrected per-window facts bridge — the LIVE carrier→`MapGrammarFacts''` producer that
    REPLACES the dead strict-carrier route.**  This is the `''` mirror of `mapWindow_grammarFacts_general`
    (`:2895`): narrow the enclosing carrier to `[lo, hi) ⊆ [lo0, hi0)`, assemble the gate
    `MapTypedInterior` from the window's own `balanced`/`dyck` plus the `{`-enclosure `MapEnclosed tokens lo`,
    and instantiate the carrier at the window.

    **Why this exists — an inhabitation-debt course-correction (R550, [[ref-inhabitation-debt-validate-target-defs]]).**
    The R549 redirect named the next brick "`mapRoot_mapGrammarFacts''` off emission, composing
    `mapGrammarFacts''_of_mapBodyProps` with `mapWindow_mapBodyProps`."  Probing BEFORE building (rule 3 —
    a hypothesis with no producer is the alarm) shows that composition is a TRAP one level up:
    `mapWindow_mapBodyProps`/`mapWindow_mapBodyProps_general` (`:2962`) — and the whole strict producer
    family `mapWindow_grammarFacts_general` (`:2895`), `mapBodyProps_assemble`'s carrier feeders, and the
    R531 joint content-pack's map half — consume `h_carrier0 : MapInteriorSeparators tokens lo0 hi0`, the
    STRICT carrier threaded through strict `MapGrammarFacts`.  But strict `MapGrammarFacts` is STRONGER than
    the robust `MapGrammarFacts'` that R547 REFUTED on the genuine bracket body `{a:[1], b:2}` window
    `[2,13)` (`mapGrammarFacts'_bracketVal_false`), so via the R545 connector `mapGrammarFacts'_of_mapGrammarFacts`
    (`:706`) the strict carrier is ALSO false there — `MapInteriorSeparators tokens 2 (size-2)` is
    UNSATISFIABLE for any input carrying a bracket-valued entry (and on the window-close axis even without
    brackets, R540).  A producer whose hypothesis no emission can supply is exactly the inhabitation-debt
    trap: it would type-check (it is verified-but-unconsumed), it would compose, and it could be discharged
    by NOBODY.  So `mapWindow_mapBodyProps` is dead as an off-emission route, and the `MapBodyProps` it
    produces is reachable only through it — meaning R549's `mapGrammarFacts''_of_mapBodyProps`, while a
    correct transform, is itself on the dead branch.

    The LIVE path bypasses `MapBodyProps` entirely: the corrected carrier `MapInteriorSeparators''`
    (`:387`) already bundles the matching-close-pinned `MapGrammarFacts''` per gated sub-window, and unlike
    the strict carrier it is NOT refuted — it is inhabited on a unit span (`mapInteriorSeparators''_unit`)
    and proved on the very bracket fixtures the strict/robust forms fail (R548 `mapGrammarFacts''_bracketVal`/
    `_mixed`).  So this bridge instantiates the inhabited corrected carrier directly, the way
    `mapWindow_grammarFacts_general` instantiated the strict one — same narrow+gate+instantiate shape, a LIVE
    hypothesis in place of a dead one.  The eventual `mapRoot_mapInteriorSeparators''` (the recursion's root
    seed) feeds `h_carrier0` here; this bridge is what every per-window consumer calls once that seed lands.

    INHABITATION-DEBT discipline: the trap is proved in `Tests/Reflections/MapCarrierRobustInhabitation.lean`
    (R550) by `mapInteriorSeparators_bracketVal_false : ¬ MapInteriorSeparators fixtureMapSeqVal 2 13` (the
    strict carrier — `mapWindow_mapBodyProps`'s `h_root_carrier` — is unproducible on real bracket emission);
    the bridge's reachability is probed by routing the inhabited unit carrier through it
    (`mapWindow_mapGrammarFacts''_general_unit`), discharging the rule-3 carrier hypothesis with a real
    inhabitant and leaving only the standard `FlowBodyWindow`/`MapEnclosed` guards (the landed
    guard-preservation infra, not this brick's debt) as legible hypotheses.  Verified-but-unconsumed:
    references no sorry site; frontier sorry count unchanged at 4. -/
theorem mapWindow_mapGrammarFacts''_general (tokens : Array (Positioned YamlToken))
    (lo0 hi0 lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_enclosed : MapEnclosed tokens lo)
    (h_carrier0 : MapInteriorSeparators'' tokens lo0 hi0)
    (h_lo0 : lo0 ≤ lo) (h_hi0 : hi ≤ hi0) :
    MapGrammarFacts'' tokens lo hi := by
  -- the enclosing CORRECTED carrier narrows to `[lo, hi) ⊆ [lo0, hi0)` (window-absolute body)
  have h_carrier : MapInteriorSeparators'' tokens lo hi :=
    MapInteriorSeparators''_narrow h_lo0 h_hi0 h_carrier0
  -- the gate: balance + Dyck floor from the window guard; the enclosing-`{` btFold-top is `MapEnclosed`
  have h_gate : MapTypedInterior tokens lo hi :=
    ⟨h_win.balanced, h_enclosed, h_win.dyck⟩
  exact h_carrier lo hi (Nat.le_refl lo) (Nat.le_of_lt h_win.lo_lt_hi) (Nat.le_refl hi) h_gate

/-- **The root-span instance of `mapWindow_mapGrammarFacts''_general`** — `lo0 := 2`, `hi0 := size-2`,
    bounds read off `FlowBodyWindow.lo_ge`/`hi_le`; the corrected-carrier mirror of
    `mapWindow_grammarFacts` (`:2916`). -/
theorem mapWindow_mapGrammarFacts'' (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_enclosed : MapEnclosed tokens lo)
    (h_root_carrier : MapInteriorSeparators'' tokens 2 (tokens.size - 2)) :
    MapGrammarFacts'' tokens lo hi :=
  mapWindow_mapGrammarFacts''_general tokens 2 (tokens.size - 2) lo hi
    h_win h_enclosed h_root_carrier h_win.lo_ge h_win.hi_le

/-- **The all-seq-PATH domain predicate** — `(i'-b-B2c-nested-project, the domain hypothesis)`, the
    proof-side Prop form of `pathAllSeq` (R336, `SeqPathDispatchProbe`).  Where `SeqEnclosed tokens lo`
    reads only the TOP of the typed bracket stack after `[0, lo)` (the window's IMMEDIATE enclosure),
    `SeqPathAllSeq` asserts the WHOLE stack is all-`true` and nonempty: every enclosing frame from the
    root to `lo` is a flow SEQUENCE `[`, none a mapping `{`.  This is the
    [[ref-aggregate-collapses-structured-separates]] structured-state dispatch — the un-aggregated
    `btFold` stack read whole, of which `SeqEnclosed` is the head PROJECTION — bounding
    `rec_seq_body_nested_project`'s navigable domain to the windows whose PATH avoids every severed
    `RecSeqEntry.map` edge ([[ref-severed-edge-bounds-navigator-domain]] / R335).  The nonemptiness
    holds at every `desc`-routed window (it sits inside at least the root `[`). -/
def SeqPathAllSeq (tokens : Array (Positioned YamlToken)) (lo : Nat) : Prop :=
  ∃ s, btFold (some []) (tokens.toList.take lo) = some s ∧ s ≠ [] ∧ s.all (· == true) = true

/-- **DESCEND domain-preservation** — `(i'-b-B2c-nested-project)`, the FIRST de-risk of the
    domain-restricted driver: the DESCEND arm's existing head hypothesis
    `h_lo_open : tokens[lo]! = .flowSequenceStart` (R333) is EXACTLY what discharges the all-seq-PATH
    domain at the recursion edge.  A `.flowSequenceStart` head pushes a `true` onto the stack
    (`btStep … = some (true :: s)`), so the whole stack stays all-`true` and nonempty — the descended
    window `[lo+1, …)` inherits the domain.  This is the WHOLE-stack analogue of `seqEnclosed_descend`
    (which preserves only the TOP); the same single PUSH, but tracking that EVERY frame, not just the
    head, remains a seq.  Confirms the four landed arms compose with NO fifth (map-mirror) sub-branch:
    the only recursion edge that grows the stack does so with a `true`. -/
theorem seqPathAllSeq_descend (tokens : Array (Positioned YamlToken)) (lo : Nat)
    (h : SeqPathAllSeq tokens lo)
    (h_lo_sz : lo < tokens.size)
    (h_open : tokens[lo]!.val = .flowSequenceStart) :
    SeqPathAllSeq tokens (lo + 1) := by
  obtain ⟨s, h_fold, _h_ne, h_all⟩ := h
  have h_lo_len : lo < tokens.toList.length := by rw [Array.length_toList]; exact h_lo_sz
  have h_split : tokens.toList.take (lo + 1)
      = tokens.toList.take lo ++ [tokens.toList[lo]'h_lo_len] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h_lo_len]; rfl
  have h_val : (tokens.toList[lo]'h_lo_len).val = .flowSequenceStart := by
    have hb : tokens.toList[lo]'h_lo_len = tokens[lo]! := by
      rw [Array.getElem_toList, getElem!_pos tokens lo h_lo_sz]
    rw [hb]; exact h_open
  have hstep : btStep (tokens.toList[lo]'h_lo_len) s = some (true :: s) := by
    simp only [btStep, h_val]
  refine ⟨true :: s, ?_, by simp, ?_⟩
  · rw [h_split, btFold_append, h_fold]
    have hfold : btFold (some s) [tokens.toList[lo]'h_lo_len]
        = btStep (tokens.toList[lo]'h_lo_len) s := rfl
    rw [hfold, hstep]
  · rw [List.all_cons, h_all]; rfl

/-- **A map head BREAKS the all-seq-PATH domain** — the negative companion that makes "no fifth
    (map-mirror) sub-branch" precise.  Descending through a `.flowMappingStart` head pushes a `false`
    onto the stack (`btStep … = some (false :: s)`), so the resulting stack is NOT all-`true`: the
    descended window FALLS OUT of `SeqPathAllSeq`.  So within the domain the DESCEND can only fire on a
    `.flowSequenceStart` head — exactly `recseqbody_descend`'s `h_lo_open` — and a `.flowMappingStart`
    head is OUT of the navigator's domain (served by the flat map-path provider), not a deferred
    recursive arm.  Together with `seqPathAllSeq_descend` this is the R337 de-risk:
    [[ref-converse-forward-invariant-asymmetry]] applied to the path stack — the seq edge preserves the
    domain, the map edge cannot. -/
theorem seqPathAllSeq_map_push_breaks (tokens : Array (Positioned YamlToken)) (lo : Nat)
    (h : SeqPathAllSeq tokens lo)
    (h_lo_sz : lo < tokens.size)
    (h_open : tokens[lo]!.val = .flowMappingStart) :
    ¬ SeqPathAllSeq tokens (lo + 1) := by
  obtain ⟨s, h_fold, _h_ne, _h_all⟩ := h
  have h_lo_len : lo < tokens.toList.length := by rw [Array.length_toList]; exact h_lo_sz
  have h_split : tokens.toList.take (lo + 1)
      = tokens.toList.take lo ++ [tokens.toList[lo]'h_lo_len] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h_lo_len]; rfl
  have h_val : (tokens.toList[lo]'h_lo_len).val = .flowMappingStart := by
    have hb : tokens.toList[lo]'h_lo_len = tokens[lo]! := by
      rw [Array.getElem_toList, getElem!_pos tokens lo h_lo_sz]
    rw [hb]; exact h_open
  have hstep : btStep (tokens.toList[lo]'h_lo_len) s = some (false :: s) := by
    simp only [btStep, h_val]
  have h_fold1 : btFold (some []) (tokens.toList.take (lo + 1)) = some (false :: s) := by
    rw [h_split, btFold_append, h_fold]
    have hfold : btFold (some s) [tokens.toList[lo]'h_lo_len]
        = btStep (tokens.toList[lo]'h_lo_len) s := rfl
    rw [hfold, hstep]
  rintro ⟨s', h_fold', _h_ne', h_all'⟩
  rw [h_fold1] at h_fold'
  have h_seq : s' = false :: s := (Option.some.inj h_fold').symm
  rw [h_seq] at h_all'
  simp at h_all'

/-- **A map frame PERSISTS, breaking the all-seq-PATH domain across its whole span** — the DESCEND-arm
    map-head refutation infra (R360), the whole-window generalisation of `seqPathAllSeq_map_push_breaks`.
    A `.flowMappingStart` opener at `p` pushes a `false` onto the typed bracket stack; as long as the
    relative balance from `p + 1` stays `≥ 0` up to `q` (the local Dyck floor — equivalently, the map's
    matching close has NOT yet been reached at `q`, so the frame is never popped), that `false` survives
    at the bottom of the stack at `q`.  Hence `q` falls OUT of `SeqPathAllSeq`.

    Where `seqPathAllSeq_map_push_breaks` handles only the one-step `q = p + 1` (the `false` is the fresh
    head, killed immediately), here the FLOOR carries the frame forward across the entire interior
    `(p, q]`: this is what the DESCEND arm needs when the head entry is a `RecSeqEntry.map` and the target
    window start `a` lands strictly INSIDE it (`q = a - 1` is interior to the map's span, so the floor over
    `[p+1, q]` is a prefix of the map interior's `WellBracketed` floor).  The window's own seq-enclosure
    (`SeqPathAllSeq tokens (a-1)`, R355) is the hypothesis the conclusion refutes, so the map-head DESCEND
    case is VACUOUS — no fifth (map-mirror) recursive arm.

    Mechanically the mirror of `seqOpenerType_of_located_and_gate`: the same `btFold_frame_inv` over a
    floored interior, but with the pushed bit `false` (a `{`, not a `[`) and only the FLOOR (no exact body
    balance, so the persisted prefix `m` may be nonempty), reading the surviving frame
    `S = m ++ (false :: s_p)` off the frame-inverse instead of pinning the head.  A stack carrying a
    `false` is not all-`true`, which is the contradiction. -/
theorem seqPathAllSeq_map_frame_persists (tokens : Array (Positioned YamlToken)) (p q : Nat)
    (h_pq : p < q) (h_q_sz : q ≤ tokens.size)
    (h_open : tokens[p]!.val = .flowMappingStart)
    (h_floor : ∀ i, p + 1 ≤ i → i ≤ q → flowBracketBalance tokens (p + 1) i ≥ 0) :
    ¬ SeqPathAllSeq tokens q := by
  rintro ⟨S, hS, _h_ne, h_all⟩
  have h_p_sz : p < tokens.size := by omega
  have h_p_T : p < tokens.toList.length := by rw [Array.length_toList]; exact h_p_sz
  -- (1) decompose `take q = take (p+1) ++ interior`.
  obtain ⟨interior, hint⟩ :
      ∃ I, I = (tokens.toList.drop (p + 1)).take (q - (p + 1)) := ⟨_, rfl⟩
  have h_split : tokens.toList.take q = tokens.toList.take (p + 1) ++ interior := by
    rw [hint, ← List.take_add]; congr 1; omega
  have h_split_p : tokens.toList.take (p + 1)
      = tokens.toList.take p ++ [tokens.toList[p]'h_p_T] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h_p_T]; rfl
  -- (2) the prefix `take p` folds to `some s_p`.
  obtain ⟨s_p, hsp⟩ : ∃ s_p, btFold (some []) (tokens.toList.take p) = some s_p :=
    btFold_some_prefix (tokens.toList.take p) ([tokens.toList[p]'h_p_T] ++ interior) S (by
      rw [← List.append_assoc, ← h_split_p, ← h_split]; exact hS)
  have hTp : tokens.toList[p]'h_p_T = tokens[p]! := by
    rw [Array.getElem_toList, getElem!_pos tokens p h_p_sz]
  -- (3) the opener pushes `false`: stack after `[0, p+1)` is `false :: s_p`.
  have h_after : btFold (some []) (tokens.toList.take (p + 1)) = some (false :: s_p) := by
    rw [h_split_p, btFold_append, hsp]
    have : btFold (some s_p) [tokens.toList[p]'h_p_T] = btStep (tokens.toList[p]'h_p_T) s_p := rfl
    rw [this, hTp]
    simp [btStep, h_open]
  -- (4) the whole `take q` fold equals the interior fold from `false :: s_p`.
  have hfold : btFold (some ([] ++ (false :: s_p))) interior = some S := by
    rw [List.nil_append]
    rw [h_split, btFold_append, h_after] at hS
    exact hS
  -- (5) floor bridge: `pbalance (interior.take k) ≥ 0` for every `k`.
  have h_int_len : interior.length = q - (p + 1) := by
    rw [hint, List.length_take, List.length_drop, Array.length_toList]; omega
  have hfloor' : ∀ k, k ≤ interior.length →
      0 ≤ (([] : List Bool).length : Int) + pbalance (interior.take k) := by
    intro k hk
    have hk' : k ≤ q - (p + 1) := by rw [h_int_len] at hk; exact hk
    have htk : interior.take k = (tokens.toList.drop (p + 1)).take k := by
      rw [hint, List.take_take]; congr 1; omega
    have hbridge : flowBracketBalance tokens (p + 1) (p + 1 + k)
        = pbalance ((tokens.toList.drop (p + 1)).take k) := by
      rw [flowBracketBalance_eq_pbalance tokens (p + 1) (p + 1 + k) (by omega)]; congr 2; omega
    have hfl : (0 : Int) ≤ pbalance ((tokens.toList.drop (p + 1)).take k) := by
      rw [← hbridge]; exact h_floor (p + 1 + k) (by omega) (by omega)
    rw [htk]; simpa using hfl
  -- (6) frame-inverse: `S = m ++ (false :: s_p)` — the `false` persists at the bottom.
  obtain ⟨m, _hm, hSm⟩ := btFold_frame_inv interior [] (false :: s_p) S hfloor' hfold
  -- (7) a stack containing `false` is not all-`true`.
  rw [hSm, List.all_append] at h_all
  simp [List.all_cons] at h_all

/-- **ADVANCE domain-preservation** — the missing third edge of the all-seq-PATH domain, the
    `SeqPathAllSeq` companion of `seqEnclosed_advance` (the TOP-projection advance).  When the
    spine-walk ADVANCES past a consumed entry-plus-separator segment `[lo, n)` to the tail base `n`,
    this lemma transports the WHOLE-path domain across the segment.  Unlike `seqPathAllSeq_descend`
    (a PUSH that overwrites the head) this is a FRAME: the segment is `WellTyped` (it returns to
    depth `0`), so `WellTyped_frame` returns the fold to the *same* stack `s` — every conjunct
    (definedness, nonemptiness, all-`true`) is preserved VERBATIM, the stack literally unchanged.
    This is even more direct than the top-only `seqEnclosed_advance`, which must re-read the head:
    here the entire stack is identical on both sides, so `h_ne`/`h_all` carry through untouched.

    R337 authored only the DESCEND edge (`seqPathAllSeq_descend`, preservation) and its NEGATION
    (`seqPathAllSeq_map_push_breaks`); the ADVANCE edge was named by the wrapper's next-step pointer
    but never proven — the navigator's domain has THREE edges (descend / advance / leaf), and the
    advance-frame analogue had to be lifted from `seqEnclosed_advance` to the whole stack.  The
    `WellTyped` segment is supplied as a hypothesis ([[ref-parametric-assembler-extraction]]); the
    producer discharges it at the depth-`0` `.flowEntry` separator (the balanced head-entry segment,
    R337's [[ref-converse-forward-invariant-asymmetry]] advance side). -/
theorem seqPathAllSeq_advance (tokens : Array (Positioned YamlToken)) (lo n : Nat)
    (h : SeqPathAllSeq tokens lo)
    (h_lo_n : lo ≤ n)
    (h_wt_seg : WellTyped ((tokens.toList.take n).drop lo)) :
    SeqPathAllSeq tokens n := by
  obtain ⟨s, h_fold, h_ne, h_all⟩ := h
  refine ⟨s, ?_, h_ne, h_all⟩
  have h_split : tokens.toList.take n
      = tokens.toList.take lo ++ (tokens.toList.take n).drop lo := by
    have h := List.take_append_drop lo (tokens.toList.take n)
    rw [List.take_take, Nat.min_eq_left h_lo_n] at h
    exact h.symm
  rw [h_split, btFold_append, h_fold, WellTyped_frame _ s h_wt_seg]

/-- **The carrier co-construction's `SeqPathAllSeq` descend edge — PUSH ∘ FRAME, NOT a new edge** —
    `(i'-b-B2c-(d) — STEP D: the joint induction's nested-arm path thread)`.  The carrier↔recursion
    co-construction (`seqRoot_carrier_of_widthEnc`'s `h_widthEnc`, the last seq residual) sources each
    NESTED window's `h_safe` from `seqWindow_safeBodyUnit`'s nested arm, whose lone non-emission
    hypothesis is `SeqPathAllSeq tokens (lo - 1)` (every enclosing frame `[`-typed).  When the joint
    induction descends from a bracket body into a CHILD bracket body, it must re-establish that path
    fact at the child opener — the residual `seqWindow_safeBodyUnit`'s docstring named "the btFold-push
    preservation of `SeqPathAllSeq` across a located `[`".

    **The de-risk finding: that residual is NOT a new edge.**  Reaching the child opener `n` from the
    parent's path key is a PUSH followed by a FRAME, both already landed:

    * **PUSH** — `seqPathAllSeq_descend` (R337): crossing the located opener `[` at `k` pushes a `true`,
      carrying `SeqPathAllSeq tokens k` to `SeqPathAllSeq tokens (k + 1)` (inside the bracket);
    * **FRAME** — `seqPathAllSeq_advance` (R357): the child opener need NOT be the FIRST entry — earlier
      sibling entries `[k+1, n)` may precede it.  That run is `WellTyped` (a depth-`0` balanced sequence
      of complete entries + separators), so it FRAMES the stack back unchanged, carrying
      `SeqPathAllSeq tokens (k + 1)` to `SeqPathAllSeq tokens n` at the child opener.

    The "single located `[`" framing in the residual description hid the FRAME-to-reach component: the
    located position `n` is not adjacent to the crossed opener `k`.  Both component edges exist AND are
    already composed for the NAVIGATOR (`nestedSeq_recseqentry_locate_descend_step` /
    `_advance_step`, R361/R362) — so the joint CARRIER induction's descend edge is the SAME composition,
    keyed for the carrier rather than the spine walk.  No new `SeqPathAllSeq` edge is owed; this brick is
    the one-line fusion ([[ref-compose-arm-seam-before-skeleton]]).

    Verified-but-unconsumed until the carrier co-construction threads it (R225): composes only the two
    landed path edges, references no sorry site, frontier sorry count unchanged at 4; axiom-clean. -/
theorem seqPathAllSeq_into_child (tokens : Array (Positioned YamlToken)) (k n : Nat)
    (h_path : SeqPathAllSeq tokens k)
    (h_k_sz : k < tokens.size)
    (h_open : tokens[k]!.val = .flowSequenceStart)
    (h_kn : k + 1 ≤ n)
    (h_seg_wt : WellTyped ((tokens.toList.take n).drop (k + 1))) :
    SeqPathAllSeq tokens n :=
  seqPathAllSeq_advance tokens (k + 1) n
    (seqPathAllSeq_descend tokens k h_path h_k_sz h_open) h_kn h_seg_wt

/-- **The seq-head DESCEND seam of the emission-spine-walk locator** — `(i'-b-B2c-nested-fbc-emission-
    locator-descend-seam)`, R361.  The standalone arm-callable the `Nat.strongRecOn` wrapper
    `nestedSeq_recseqentry_locate` invokes in its DESCEND case when the head entry is a *seq* block
    `op :: (interior ++ [cl])` and the target window start lands strictly INSIDE it.  Composing the two
    landed bricks the seam is named for ("descend brick ▸ `seqPathAllSeq_descend`",
    [[ref-compose-arm-seam-before-skeleton]]): `nestedSeq_recseqentry_locate_descend` (R353, the pure
    drop-algebra slice re-base — the descended interior re-slices to `[off+1, off+1+interior.length)`)
    and `seqPathAllSeq_descend` (R337, the all-seq-PATH domain preservation across the single
    `.flowSequenceStart` PUSH).  Together they re-establish, at the descended base `off+1`, BOTH the
    navigator's slice invariant AND its domain — the two non-mechanical facts the recursion's IH
    consumes (the fit and `H' ≤ size` are arithmetic the wrapper does; `RecSeqBody interior` is the
    head entry's stored `seq.h_rec` the wrapper holds from `cases e`).

    The off-opener type `tokens[off]! = .flowSequenceStart` is taken as a hypothesis, IDENTICALLY to the
    LEAF arm `nestedSeq_recseqentry_locate_leaf_full`'s `h_open` — the wrapper supplies both arms the
    head-opener type from the same `cases e` `.seq` decomposition, so the seam never re-extracts the head
    from the slice.  Mirrors R359's LEAF seam: compose the landed-brick arm's seam BEFORE the skeleton,
    de-risking the DESCEND case's slice+domain composition in isolation.  Verified-but-unconsumed until
    the wrapper threads it; references no sorry site, frontier sorry count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_descend_step
    (tokens : Array (Positioned YamlToken))
    (body rest interior : List (Positioned YamlToken))
    (op cl : Positioned YamlToken)
    (off H : Nat)
    (h_slice : body = (tokens.toList.take H).drop off)
    (h_bound : off + body.length ≤ H)
    (h_Hsz : H ≤ tokens.size)
    (h_prefix : body = (op :: (interior ++ [cl])) ++ rest)
    (h_off_open : tokens[off]!.val = .flowSequenceStart)
    (h_domain : SeqPathAllSeq tokens off) :
    interior = (tokens.toList.take (off + 1 + interior.length)).drop (off + 1)
    ∧ SeqPathAllSeq tokens (off + 1) := by
  refine ⟨nestedSeq_recseqentry_locate_descend tokens body rest interior op cl off H
            h_slice h_bound h_prefix, ?_⟩
  have hlen : 1 ≤ body.length := by
    rw [h_prefix, List.length_append, List.length_cons]; omega
  have h_off_H : off < H := by omega
  have h_off_sz : off < tokens.size := by omega
  exact seqPathAllSeq_descend tokens off h_domain h_off_sz h_off_open

/-- **The seq-head ADVANCE seam of the emission-spine-walk locator** — `(i'-b-B2c-nested-fbc-emission-
    locator-advance-seam)`, R362, the LAST arm seam before the `Nat.strongRecOn` skeleton.  The
    standalone arm-callable the wrapper `nestedSeq_recseqentry_locate` invokes in its ADVANCE case when
    the head entry `e` is followed by a depth-`0` `.flowEntry` separator `fe` and the target window start
    lands strictly PAST the head entry-plus-separator block.  A PARALLEL fusion
    ([[ref-compose-arm-seam-before-skeleton]], R361's parallel shape): `nestedSeq_recseqentry_locate_advance`
    (R353, the pure drop-algebra TAIL re-base — `rest` re-slices to `[off+e.length+1, H)`, dropping the
    `e.length+1` head-entry-plus-separator tokens) and `seqPathAllSeq_advance` (R357, the all-seq-PATH
    domain preservation across the consumed segment) re-establish, at the advanced base `off+e.length+1`,
    BOTH the slice invariant AND the domain.

    Unlike the DESCEND seam, the domain advance needs the consumed segment to be stack-neutral —
    `seqPathAllSeq_advance` demands `WellTyped` of the segment `[off, off+e.length+1)`.  That segment is
    EXACTLY the entry-plus-separator `e ++ [fe]` (proven internally from the `h_slice`/`h_prefix`/`h_bound`
    frame via `List.drop_take` + `List.take_append`), so the seam exposes the obligation in its STRUCTURAL
    form `WellTyped (e ++ [fe])`, not the raw slice.

    The `WellTyped (e ++ [fe])` hypothesis is THREADED, not discharged inside the seam: a probe
    ([[ref-probe-deferred-universal-before-producing]], [[ref-minimal-pair-extracts-the-gate]]) refuted the
    blueprint-named `RecSeqEntry e → WellTyped e` bridge.  `WellBracketed` (the only interior gate the
    `RecSeqEntry.map` constructor stores) is balance-only and TYPE-BLIND (`flowBracketDelta` maps both `[`
    and `{` to `+1`), so it admits a MISTYPED map interior like `[ }` — concretely `{ [ } }` has
    `pbalance = 0` (passes the gate) yet `btFold (some []) · = none` (not `WellTyped`).  So the typed fact
    cannot be CREATED from the entry's type-blind structure ([[ref-type-blind-invariant-transports-via-converse-frame]]);
    it is the seam's deferred obligation, to be sourced later by frame-transport from a global `WellTyped`.
    Verified-but-unconsumed until the wrapper threads it; references no sorry site, frontier sorry count
    unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_advance_step
    (tokens : Array (Positioned YamlToken))
    (body rest e : List (Positioned YamlToken))
    (fe : Positioned YamlToken)
    (off H : Nat)
    (h_slice : body = (tokens.toList.take H).drop off)
    (h_bound : off + body.length ≤ H)
    (h_prefix : body = e ++ fe :: rest)
    (h_domain : SeqPathAllSeq tokens off)
    (h_wt_seg : WellTyped (e ++ [fe])) :
    rest = (tokens.toList.take H).drop (off + e.length + 1)
    ∧ SeqPathAllSeq tokens (off + e.length + 1) := by
  refine ⟨nestedSeq_recseqentry_locate_advance tokens body rest e fe off H h_slice h_prefix, ?_⟩
  -- bound on the advanced base: off + e.length + 1 ≤ off + body.length ≤ H
  have h_blen : e.length + 1 ≤ body.length := by
    rw [h_prefix, List.length_append, List.length_cons]; omega
  have h_n_le_H : off + e.length + 1 ≤ H := by omega
  -- the consumed segment `[off, off+e.length+1)` is exactly the entry-plus-separator `e ++ [fe]`
  have h_seg : (tokens.toList.take (off + e.length + 1)).drop off = e ++ [fe] := by
    have h_take_take : tokens.toList.take (off + e.length + 1)
        = (tokens.toList.take H).take (off + e.length + 1) := by
      rw [List.take_take, Nat.min_eq_left h_n_le_H]
    rw [h_take_take, List.drop_take, ← h_slice, h_prefix]
    have h_sub : off + e.length + 1 - off = e.length + 1 := by omega
    rw [h_sub, List.take_append]
    congr 1
    · exact List.take_of_length_le (by omega)
    · have : e.length + 1 - e.length = 1 := by omega
      rw [this]; simp
  rw [← h_seg] at h_wt_seg
  exact seqPathAllSeq_advance tokens off (off + e.length + 1) h_domain (by omega) h_wt_seg

/-- **The ADVANCE arm's `WellTyped` supplier of the emission-spine-walk locator** —
    `(i'-b-B2c-nested-fbc-emission-locator-advance-welltyped)`, the LAST content brick before the
    `Nat.strongRecOn` skeleton.  The ADVANCE seam `nestedSeq_recseqentry_locate_advance_step` (R362)
    THREADS `WellTyped (e ++ [fe])` rather than discharging it, because the R362 probe refuted the
    `RecSeqEntry e → WellTyped e` bridge (`WellBracketed` is type-blind, admits the mistyped `{ [ } }`).
    This brick is the discharge the seam deferred: it PRODUCES `WellTyped (e ++ [fe])` at the dispatch
    site from the wrapper's `FlowBodyWindow` guard.

    The de-risk that the skeleton's SMALLEST-FIRST next-step posed — "does the wrapper's `RecSeqBody body`
    window site sit under a global `WellTyped`?" — resolves YES: the wrapper's four-conjunct `G` carries
    `FlowBodyWindow tokens off H`, whose `.wellTyped` field IS `WellTyped ((tokens.toList.take H).drop off)`
    (the whole-window typed fact) and whose `.dyck` field is the Dyck floor.  The type-blind balance
    invariant cannot CREATE the typed fact but it can LICENSE its TRANSPORT
    ([[ref-type-blind-invariant-transports-via-converse-frame]]): `WellTyped_subrange` carries the
    whole-window `WellTyped` DOWN to the balanced-cut prefix `[off, off+e.length+1)` given the dispatch's
    `flowBracketBalance tokens off (off+e.length+1) = 0` (the separator sits at depth `0`).  The cut prefix
    is EXACTLY the entry-plus-separator `e ++ [fe]` (the slice bridge `h_seg`, lifted verbatim from the
    advance seam), so the produced fact lands in the seam's STRUCTURAL form, ready to thread.

    So no preceding frame-transport brick is owed — the skeleton supplies the ADVANCE arm's typed fact
    inline, exactly as `seqWindowRecSeqBody` already does at its own `m+1` cut (`WellTyped_subrange` from
    `h_win.wellTyped` + `h_bal_m1`).  Mirrors the leaf/descend/advance seams' discipline
    ([[ref-compose-arm-seam-before-skeleton]]): compose the last standalone arm-callable BEFORE the
    skeleton tangles it with dispatch + measure.  Verified-but-unconsumed until the wrapper threads it;
    references no sorry site, frontier sorry count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_advance_welltyped
    (tokens : Array (Positioned YamlToken))
    (body rest e : List (Positioned YamlToken)) (fe : Positioned YamlToken)
    (off H : Nat)
    (h_slice : body = (tokens.toList.take H).drop off)
    (h_bound : off + body.length ≤ H)
    (h_prefix : body = e ++ fe :: rest)
    (h_win : FlowBodyWindow tokens off H)
    (h_bal0 : flowBracketBalance tokens off (off + e.length + 1) = 0) :
    WellTyped (e ++ [fe]) := by
  have h_blen : e.length + 1 ≤ body.length := by
    rw [h_prefix, List.length_append, List.length_cons]; omega
  have h_n_le_H : off + e.length + 1 ≤ H := by omega
  have h_seg : (tokens.toList.take (off + e.length + 1)).drop off = e ++ [fe] := by
    have h_take_take : tokens.toList.take (off + e.length + 1)
        = (tokens.toList.take H).take (off + e.length + 1) := by
      rw [List.take_take, Nat.min_eq_left h_n_le_H]
    rw [h_take_take, List.drop_take, ← h_slice, h_prefix]
    have h_sub : off + e.length + 1 - off = e.length + 1 := by omega
    rw [h_sub, List.take_append]
    congr 1
    · exact List.take_of_length_le (by omega)
    · have : e.length + 1 - e.length = 1 := by omega
      rw [this]; simp
  rw [← h_seg]
  exact WellTyped_subrange tokens off off (off + e.length + 1) H
    (Nat.le_refl off) (by omega) h_n_le_H (Nat.le_of_lt h_win.hi_lt) h_win.wellTyped h_bal0
    (fun p hp1 hp2 => h_win.dyck p hp1 (by omega))

/-- **The ADVANCE arm's balance-`0` cut fact of the emission-spine-walk locator** —
    `(i'-b-B2c-nested-fbc-emission-locator-advance-balance)`, the DISPATCH brick: the SMALLEST-FIRST
    de-risk of the `Nat.strongRecOn` skeleton.  The skeleton's ADVANCE arm feeds
    `nestedSeq_recseqentry_locate_advance_welltyped` (R363) a hypothesis
    `flowBracketBalance tokens off (off + e.length + 1) = 0` (the cut sits at depth `0`).  Unlike
    `seqWindowRecSeqBody`'s balance-keyed dispatch — where the analogous `h_bal_m1` is derived from the
    dispatch's located separator `m` plus the comma delta (`SeqInteriorSeparators.lean:1899`) — this
    locator's dispatch is pure LENGTH ARITHMETIC (`SeqNestedEntryLocateProbe.move_trichotomy`, R350),
    so the cut fact is sourced STRUCTURALLY instead: the head entry `e` is a complete `RecSeqEntry`
    (`pbalance e = 0` from `RecSeqEntry.toWellBracketed`) and the `.flowEntry` separator `fe` has
    `flowBracketDelta = 0`, so the entry-plus-separator `e ++ [fe]` is balanced (`pbalance = 0`), which
    `flowBracketBalance_eq_pbalance` transports to the positional `flowBracketBalance tokens off
    (off+e.length+1)`.

    This is `recseqbody_advance`'s `h_bal_sep` derivation (`NonemptyStructure.lean:1169`) lifted to a
    standalone brick keyed on the locator's slice frame (`h_slice`/`h_bound`/`h_prefix`) rather than the
    `recseqbody_advance` dispatch's `h_eq` — the only non-mechanical piece between the landed arm seams
    (LEAF R359, DESCEND R361, ADVANCE consume R362 + WellTyped supplier R363) and the closed recursion;
    with it the skeleton is pure plumbing.  Verified-but-unconsumed until the wrapper threads it;
    references no sorry site, frontier sorry count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_advance_balance
    (tokens : Array (Positioned YamlToken))
    (body rest e : List (Positioned YamlToken)) (fe : Positioned YamlToken)
    (off H : Nat)
    (h_slice : body = (tokens.toList.take H).drop off)
    (h_bound : off + body.length ≤ H)
    (h_prefix : body = e ++ fe :: rest)
    (h_e : RecSeqEntry e)
    (h_fe : fe.val = .flowEntry) :
    flowBracketBalance tokens off (off + e.length + 1) = 0 := by
  have h_eq : (tokens.toList.take H).drop off = e ++ fe :: rest := by rw [← h_slice]; exact h_prefix
  have h_blen : body.length = e.length + 1 + rest.length := by
    rw [h_prefix, List.length_append, List.length_cons]; omega
  have hle : e.length + 1 ≤ H - off := by omega
  -- the entry-plus-separator slice `[off, off+|e|+1)` is exactly `e ++ [fe]`
  have h_take_sep : (tokens.toList.drop off).take (e.length + 1) = e ++ [fe] := by
    have h1 : ((tokens.toList.take H).drop off).take (e.length + 1)
        = (tokens.toList.drop off).take (e.length + 1) := by
      rw [List.drop_take, List.take_take, Nat.min_eq_left hle]
    rw [← h1, h_eq, List.take_append, List.take_of_length_le (by omega),
        show e.length + 1 - e.length = 1 from by omega]
    simp
  -- `pbalance (e ++ [fe]) = 0`: the entry balances (`RecSeqEntry`) and the separator has delta `0`.
  have h_pbsep : pbalance (e ++ [fe]) = (0 : Int) := by
    rw [pbalance_append, h_e.toWellBracketed.1, pbalance_singleton, h_fe,
        flowBracketDelta_flowEntry]; rfl
  rw [flowBracketBalance_eq_pbalance tokens off (off + e.length + 1) (by omega),
      show off + e.length + 1 - off = e.length + 1 from by omega, h_take_sep, h_pbsep]

/-- **The LEAF branch of the emission-spine-walk locator's per-window step `h_step`** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-hstep)`, R366, the SMALLEST-FIRST de-risk the
    blueprint queued for the step: "write `G` as a concrete bundle and prove the LEAF branch of
    `h_step` FIRST, confirming `G` carries exactly `leaf_full`'s hypothesis list and nothing more is
    owed there".  This is that brick — the LEAF arm bridged to its `G`-fields BEFORE `G` is finalized
    as a structure, so the LEAF's debt is itemized from the window-ABSOLUTE typed-interior bundle the
    blueprint says `G` carries.

    At the LEAF (`a = off + 1`, the dispatch's first `move_trichotomy` arm) the guard supplies the
    slice/window frame (`h_slice`/`h_bound`/`h_Hsz`/`h_rec`), the opener `tokens[off]! = [` (a head
    projection of `G`'s `SeqPathAllSeq tokens off`), the close `tokens[b]! = ]`, and — keyed on the
    FIXED target window `[off+1, b)` (R356 window-absolute, NOT the walking origin) — the typed-interior
    bundle `SeqTypedInterior tokens (off+1) b`.  The LEAF seam `nestedSeq_recseqentry_locate_leaf_full`
    (R359) reads TWO balance facts off that bundle, at DIFFERENT origins: its `h_inner`
    (`flowBracketBalance (off+1) b = 0`) is `SeqTypedInterior`'s first conjunct VERBATIM, but its
    `h_floor` (the ENCLOSURE floor `∀ i ∈ (off, b], flowBracketBalance off i ≥ 1`, keyed on the OPENER
    origin `off`) is one origin LOWER than the bundle's INTERIOR floor (`≥ 0`, keyed on `off+1`).  The
    gap is exactly the opener delta: `flowBracketBalance off i = flowBracketBalance off (off+1) +
    flowBracketBalance (off+1) i = (+1) + (≥ 0) ≥ 1` (`flowBracketBalance_compose` + the single-token
    opener read `flowBracketDelta tokens[off]! = +1`).  So the `≥ 1` enclosure floor the close-pinning
    `recseqentry_close_pin` consumes is DERIVED from the bundle's `≥ 0` interior floor — it is NOT a
    separate `G`-field, confirming `G` owes the LEAF only the window-absolute `SeqTypedInterior` (plus
    the opener/close/slice it already carries for the other arms).

    Verified-but-unconsumed until the skeleton wires `h_step` (dispatch on `move_trichotomy`, this is
    the `a = off+1` disjunct producing `Q` via `Or.inl`); references no sorry site, frontier sorry
    count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_leaf_typed
    (tokens : Array (Positioned YamlToken)) (off H b : Nat)
    (body : List (Positioned YamlToken))
    (h_slice : body = (tokens.toList.take H).drop off)
    (h_bound : off + body.length ≤ H)
    (h_Hsz : H ≤ tokens.size)
    (h_rec : RecSeqBody body)
    (h_open : tokens[off]!.val = .flowSequenceStart)
    (h_off1_b : off + 1 < b)
    (h_b_H : b < H)
    (h_bclose : tokens[b]!.val = .flowSequenceEnd)
    (h_typed : SeqTypedInterior tokens (off + 1) b) :
    ∃ lo op cl interior, lo + 1 = off + 1 ∧ off + 1 ≤ b ∧
      RecSeqEntry (op :: (interior ++ [cl])) ∧
      op.val = .flowSequenceStart ∧ interior ≠ [] ∧
      (tokens.toList.take (b + 1)).drop lo = op :: (interior ++ [cl]) := by
  obtain ⟨h_inner, _h_mark, h_floor0⟩ := h_typed
  have h_off_sz : off < tokens.size := by omega
  have h_off_len : off < tokens.toList.length := by rw [Array.length_toList]; exact h_off_sz
  -- Single-token opener read at `off`, bridging `tokens.toList[off]` to `tokens[off]!`.
  have h_tok : tokens.toList[off]'h_off_len = tokens[off]! := by
    rw [getElem!_pos tokens off h_off_sz, Array.getElem_toList]
  have h_single : flowBracketBalance tokens off (off + 1) = flowBracketDelta tokens[off]!.val := by
    rw [flowBracketBalance_single tokens off h_off_len, h_tok]
  have h_delta1 : flowBracketDelta tokens[off]!.val = 1 := by
    rw [h_open]; exact flowBracketDelta_flowSequenceStart
  -- Enclosure floor `≥ 1` (origin `off`) from the interior floor `≥ 0` (origin `off+1`) + opener `+1`.
  have h_floor : ∀ i, off < i → i ≤ b → flowBracketBalance tokens off i ≥ 1 := by
    intro i hi1 hi2
    have h_comp : flowBracketBalance tokens off i
        = flowBracketBalance tokens off (off + 1) + flowBracketBalance tokens (off + 1) i :=
      flowBracketBalance_compose tokens off (off + 1) i (by omega) (by omega)
    have h_f0 : flowBracketBalance tokens (off + 1) i ≥ 0 := h_floor0 i (by omega) hi2
    rw [h_comp, h_single, h_delta1]
    omega
  exact nestedSeq_recseqentry_locate_leaf_full tokens off H b body
    h_slice h_bound h_Hsz h_rec h_open h_off1_b h_b_H h_bclose h_inner h_floor

/-- **The emission-spine-walk locator's per-window GUARD, as a concrete structure** —
    `(i'-b-B2c-nested-fbc-emission-locator-guard-structure)`, R367.  The bundle `G off H body` the
    `Nat.strongRecOn` driver `seqLocateRecDriver` threads, finally pinned as a `structure` so the three
    arm re-bundles (LEAF / DESCEND / ADVANCE) all read and write the SAME field set.  Parameterised by
    the FIXED target window `[a, b)` (the constants `Q` mentions, never the walk's `off`/`H`/`body`) and
    the WALKING window `off H body`.

    The fields are the R354/R356-settled and R366-confirmed list PLUS the R368 `opener` field PLUS the
    R369-added `window : FlowBodyWindow tokens off H` — the WALKING-keyed field only the ADVANCE arm's
    `WellTyped`-supplier (`…advance_welltyped`, R363) consumes, added now as an additive extension of this
    own-type ([[ref-additive-parallel-type-over-shared-edit]]: the structure is built up arm-by-arm, the
    field committed once its consumer's form is confirmed).  Unlike the window-ABSOLUTE fields it is keyed
    on the WALKING `off`/`H`, so each recursion move RE-ESTABLISHES it (DESCEND via `WellTyped_subrange`,
    ADVANCE via `flowBodyWindow_advance`) — it does NOT pass through.  The key R366 finding is encoded
    here: `typed : SeqTypedInterior tokens a b`
    is keyed on the FIXED `[a, b)`, NOT the walking `off` — it is WINDOW-ABSOLUTE and so passes through
    every descend/advance UNCHANGED, the reason the LEAF could read it at `a = off + 1` without an
    `off`-origin floor field.  The R368 `opener` field (`flowBracketBalance tokens (a-1) a = 1`) is the
    same kind: fixed-target-keyed, descends free, and is the strict-containment discriminator the
    END-FREE gate cannot carry ([[ref-strict-containment-needs-opener]]). -/
structure SeqLocateGuard (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (off H : Nat) (body : List (Positioned YamlToken)) : Prop where
  /-- the all-seq-PATH domain at the walking origin (descend PUSHes a `[`, advance FRAMEs across a
      balanced segment — both preserve it). -/
  domain : SeqPathAllSeq tokens off
  /-- the walking body is a recursive seq body (the head-entry-or-cons dispatch reads it). -/
  recBody : RecSeqBody body
  /-- the walking body is the positional slice `[off, H)`. -/
  slice : body = (tokens.toList.take H).drop off
  /-- the slice fits inside the window. -/
  bound : off + body.length ≤ H
  /-- the window's right cut is inside the token array. -/
  Hsz : H ≤ tokens.size
  /-- the WINDOW-ABSOLUTE typed interior of the FIXED target `[a, b)` (R356 — invariant across the
      walk). -/
  typed : SeqTypedInterior tokens a b
  /-- the FIXED target's close token. -/
  close : tokens[b]!.val = .flowSequenceEnd
  /-- the FIXED target's OPENER is a real bracket — the R368 discriminator the END-FREE gate cannot
      carry ([[ref-strict-containment-needs-opener]]).  Keyed on the FIXED `a - 1` (the entry opener,
      one before the gated interior start), so — like `typed`/`close` — it is WINDOW-ABSOLUTE and
      descends through every move UNCHANGED, supplying `seqTarget_close_lt_interiorEnd`'s strict
      `b < c` (R368) at the descend re-bundle's `win_hi`. -/
  opener : flowBracketBalance tokens (a - 1) a = 1
  /-- the FIXED target's ENCLOSING PATH is all-seq — the R374 (BRICK B-i) probe's owed window-absolute
      fact (`seqPathAllSeq_map_descend_excluded`'s `h_path`).  Keyed on the FIXED `a - 1` (the entry
      opener, the same anchor as `opener`), so — like `typed`/`close`/`opener` — it is WINDOW-ABSOLUTE
      and descends through every move UNCHANGED (a free verbatim pass-through in the constructing
      DESCEND/ADVANCE arms).  Distinct from the walking-keyed `domain : SeqPathAllSeq tokens off`: in the
      map-head DESCEND case `domain` re-based to `a - 1` is precisely what `seqPathAllSeq_map_frame_persists`
      REFUTES — so the refutation's positive must be this target-anchored TWIN, not the walking copy
      ([[ref-target-anchored-twin-refutes-walk-break]]).  Its root-seed instance is the descent's DEBT
      ([[ref-root-seed-discriminator-not-from-gate]]), owed at BRICK D; nothing establishes it yet. -/
  path : SeqPathAllSeq tokens (a - 1)
  /-- window containment: the target start is past the walking opener… -/
  win_lo : off + 1 ≤ a
  /-- …the target is STRICTLY non-degenerate — the interior `[a, b)` is NON-EMPTY (R376, C-i).  This
      was `a ≤ b` through R375, but the doc always claimed "non-degenerate": a probe (empty seq `[` `]`,
      `a = b`) showed `a ≤ b` together with `opener`/`close`/`typed` is satisfied by an EMPTY-seq target,
      so the bare guard could NOT exclude `RecSeqEntry.seqEmpty` (whose interior is `[]`, failing the
      deliverable's `interior ≠ []`).  Non-emptiness is INDEPENDENT of the other window-absolute fields,
      so it is RESTORED here as the strict `a < b` ([[ref-downstream-derisk-restores-upstream]]; the
      doc/type mismatch was the tell).  Window-ABSOLUTE (keyed on the fixed `a`/`b`), so it descends
      verbatim through the constructing arms; its root-seed instance is the locator's non-empty-target
      precondition, owed at BRICK D.  At the LEAF (`a = off + 1`) it IS the leaf's `h_off1_b : off+1 < b`
      precondition (`nestedSeq_recseqentry_locate_leaf_off1_b`). -/
  win_ab : a < b
  /-- …and the target close is inside the walking right cut. -/
  win_hi : b < H
  /-- the WALKING window `[off, H)` is a `FlowBodyWindow` — the R367-deferred field that only the
      ADVANCE arm's `WellTyped`-supplier (`…advance_welltyped`, R363) consumes, now come due (its exact
      form pinned by that consumer).  Unlike the window-ABSOLUTE fields above, this one is keyed on the
      WALKING `off`/`H`, so each recursion move RE-ESTABLISHES it: DESCEND transports it down to the head
      interior `[off+1, off+1+interior.length)` via `WellTyped_subrange` (the balanced descend sub-window
      [[ref-type-blind-invariant-transports-via-converse-frame]]), ADVANCE re-frames it across the
      consumed entry via `flowBodyWindow_advance`. -/
  window : FlowBodyWindow tokens off H

/-- **The LEAF disjunct of the locator's per-window step `h_step`, through the guard structure** —
    `(i'-b-B2c-nested-fbc-emission-locator-step-leaf)`, R367.  With `G` now a concrete `SeqLocateGuard`,
    this is the LEAF arm of `h_step` projected through the structure: at the dispatch's first
    `move_trichotomy` arm (`a = off + 1`, the target window IS the walking head entry) the guard's
    fields supply `leaf_typed`'s entire hypothesis list — slice/bound/Hsz/rec/typed/close directly,
    `b < H` as `win_hi` — and the two residual leaf-DISPATCH facts (`h_open`, the head opener type, and
    `h_off1_b`, the non-degenerate close `off + 1 < b`) are taken as hypotheses, exactly as the skeleton
    will derive them from the `recseqbody_head_or_cons` decomposition before invoking this arm.  Commits
    the structure (every field but `win_lo`/`win_ab`/`opener`/`path` is consumed here, pinning their
    types) and confirms the LEAF arm still threads after the R368 `opener` and R375 `path` extensions
    (additive own-type fields ⇒ it must — the LEAF ignores the new fixed-target discriminators; `opener`
    feeds the DESCEND `win_hi`, `path` feeds the map-DESCEND refutation, neither read here).
    Verified-but-unconsumed until the skeleton wires `h_step`; references no sorry site, frontier sorry
    count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_step_leaf
    (tokens : Array (Positioned YamlToken)) (a b off H : Nat)
    (body : List (Positioned YamlToken))
    (g : SeqLocateGuard tokens a b off H body)
    (h_a : a = off + 1)
    (h_open : tokens[off]!.val = .flowSequenceStart)
    (h_off1_b : off + 1 < b) :
    ∃ lo op cl interior, lo + 1 = a ∧ a ≤ b ∧
      RecSeqEntry (op :: (interior ++ [cl])) ∧
      op.val = .flowSequenceStart ∧ interior ≠ [] ∧
      (tokens.toList.take (b + 1)).drop lo = op :: (interior ++ [cl]) := by
  subst h_a
  exact nestedSeq_recseqentry_locate_leaf_typed tokens off H b body
    g.slice g.bound g.Hsz g.recBody h_open h_off1_b g.win_hi g.close g.typed

/-- **The LEAF's non-degenerate-close fact `off + 1 < b` — the `seqEmpty`-target EXCLUSION** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-brick-c-i)`, R376, BRICK C-i.  At the dispatch's LEAF
    arm (`a = off + 1`, the target IS the walking head entry) the deliverable `Q` demands `interior ≠ []`,
    i.e. the target close `b` is strictly past the start (`off + 1 < b`) — exactly the leaf's `h_off1_b`
    precondition (`nestedSeq_recseqentry_locate_step_leaf`).  This is NOT derivable from
    `opener`/`close`/`typed`/`win_ab`-as-`≤`: a probe (empty seq `[` `]`, `a = b`) satisfies ALL of them
    yet has an EMPTY interior, so a `RecSeqEntry.seqEmpty` head (interior `[]`) would pass the bare guard
    and break the deliverable.  The discriminator is the strict `win_ab : a < b` restored at R376
    ([[ref-downstream-derisk-restores-upstream]]); here it is simply re-based to the leaf coordinate.  So
    the `seqEmpty` head arm is EXCLUDED — its close sits at `off + 1`, and `b = off + 1` would contradict
    this `off + 1 < b` (the `b = off + 1` step is BRICK D's matching-uniqueness, fed by THIS fact).  Landed
    standalone so the boundary fact is debugged OUTSIDE the dispatch's case tree; verified-but-unconsumed
    until BRICK D wires `h_step`.  References no sorry site, frontier sorry count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_leaf_off1_b
    (tokens : Array (Positioned YamlToken)) (a b off H : Nat)
    (body : List (Positioned YamlToken))
    (g : SeqLocateGuard tokens a b off H body)
    (h_a : a = off + 1) :
    off + 1 < b := by
  subst h_a; exact g.win_ab

/-- **The DELTA-GENERIC CONS boundary exclusion — `a` is never ONE PAST a non-opener token** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-brick-c-ii-delta)`, R379, BRICK D assembly.  The
    delta-generic lift of `nestedSeq_recseqentry_locate_cons_boundary` (below, now a corollary): given a
    boundary token at position `m` whose flow-bracket DELTA is `≠ 1` (i.e. NOT a `[`/`{` opener), the
    target start `a ≠ m + 1`.  The discriminator is `g.opener : flowBracketBalance tokens (a-1) a = 1` —
    at `a = m + 1` the single-token balance at `a - 1 = m` is `flowBracketDelta tokens[m]!.val`, which
    `h_delta` says is `≠ 1`; contradiction.  The boundary token's identity enters ONLY through `h_delta`,
    so ONE proof subsumes every non-opener boundary: the seq CLOSE (`.flowSequenceEnd`, δ = −1), the MAP
    CLOSE (`.flowMappingEnd`, δ = −1), AND the scalar HEAD (δ = 0) — exactly the three CONS-shape
    boundaries BRICK D's `h_step` must exclude.  This is the demo's `boundary_excluded` (R377,
    `Tests/Reflections/DeltaGenericBoundaryFamily.lean`, already fully delta-generic) realised at the
    `tokens`/`flowBracketBalance` layer.  Verified-but-unconsumed until `h_step` wires it; references no
    sorry site, frontier sorry count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_cons_boundary_delta
    (tokens : Array (Positioned YamlToken)) (a b off H m : Nat)
    (body : List (Positioned YamlToken))
    (g : SeqLocateGuard tokens a b off H body)
    (h_m_sz : m < tokens.size)
    (h_delta : flowBracketDelta tokens[m]!.val ≠ 1) :
    a ≠ m + 1 := by
  have h_m_len : m < tokens.toList.length := by rw [Array.length_toList]; exact h_m_sz
  have h_tok_m : tokens.toList[m]'h_m_len = tokens[m]! := by
    rw [getElem!_pos tokens m h_m_sz, Array.getElem_toList]
  have h_bal : flowBracketBalance tokens m (m + 1) = flowBracketDelta tokens[m]!.val := by
    rw [flowBracketBalance_single tokens m h_m_len, h_tok_m]
  intro h_a
  have hop := g.opener
  rw [h_a] at hop
  have harith : m + 1 - 1 = m := by omega
  rw [harith, h_bal] at hop
  exact h_delta hop

/-- **The CONS boundary exclusion — the target start `a` is never ONE PAST a seq CLOSE** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-brick-c-ii)`, R377, BRICK C-ii.  `move_trichotomy off
    e.length a` (the dispatch's length-arithmetic move selector) requires `h_ne : a ≠ off + e.length` —
    the separator/post-close position can never be a valid interior start.  This brick supplies it for the
    seq head: given a `.flowSequenceEnd` close at position `m`, the target start `a ≠ m + 1`.  BRICK D
    instantiates it at the seq head entry's close (`e = op :: (interior ++ [cl])`, `cl` at
    `m = off + interior.length + 1`, so `m + 1 = off + e.length`) to discharge `move_trichotomy`'s `h_ne`.

    Now a one-line COROLLARY of the delta-generic sibling above (R379): a seq close has
    `flowBracketDelta .flowSequenceEnd = -1 ≠ 1`.  This is the EXACT argument `step_advance`'s
    `h_ne_boundary` runs for the SEPARATOR (`a ≠ off + e.length + 1`, `a-1` the depth-`0` `.flowEntry`),
    with the close (delta `-1`) swapped for the separator (delta `0`).  C-i's lesson APPLIED: the queued
    spec described `a-1` as the separator, but a `#guard`/`#eval` probe (witnesses `N`/`T`/`D`,
    `SeqNestedEntryLocateProbe`) showed at `a = off + e.length` the position `a - 1 = off + e.length - 1`
    is the head entry's CLOSE (delta `-1` for a seq `]`, `0` for a scalar), NOT the separator (which sits
    at `a`, delta `0`) — so the geometry differs but `g.opener` IS the discriminator (delta at `a-1` is
    `≤ 0 ≠ 1` in every case).  References no sorry site, frontier sorry count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_cons_boundary
    (tokens : Array (Positioned YamlToken)) (a b off H m : Nat)
    (body : List (Positioned YamlToken))
    (g : SeqLocateGuard tokens a b off H body)
    (h_m_sz : m < tokens.size)
    (h_close : tokens[m]!.val = .flowSequenceEnd) :
    a ≠ m + 1 :=
  nestedSeq_recseqentry_locate_cons_boundary_delta tokens a b off H m body g h_m_sz (by
    rw [h_close, flowBracketDelta_flowSequenceEnd]; omega)

/-- **The head entry's interior balance + Dyck floor, in `tokens` coordinates — head-shape-BLIND** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-hstep-interior-floor)`, R373, the FIRST refutation
    brick the skeleton-wiring de-risk surfaced (BRICK A).  Given the walking slice frame
    (`h_slice`/`h_bound`) and a head decomposition `body = (op :: (interior ++ [cl])) ++ rest` with
    `WellBracketed interior`, the interior window `[off+1, off+1+interior.length)` is balanced and
    Dyck-floored in `tokens` coordinates.

    The point is the word **head-blind**: this transport was, until now, INLINE inside
    `nestedSeq_recseqentry_locate_step_descend` (R369), specialised to the SEQ head — but the derivation
    never reads the head's `.flowSequenceStart`.  The interior slice is recovered by
    `nestedSeq_recseqentry_locate_descend` (R353), whose only inputs are the slice frame + the
    `op :: (interior ++ [cl])` prefix shape, NOT the opener type; the balance/floor then re-base into
    `pbalance` over that slice (`flowBracketBalance_eq_pbalance`) and discharge against
    `WellBracketed interior`'s two conjuncts directly.  Extracting it severs the head-shape dependency so
    the SAME lemma serves the dispatch's MAP-head refutation: when the head entry is a `RecSeqEntry.map`
    whose interior contains the target seq opener (the dangerous DESCEND-into-map case), the map's
    interior floor is exactly this `h_floor`, fed to `seqPathAllSeq_map_frame_persists` to refute the
    carried `domain : SeqPathAllSeq tokens off` — the case is VACUOUS, no fifth recursive arm.  So one
    extraction discharges the de-risk's load-bearing gap on BOTH sides of the seq/map split
    ([[ref-coerce-to-weaker-reuse-wrapper]]: the producer keeps one substrate; the head-type that
    distinguishes the consumers is precisely the field the transport never touches).

    CONSUMED below by the retrofitted `nestedSeq_recseqentry_locate_step_descend` (it replaces that arm's
    inline `h_drop`/`h_takem`/`h_int_bal`/`h_int_floor` block with one `obtain`), and queued for the
    map-refutation brick (BRICK B).  References no sorry site, frontier sorry count unchanged at 4. -/
theorem recseqentry_head_interior_floor_tokens
    (tokens : Array (Positioned YamlToken))
    (body rest interior : List (Positioned YamlToken))
    (op cl : Positioned YamlToken)
    (off H : Nat)
    (h_slice : body = (tokens.toList.take H).drop off)
    (h_bound : off + body.length ≤ H)
    (h_prefix : body = (op :: (interior ++ [cl])) ++ rest)
    (h_wb : WellBracketed interior) :
    flowBracketBalance tokens (off + 1) (off + 1 + interior.length) = 0 ∧
    (∀ i, off + 1 ≤ i → i ≤ off + 1 + interior.length →
        flowBracketBalance tokens (off + 1) i ≥ 0) := by
  have h_islice : interior = (tokens.toList.take (off + 1 + interior.length)).drop (off + 1) :=
    nestedSeq_recseqentry_locate_descend tokens body rest interior op cl off H
      h_slice h_bound h_prefix
  have h_drop : (tokens.toList.drop (off + 1)).take interior.length = interior := by
    have h1 : (tokens.toList.take (off + 1 + interior.length)).drop (off + 1)
        = (tokens.toList.drop (off + 1)).take interior.length := by
      rw [List.drop_take]; congr 1; omega
    rw [← h1]; exact h_islice.symm
  have h_takem : ∀ m, m ≤ interior.length →
      interior.take m = (tokens.toList.drop (off + 1)).take m := by
    intro m hm
    rw [← h_drop, List.take_take, Nat.min_eq_left hm]
  refine ⟨?_, ?_⟩
  · rw [flowBracketBalance_eq_pbalance tokens (off + 1) (off + 1 + interior.length) (by omega)]
    have harith : off + 1 + interior.length - (off + 1) = interior.length := by omega
    rw [harith, h_drop]; exact h_wb.1
  · intro i hi1 hi2
    rw [flowBracketBalance_eq_pbalance tokens (off + 1) i hi1,
        ← h_takem (i - (off + 1)) (by omega)]
    exact h_wb.2 (i - (off + 1))

/-- **A map head BREAKS the seq-enclosure TOP — the map-LEAF refutation** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-hstep-map-refute-leaf)`, R374, BRICK B-ii.  The
    top-only mirror of `seqPathAllSeq_map_push_breaks` (lines 1359–1384) — the same one-step PUSH, but
    tracking only the typed-stack TOP (`SeqEnclosed`) instead of the whole path (`SeqPathAllSeq`).  A
    `.flowMappingStart` opener at `lo` pushes a `false` onto the stack (`btStep … = some (false :: s)`),
    so the head after `[0, lo+1)` is `false`, NOT `true`: `lo+1` falls OUT of `SeqEnclosed`.

    This is the cleaner of the dispatch's two map-head routes.  At the LEAF arm (`a = off + 1`, the
    map is the IMMEDIATE encloser of the target start `a = lo+1` with `lo = off = a-1`), the guard's
    window-absolute `typed.2.1 : SeqEnclosed tokens a` is contradicted DIRECTLY — no whole-stack
    `domain` (`SeqPathAllSeq`) is needed, because `SeqEnclosed` reads exactly the frame the map pushes.
    The proof never assumes the prefix fold is defined: if `btFold (take lo) = none` the enclosure is
    already `none ≠ some true`; if `some s`, the map push makes the head `false`.  Verified-but-
    unconsumed until BRICK D wires `h_step`; references no sorry site, frontier sorry count unchanged
    at 4. -/
theorem seqEnclosed_map_push_breaks (tokens : Array (Positioned YamlToken)) (lo : Nat)
    (h_lo_sz : lo < tokens.size)
    (h_open : tokens[lo]!.val = .flowMappingStart) :
    ¬ SeqEnclosed tokens (lo + 1) := by
  intro h_enc
  unfold SeqEnclosed at h_enc
  have h_lo_len : lo < tokens.toList.length := by rw [Array.length_toList]; exact h_lo_sz
  have h_lo_val : (tokens.toList[lo]'h_lo_len).val = .flowMappingStart := by
    rw [Array.getElem_toList, ← getElem!_pos tokens lo h_lo_sz]; exact h_open
  rw [List.take_succ_eq_append_getElem h_lo_len, btFold_append] at h_enc
  cases hf : btFold (some []) (tokens.toList.take lo) with
  | none => rw [hf, btFold_none] at h_enc; simp at h_enc
  | some s =>
    rw [hf, btFold_cons_some] at h_enc
    simp only [btFold, List.foldl_nil, btStep, h_lo_val, Option.bind_some, List.head?_cons] at h_enc
    exact absurd h_enc (by simp)

/-- **A map head with the target INTERIOR is VACUOUS — the map-DESCEND refutation** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-hstep-map-refute-descend)`, R374, BRICK B-i.  The
    DESCEND-shaped map case: the head entry is a `.flowMappingStart` block `op :: (interior ++ [cl])`
    at `off` and the FIXED target opener `a - 1` lands strictly INSIDE it (`off + 1 < a`, `a - 1`
    interior to the map's span).  This case is refuted by carrying the map's `false` frame from `off`
    all the way to `a - 1` (the map has not closed before `a - 1`, so its `false` is still on the
    stack), which puts `a - 1` OUT of `SeqPathAllSeq` — contradicting the target's own all-seq path.

    **The probe (R374) that resolved the de-risk's open CAUTION.**  The contradiction needs a POSITIVE
    `SeqPathAllSeq tokens (a - 1)` — the target opener's full enclosing path is all-seq.  This is NOT
    the guard's `domain : SeqPathAllSeq tokens off` "re-based to `a-1`": re-basing is impossible HERE,
    because the map between `off` and `a-1` is exactly what breaks all-seq (the would-be re-based fact
    is precisely what `seqPathAllSeq_map_frame_persists` refutes).  Nor is `SeqPathAllSeq tokens (a-1)`
    a current guard field or derivable from `g.domain` in the map case (it is FALSE there).  So it is
    a genuinely NEW window-absolute fact — the target's path-domain, true for the real target
    regardless of what the walk encounters — taken here as the hypothesis `h_path`.  This is now
    SOURCED (R375): the R368 pattern ([[ref-downstream-derisk-restores-upstream]] — a discriminator the
    gate cannot carry is restored as a window-absolute guard field) added `path : SeqPathAllSeq tokens
    (a - 1)` to `SeqLocateGuard` as its 14th field — a free verbatim pass-through (`path := g.path`) in
    the constructing DESCEND/ADVANCE arms, READ-ONLY (ignored) in LEAF; its root-seed instance remains
    the descent's DEBT, owed at BRICK D ([[ref-root-seed-discriminator-not-from-gate]]).  When BRICK D
    wires `h_step` it discharges this lemma's `h_path` by `g.path`.

    The map's interior floor over `[off+1, a-1]` is exactly BRICK A's `recseqentry_head_interior_floor_tokens`
    (head-BLIND — the SAME extraction the seq-DESCEND `win_hi` consumes), restricted to `a - 1 ≤
    off+1+interior.length`, fed to `seqPathAllSeq_map_frame_persists tokens off (a-1)`.  Verified-but-
    unconsumed until BRICK D wires `h_step`; references no sorry site, frontier sorry count unchanged at
    4. -/
theorem seqPathAllSeq_map_descend_excluded
    (tokens : Array (Positioned YamlToken)) (a off H : Nat)
    (body rest interior : List (Positioned YamlToken))
    (op cl : Positioned YamlToken)
    (h_slice : body = (tokens.toList.take H).drop off)
    (h_bound : off + body.length ≤ H)
    (h_Hsz : H ≤ tokens.size)
    (h_prefix : body = (op :: (interior ++ [cl])) ++ rest)
    (h_wb : WellBracketed interior)
    (h_map : tokens[off]!.val = .flowMappingStart)
    (h_path : SeqPathAllSeq tokens (a - 1))
    (h_desc_lo : off + 1 < a)
    (h_desc_hi : a < off + interior.length + 2) :
    False := by
  obtain ⟨_h_bal, h_floorA⟩ :=
    recseqentry_head_interior_floor_tokens tokens body rest interior op cl off H
      h_slice h_bound h_prefix h_wb
  have hblen : body.length = interior.length + 2 + rest.length := by
    rw [h_prefix]; simp only [List.length_append, List.length_cons, List.length_nil]
  have h_q_sz : a - 1 ≤ tokens.size := by omega
  have h_notpath : ¬ SeqPathAllSeq tokens (a - 1) :=
    seqPathAllSeq_map_frame_persists tokens off (a - 1) (by omega) h_q_sz h_map
      (fun i h1 h2 => h_floorA i h1 (by omega))
  exact h_notpath h_path

/-- **The DESCEND re-bundle's containment thread `win_hi`** — `(i'-b-B2c-nested-fbc-emission-locator-
    descend-win-hi)`, R368, the lone analytical field of the not-yet-assembled
    `nestedSeq_recseqentry_locate_step_descend`.  At the descended window `[off+1, c)` — `c =
    off+1+interior.length`, the head interior's right end (= the head's close position) — the target
    close `b` must satisfy `b < c`, the descended guard's `win_hi`.  This is NOT omega from the dispatch
    (`move_trichotomy` constrains only `a` by length, never `b`); it is a two-floor relay
    ([[ref-two-floor-relay-close-bound]]) — but with a THIRD input the gate alone does not carry.

    **The gate is END-FREE w.r.t. this bound** ([[ref-end-free-gate-underdetermines-the-close]]).
    Recall the deliverable's entry is `op :: (interior' ++ [cl'])` at `[a-1, b]` — opener at `a-1`,
    the gated window `[a, b)` is its INTERIOR, close at `b`.  `SeqTypedInterior tokens a b` + `close`
    admit `b = c` (the target close coinciding with the head's OWN interior-end close): inside an
    interior `x , [y]` the window at `a` = the position just past the `,` separator passes the gate
    (`balance (off+1) a = 0`, mark seq) with `b` = the interior end `c`, yet that `a` is NOT a genuine
    seq-entry interior start — `tokens[a-1]` is the separator `,`, not the opener `[`.  So the relay
    yields only the NON-strict `b ≤ c`; the strict `b < c` needs the discriminator that the target's
    opener at `a - 1` is a real bracket — `flowBracketBalance tokens (a-1) a = 1` — which excludes
    exactly the spurious separator-headed windows ([[ref-downstream-derisk-restores-upstream]]: the
    dropped discriminator is restored as a guard field, window-absolute so it descends unchanged like
    `typed`/`close`).

    The proof: assume `c ≤ b`.  The gate floor at `c` (`a ≤ c ≤ b`) gives `balance a c ≥ 0`; composing
    through the balanced interior (`balance (off+1) c = 0`) plus the interior Dyck floor at `a` forces
    `balance (off+1) a = 0` — `a` sits at the interior TOP level.  Then the opener `balance (a-1) a = 1`
    composes to `balance (off+1) (a-1) = -1`, contradicting the interior Dyck floor at `a-1`.  So
    `b < c`.  Only the interior balance + Dyck floor + the gate floor + the opener are used (no head
    opener/close delta needed) — the minimal hypothesis set, exactly the descend window's re-established
    facts plus the new opener field.  Verified-but-unconsumed until the descend re-bundle threads it;
    references no sorry site, frontier sorry count unchanged. -/
theorem seqTarget_close_lt_interiorEnd
    (tokens : Array (Positioned YamlToken)) (a b off c : Nat)
    (h_off_a : off + 2 ≤ a)
    (h_a_c : a ≤ c)
    (h_int_bal : flowBracketBalance tokens (off + 1) c = 0)
    (h_int_floor : ∀ i, off + 1 ≤ i → i ≤ c → flowBracketBalance tokens (off + 1) i ≥ 0)
    (h_open : flowBracketBalance tokens (a - 1) a = 1)
    (h_gate : SeqTypedInterior tokens a b) :
    b < c := by
  obtain ⟨_h_bal, _h_mark, h_gate_floor⟩ := h_gate
  rcases Nat.lt_or_ge b c with h_lt | h_ge
  · exact h_lt
  · exfalso
    -- gate floor at `c`: `balance a c ≥ 0`.
    have h_ac : flowBracketBalance tokens a c ≥ 0 := h_gate_floor c h_a_c h_ge
    -- compose through the balanced interior: `balance (off+1) c = balance (off+1) a + balance a c`.
    have h_comp : flowBracketBalance tokens (off + 1) c
        = flowBracketBalance tokens (off + 1) a + flowBracketBalance tokens a c :=
      flowBracketBalance_compose tokens (off + 1) a c (by omega) h_a_c
    -- interior Dyck floor at `a`: `balance (off+1) a ≥ 0`.
    have h_int_a : flowBracketBalance tokens (off + 1) a ≥ 0 :=
      h_int_floor a (by omega) h_a_c
    -- so `a` sits at the interior top level.
    have h0 : flowBracketBalance tokens (off + 1) a = 0 := by
      rw [h_int_bal] at h_comp; omega
    -- the opener at `a-1` composes to `balance (off+1) (a-1) = -1`, contradicting the floor.
    have h_comp2 : flowBracketBalance tokens (off + 1) a
        = flowBracketBalance tokens (off + 1) (a - 1) + flowBracketBalance tokens (a - 1) a :=
      flowBracketBalance_compose tokens (off + 1) (a - 1) a (by omega) (by omega)
    have h_int_a1 : flowBracketBalance tokens (off + 1) (a - 1) ≥ 0 :=
      h_int_floor (a - 1) (by omega) (by omega)
    rw [h_open, h0] at h_comp2
    omega

/-- **The DESCEND disjunct of the locator's per-window step `h_step`, through the guard structure** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-hstep-descend)`, R369.  The second `move_trichotomy`
    arm (`off + 1 < a < off + L`, `L = e.length`): the FIXED target window `[a, b)` lands strictly
    INSIDE the walking head entry, which is a SEQ block `op :: (interior ++ [cl])`, so the recursion
    DESCENDS into that interior and re-bundles `G` at the descended window `(off+1, off+1+interior.length,
    interior)`.  This is the pure-plumbing assembly the R368 work left: the analytical field `win_hi`
    (`b < off+1+interior.length`) discharges via `seqTarget_close_lt_interiorEnd` (R368) against the
    carried `opener`/`typed` + the head interior's `WellBracketed`-sourced balance/floor; every other
    field is mechanical or a window-absolute pass-through.

    Field sourcing at `(off+1, off+1+interior.length, interior)`:
    * `domain`/`slice` — from `nestedSeq_recseqentry_locate_descend_step` (R361, the descend seam:
      slice re-base `▸` `seqPathAllSeq_descend`), fed the guard's frame + `h_off_open` + `h_prefix`;
    * `recBody` — the head SEQ entry's stored `RecSeqBody interior` (`seq.h_rec`, threaded as `h_rec_int`);
    * `typed`/`close`/`opener`/`win_ab` — WINDOW-ABSOLUTE (keyed on the FIXED `[a,b]`/`a-1`), PASS
      THROUGH the descent UNCHANGED;
    * `bound`/`Hsz`/`win_lo` — `omega` from the frame + the descend bounds (`win_lo : off+2 ≤ a` is the
      arm's `off+1 < a`);
    * `win_hi` — `seqTarget_close_lt_interiorEnd` (R368) at `c = off+1+interior.length`, whose
      `h_int_bal`/`h_int_floor` are the head interior's Dyck balance + floor TRANSPORTED into `tokens`
      coordinates from `h_wb : WellBracketed interior` via the descend slice (`flowBracketBalance_eq_pbalance`
      + the `List.drop_take` slice commutation), `h_open` = the carried `opener`, `h_gate` = the carried
      `typed`.

    The shrink witness is `interior.length < body.length` (`body = (op :: interior ++ [cl]) ++ rest` ⇒
    `body.length = interior.length + 2 + rest.length`) — the single measure both recursive arms feed the
    `seqLocateRecDriver`.  The head opener type `tokens[off]! = [` is taken as a hypothesis IDENTICALLY to
    the LEAF/seam arms (the skeleton supplies it from the same `cases e` `.seq` decomposition).  The
    map-head sub-case is REFUTED upstream by the dispatch (`seqPathAllSeq_map_frame_persists`, R360) before
    this arm fires, so only the seq-head shape reaches here.  Verified-but-unconsumed until the skeleton
    wires `h_step`; references no sorry site, frontier sorry count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_step_descend
    (tokens : Array (Positioned YamlToken)) (a b off H : Nat)
    (body rest interior : List (Positioned YamlToken))
    (op cl : Positioned YamlToken)
    (g : SeqLocateGuard tokens a b off H body)
    (h_prefix : body = (op :: (interior ++ [cl])) ++ rest)
    (h_off_open : tokens[off]!.val = .flowSequenceStart)
    (h_wb : WellBracketed interior)
    (h_rec_int : RecSeqBody interior)
    (h_desc_lo : off + 1 < a)
    (h_desc_hi : a < off + interior.length + 2) :
    ∃ off' H' body', body'.length < body.length ∧
      SeqLocateGuard tokens a b off' H' body' := by
  -- descend seam: re-establish the slice + domain at the descended base `off+1`.
  obtain ⟨h_slice', h_domain'⟩ :=
    nestedSeq_recseqentry_locate_descend_step tokens body rest interior op cl off H
      g.slice g.bound g.Hsz h_prefix h_off_open g.domain
  -- body length, for the shrink measure and the descended `Hsz`.
  have hblen : body.length = interior.length + 2 + rest.length := by
    rw [h_prefix]; simp only [List.length_append, List.length_cons, List.length_nil]
  have h_Hsz' : off + 1 + interior.length ≤ tokens.size := by
    have hb := g.bound; have hh := g.Hsz; omega
  -- interior balance + floor in `tokens` coordinates, transported from `WellBracketed interior` via the
  -- descend slice (the `[off+1, off+1+interior.length)` window IS `interior`).  R373 (BRICK A) extracted
  -- this head-shape-BLIND transport from here so the map-head refutation reuses it; now CONSUMED.
  obtain ⟨h_int_bal, h_int_floor⟩ :=
    recseqentry_head_interior_floor_tokens tokens body rest interior op cl off H
      g.slice g.bound h_prefix h_wb
  -- the lone analytical field: the strict close-containment (R368), needing the carried opener.
  have h_win_hi : b < off + 1 + interior.length :=
    seqTarget_close_lt_interiorEnd tokens a b off (off + 1 + interior.length)
      (by omega) (by omega) h_int_bal h_int_floor g.opener g.typed
  -- the WALKING-keyed `window` field RE-ESTABLISHED at the descended interior `[off+1, off+1+|interior|)`:
  -- a balanced descend sub-window of the carried parent `g.window`, so `WellTyped_subrange` transports
  -- its typed fact down (the type-blind balance licenses the transport); the bounds are `omega` and the
  -- balance/floor are the same `h_int_bal`/`h_int_floor` the `win_hi` brick already needed.
  have h_window' : FlowBodyWindow tokens (off + 1) (off + 1 + interior.length) :=
    { lo_ge := by have := g.window.lo_ge; omega
      lo_lt_hi := by omega
      hi_le := by have := g.window.hi_le; have := g.bound; omega
      hi_lt := by have := g.window.hi_le; have := g.bound; omega
      balanced := h_int_bal
      dyck := h_int_floor
      wellTyped := WellTyped_subrange tokens off (off + 1) (off + 1 + interior.length) H
        (by omega) (by omega) (by have := g.bound; omega) g.Hsz g.window.wellTyped h_int_bal h_int_floor }
  exact ⟨off + 1, off + 1 + interior.length, interior, by omega,
    { domain := h_domain'
      recBody := h_rec_int
      slice := h_slice'
      bound := by omega
      Hsz := h_Hsz'
      typed := g.typed
      close := g.close
      opener := g.opener
      path := g.path
      win_lo := by omega
      win_ab := g.win_ab
      win_hi := h_win_hi
      window := h_window' }⟩

/-- **The seq-head ADVANCE re-bundle of the emission-spine-walk locator's per-window step** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-hstep-advance)`, R371, the LAST arm re-bundle before
    the `Nat.strongRecOn` skeleton wires `h_step`.  The third `move_trichotomy` arm (`off + e.length < a`,
    the target window start lands strictly PAST the head entry-plus-separator block): re-bundle
    `SeqLocateGuard` at the advanced window `(off + e.length + 1, H, rest)`.  domain/slice from the ADVANCE
    seam `nestedSeq_recseqentry_locate_advance_step` (R362), recBody from the tail's `RecSeqBody rest`
    (`cons.h_rest`), and — UNLIKE DESCEND — the right cut `H` is UNCHANGED, so `Hsz`/`win_hi` and the
    window-ABSOLUTE `typed`/`close`/`opener`/`win_ab` all PASS THROUGH `g` verbatim; `bound` is `omega`.

    Two fields are real work.  **`win_lo`** (`off + e.length + 2 ≤ a`): the arm condition gives only
    `off + e.length + 1 ≤ a`, and the boundary `a = off + e.length + 1` is admitted by the arm yet violates
    `win_lo` — it is EXCLUDED by the carried `g.opener`, because at that `a` the position `a - 1 =
    off + e.length` is the depth-`0` `.flowEntry` separator (`flowBracketBalance (a-1) a = 0`),
    contradicting `opener : flowBracketBalance (a-1) a = 1` (the DESCEND analogue of `win_hi`'s
    `seqTarget_close_lt_interiorEnd` discriminator).  **The walking-keyed `window`** (R370,
    [[ref-additive-field-cost-by-keying]]) is RE-ESTABLISHED, not passed through: the advanced
    `FlowBodyWindow tokens (off+e.length+1) H` comes from `flowBodyWindow_advance` re-framing `g.window`
    across the consumed entry-plus-separator — its depth-`0` cut `flowBracketBalance off (off+e.length) = 0`
    is the entry balance (`…advance_balance` R364's `flowBracketBalance off (off+e.length+1) = 0` minus the
    separator delta `0`) and its separator type is `h_sep_pos`.  That same R364 cut also feeds
    `…advance_welltyped` (R363, reading `g.window`) for the seam's threaded `WellTyped (e ++ [fe])`, so
    `g.window` is the joint source of BOTH the advance seam's `WellTyped` input AND the advanced `window`.

    With this all three arm re-bundles (LEAF R367, DESCEND R369, ADVANCE R371) exist ⇒ the skeleton can
    wire `h_step` (dispatch `recseqbody_head_or_cons` + `move_trichotomy` → the three arm steps),
    instantiate `seqLocateRecDriver`, and the locator `nestedSeq_recseqentry_locate` lands.  Verified-but-
    unconsumed until the skeleton wires it; references no sorry site, frontier sorry count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_step_advance
    (tokens : Array (Positioned YamlToken)) (a b off H : Nat)
    (body rest e : List (Positioned YamlToken))
    (fe : Positioned YamlToken)
    (g : SeqLocateGuard tokens a b off H body)
    (h_prefix : body = e ++ fe :: rest)
    (h_e : RecSeqEntry e)
    (h_fe : fe.val = .flowEntry)
    (h_rec_rest : RecSeqBody rest)
    (h_sep_pos : tokens[off + e.length]!.val = .flowEntry)
    (h_adv : off + e.length < a) :
    ∃ off' H' body', body'.length < body.length ∧
      SeqLocateGuard tokens a b off' H' body' := by
  have hbound := g.bound
  have hblen : body.length = e.length + 1 + rest.length := by
    rw [h_prefix]; simp only [List.length_append, List.length_cons]; omega
  -- the separator sits inside the array (needed for the single-token depth read).
  have h_m_sz : off + e.length < tokens.size := by have := g.Hsz; omega
  have h_m_len : off + e.length < tokens.toList.length := by
    rw [Array.length_toList]; exact h_m_sz
  have h_tok_m : tokens.toList[off + e.length]'h_m_len = tokens[off + e.length]! := by
    rw [getElem!_pos tokens (off + e.length) h_m_sz, Array.getElem_toList]
  -- the separator token is depth-`0`: its single-token balance is `flowBracketDelta .flowEntry = 0`.
  have h_sep_bal : flowBracketBalance tokens (off + e.length) (off + e.length + 1) = 0 := by
    rw [flowBracketBalance_single tokens (off + e.length) h_m_len, h_tok_m, h_sep_pos]
    exact flowBracketDelta_flowEntry
  -- ADVANCE seam chain: balance-`0` cut (R364) ▸ WellTyped supplier (R363) ▸ slice+domain re-base (R362).
  have h_bal0 : flowBracketBalance tokens off (off + e.length + 1) = 0 :=
    nestedSeq_recseqentry_locate_advance_balance tokens body rest e fe off H
      g.slice g.bound h_prefix h_e h_fe
  have h_wt_seg : WellTyped (e ++ [fe]) :=
    nestedSeq_recseqentry_locate_advance_welltyped tokens body rest e fe off H
      g.slice g.bound h_prefix g.window h_bal0
  obtain ⟨h_slice', h_domain'⟩ :=
    nestedSeq_recseqentry_locate_advance_step tokens body rest e fe off H
      g.slice g.bound h_prefix g.domain h_wt_seg
  -- `win_lo`: the boundary `a = off+e.length+1` is admitted by the arm but EXCLUDED by `g.opener` (at
  -- that `a`, `a-1` is the depth-`0` separator, so `flowBracketBalance (a-1) a = 0 ≠ 1`).
  have h_ne_boundary : a ≠ off + e.length + 1 := by
    intro h_a
    have hop := g.opener
    rw [h_a] at hop
    have harith : off + e.length + 1 - 1 = off + e.length := by omega
    rw [harith, h_sep_bal] at hop
    omega
  have h_win_lo : off + e.length + 2 ≤ a := by omega
  -- the WALKING-keyed `window` RE-ESTABLISHED at `[off+e.length+1, H)` via `flowBodyWindow_advance`:
  -- its cut `flowBracketBalance off (off+e.length) = 0` is `h_bal0` minus the depth-`0` separator delta.
  have h_m_bal : flowBracketBalance tokens off (off + e.length) = 0 := by
    have h_comp := flowBracketBalance_compose tokens off (off + e.length) (off + e.length + 1)
      (by omega) (by omega)
    rw [h_bal0, h_sep_bal] at h_comp
    omega
  have h_window' : FlowBodyWindow tokens (off + e.length + 1) H :=
    flowBodyWindow_advance tokens off (off + e.length) H g.window (by omega)
      (by have := g.win_ab; have := g.win_hi; omega) h_m_bal h_sep_pos
  exact ⟨off + e.length + 1, H, rest, by omega,
    { domain := h_domain'
      recBody := h_rec_rest
      slice := h_slice'
      bound := by omega
      Hsz := g.Hsz
      typed := g.typed
      close := g.close
      opener := g.opener
      path := g.path
      win_lo := h_win_lo
      win_ab := g.win_ab
      win_hi := g.win_hi
      window := h_window' }⟩

/-- **The locator skeleton's HEAD positional bridge** — `(i'-b-B2c-nested-fbc-emission-locator-
    skeleton-head-bridge)`, R372.  The walking body's head element sits at token position `off`:
    given the slice frame (`h_slice`/`h_bound`/`h_Hsz`) and a head decomposition `body = x :: xs`,
    `tokens[off]! = x`.  This is the first of the two residual POSITIONAL BRIDGES the skeleton's
    `h_step` dispatch needs (the SMALLEST-FIRST wrapper work the blueprint queued): the LEAF/DESCEND
    arms take `tokens[off]! = .flowSequenceStart` as a hypothesis, which the skeleton supplies by this
    bridge ▸ the seq-entry head's `op.val = .flowSequenceStart` (read off `recseqbody_head_or_cons`'s
    `RecSeqEntry e` in the seq case).  Proof: the slice `[off, H)` opens with `x` (`h_slice ▸ h_cons`),
    so the option-indexed `((take H).drop off)[0]? = some x` transports through `getElem?_drop` +
    `getElem?_take` (the `off < H` guard from `h_bound` + the nonempty body) to `tokens.toList[off]? =
    some x`, then `getElem?_eq_getElem` + the `tokens[off]!`/`tokens.toList[off]` array-list bridge
    (`getElem!_pos` + `Array.getElem_toList`) close it.  Pure positional plumbing — no guard fields, no
    grammar; references no sorry site, frontier sorry count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_head_pos
    (tokens : Array (Positioned YamlToken))
    (body xs : List (Positioned YamlToken)) (x : Positioned YamlToken)
    (off H : Nat)
    (h_slice : body = (tokens.toList.take H).drop off)
    (h_bound : off + body.length ≤ H)
    (h_Hsz : H ≤ tokens.size)
    (h_cons : body = x :: xs) :
    tokens[off]! = x := by
  have h_pos : 0 < body.length := by rw [h_cons]; simp
  have h_off_sz : off < tokens.size := by omega
  have h_off_len : off < tokens.toList.length := by rw [Array.length_toList]; exact h_off_sz
  have h_eq : (tokens.toList.take H).drop off = x :: xs := by rw [← h_slice]; exact h_cons
  have h_getq : tokens.toList[off]? = some x := by
    have hc : ((tokens.toList.take H).drop off)[0]? = some x := by rw [h_eq]; rfl
    rw [List.getElem?_drop, List.getElem?_take, Nat.add_zero, if_pos (by omega : off < H)] at hc
    exact hc
  have h_elem : tokens.toList[off]'h_off_len = x := by
    have := List.getElem?_eq_getElem h_off_len
    rw [h_getq] at this
    exact (Option.some.inj this).symm
  rw [getElem!_pos tokens off h_off_sz, ← Array.getElem_toList]
  exact h_elem

/-- **The locator skeleton's SEPARATOR positional bridge** — `(i'-b-B2c-nested-fbc-emission-locator-
    skeleton-sep-bridge)`, R372, the second residual positional bridge.  When the walking body is a
    `cons` `body = e ++ fe :: rest`, the inter-entry separator `fe` sits at token position
    `off + e.length`: `tokens[off + e.length]! = fe`.  This supplies the ADVANCE arm's
    `h_sep_pos : tokens[off + e.length]!.val = .flowEntry` hypothesis (▸ `recseqbody_head_or_cons`'s
    `cons.h_fe : fe.val = .flowEntry`).  Same `getElem?`-transport skeleton as the head bridge, with the
    index `e.length` located in `e ++ fe :: rest` by `getElem?_append_right (Nat.le_refl e.length)` +
    `Nat.sub_self` (the separator is the FIRST element past the entry block) and the `off + e.length < H`
    guard from the cons length `body.length = e.length + 1 + rest.length` + `h_bound`.  Pure positional
    plumbing; references no sorry site, frontier sorry count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_sep_pos
    (tokens : Array (Positioned YamlToken))
    (body rest e : List (Positioned YamlToken)) (fe : Positioned YamlToken)
    (off H : Nat)
    (h_slice : body = (tokens.toList.take H).drop off)
    (h_bound : off + body.length ≤ H)
    (h_Hsz : H ≤ tokens.size)
    (h_prefix : body = e ++ fe :: rest) :
    tokens[off + e.length]! = fe := by
  have h_blen : body.length = e.length + 1 + rest.length := by
    rw [h_prefix, List.length_append, List.length_cons]; omega
  have h_m_sz : off + e.length < tokens.size := by omega
  have h_m_len : off + e.length < tokens.toList.length := by
    rw [Array.length_toList]; exact h_m_sz
  have h_eq : (tokens.toList.take H).drop off = e ++ fe :: rest := by rw [← h_slice]; exact h_prefix
  have h_getq : tokens.toList[off + e.length]? = some fe := by
    have hc : ((tokens.toList.take H).drop off)[e.length]? = some fe := by
      rw [h_eq, List.getElem?_append_right (Nat.le_refl e.length), Nat.sub_self]; rfl
    rw [List.getElem?_drop, List.getElem?_take, if_pos (by omega : off + e.length < H)] at hc
    exact hc
  have h_elem : tokens.toList[off + e.length]'h_m_len = fe := by
    have := List.getElem?_eq_getElem h_m_len
    rw [h_getq] at this
    exact (Option.some.inj this).symm
  rw [getElem!_pos tokens (off + e.length) h_m_sz, ← Array.getElem_toList]
  exact h_elem

/-- **The emission-spine-walk locator's `Nat.strongRecOn` DRIVER** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton)`, R365, the SMALLEST-FIRST plumbing de-risk of the
    skeleton `nestedSeq_recseqentry_locate`.  Before wiring the whole recursion (dispatch + three arm
    seams + guard threading) the blueprint's next-step posed the plumbing question in isolation: does the
    `Nat.strongRecOn`-on-`body.length` measure + IH interface each arm's recursive call needs typecheck,
    BEFORE the arm bodies are filled?  This is that interface, abstracted as a P/G combinator
    ([[ref-width-recursion-combinator-before-grammar-step]]): the per-window STEP is the abstract
    hypothesis `h_step`, the grammar-free `Nat.strongRecOn` plumbing is the proof.

    `Q` is the FIXED deliverable (the located-entry existential — it mentions only the target window
    `[a,b)` + `tokens`, never the recursion's walking `off`/`H`/`body`, so it is a constant across the
    walk).  `G off H body` is the per-window GUARD the skeleton will instantiate to its bundle
    (`SeqPathAllSeq tokens off` ∧ the four-conjunct `FlowBodyWindow ∧ FlowBodyContentDeep ∧ SeqEnclosed ∧
    close` ∧ `RecSeqBody body` ∧ the slice/window facts relating `a` to `[off,H)`).  `h_step` says: at any
    guarded window, EITHER we are at a leaf (produce `Q` directly — the LEAF arm,
    `nestedSeq_recseqentry_locate_leaf_full`) OR there is a strictly-SMALLER sub-window still in the guard
    (the DESCEND arm re-bundles `G` at `(off+1, off+1+interior.length, interior)` via
    `nestedSeq_recseqentry_locate_descend_step`; the ADVANCE arm re-bundles at `(off+e.length+1, H, rest)`
    via `…advance_balance` → `…advance_welltyped` → `…advance_step`).  BOTH recursive positions hand back a
    `body'` with `body'.length < body.length` — the single measure the whole recursion rests on; this
    combinator confirms that one measure suffices for both arms (DESCEND: `interior.length < body.length`
    since `body = (op :: interior ++ [cl]) ++ rest`; ADVANCE: `rest.length < body.length` since
    `body = e ++ fe :: rest`), pinning the IH interface independent of WHICH arm fired.

    The dispatch's three-way EXHAUSTIVENESS is the orthogonal, already-landed
    `SeqNestedEntryLocateProbe.move_trichotomy` (R350, pure `omega`); this driver supplies the MEASURE.
    Together they are the skeleton's complete plumbing.  Verified-but-unconsumed until the skeleton fills
    `h_step` from `move_trichotomy` + the arm seams; references no sorry site, frontier sorry count
    unchanged at 4. -/
theorem seqLocateRecDriver {Q : Prop}
    (G : Nat → Nat → List (Positioned YamlToken) → Prop)
    (h_step : ∀ off H body, G off H body →
        Q ∨ (∃ off' H' body', body'.length < body.length ∧ G off' H' body'))
    (off H : Nat) (body : List (Positioned YamlToken)) (h_g : G off H body) : Q := by
  suffices h : ∀ n off H body, body.length = n → G off H body → Q from
    h body.length off H body rfl h_g
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro off H body h_len h_g
    rcases h_step off H body h_g with hq | ⟨off', H', body', h_lt, h_g'⟩
    · exact hq
    · exact IH body'.length (by omega) off' H' body' rfl h_g'

/-- **`SeqPathAllSeq` dominates `SeqEnclosed`** — the all-`true` path stack has TOP `true`, so the
    navigator's domain hypothesis is STRICTLY STRONGER than the immediate-enclosure fact the dispatch
    (`seqWindow_flowBodyContent`) consumes.  Lets the domain-restricted driver supply the dispatch's
    `SeqEnclosed` for free from its carried `SeqPathAllSeq`, with no separate threading. -/
theorem seqEnclosed_of_seqPathAllSeq (tokens : Array (Positioned YamlToken)) (lo : Nat)
    (h : SeqPathAllSeq tokens lo) :
    SeqEnclosed tokens lo := by
  obtain ⟨s, h_fold, h_ne, h_all⟩ := h
  unfold SeqEnclosed
  rw [h_fold]
  cases s with
  | nil => exact absurd rfl h_ne
  | cons a t =>
    cases a with
    | false => simp at h_all
    | true => rfl

/-- **The consumer's GATE already supplies the producer's enclosure need** — `(i'-b-B2c-map-path)`,
    the de-risk that DISSOLVES the all-seq/map-path partition (Reflection 339).

    `SeqTypedInterior tokens a b` (the gate `seqInteriorSeparators_of_safebody_provider`'s `provider`
    quantifies under) has, as its SECOND conjunct, `(btFold (some []) (tokens.toList.take a)).bind
    (·.head?) = some true` — which is *definitionally* `SeqEnclosed tokens a`.  So the producer
    `seqWindowRecSeqBody`'s only path-sensitive hypothesis (`SeqEnclosed`) is handed to it FREE by the
    very gate the consumer threads, IDENTICALLY for every gated window — whether its path to the root
    runs through all `[` (all-seq) or dips through a `{` (map-path).

    This is the [[ref-conjunct-of-projection-is-free-field]] move at the gate, and it completes the
    [[ref-probe-provider-satisfiable-before-assembler]] / [[ref-probe-provider-head-blind-gate]]
    conclusion that the planned **flat map-path complement provider is UNNECESSARY** and the routing
    tag `SeqPathAllSeq` is **vestigial**: `SeqEnclosed` reads only the TOP of `take a` (the window's
    own `[`, `true` for every seq body), so it is PATH-INVARIANT; the deeper map-vs-seq distinction
    `SeqPathAllSeq` tracks is never read by the producer (whose sole descend edge fires on
    `.flowSequenceStart`, STOPPING at map leaves — R338, [[ref-producer-stops-at-severed-edge]]).  The
    map-path-nested seq windows the partition was built to route are never reached by the recursion;
    the same producer serves the whole gated domain through this one free conjunct. -/
theorem seqEnclosed_of_seqTypedInterior (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h : SeqTypedInterior tokens a b) :
    SeqEnclosed tokens a :=
  h.2.1

/-- **`SeqEnclosed` at a backward-LOCATED enclosing opener** — `(i'-b-B2c-desc-closing)` sub-brick 2a,
    the `h_q_succ` supplier for the `desc` discharge's `seqDescent_provider_of_located` call.

    `seqDescent_provider_of_located` consumes `Q (p+1)` as its IH's seed `h_q_succ`; instantiated at
    `Q := SeqEnclosed tokens`, that is `SeqEnclosed tokens (p+1)` at the backward-located enclosing
    opener `p < a` — **not** `SeqEnclosed p`.  This is the de-risk's first finding: the consumer reads
    the POST-opener stack-top (the enclosing seq body starts at `p+1`), so the `+1` form is what is
    owed, and it needs no `SeqEnclosed p` threaded down as an extra locator output.

    It is the consume-site dual of `seqEnclosed_descend`: that DESCEND edge pushes the window HEAD
    `tokens[lo]` (an opener already in scope at the recursion) and takes its `.flowSequenceStart` type
    as a hypothesis; here the opener `p` is recovered by the backward locator
    (`seqEnclosingOpener_of_gate`) and its `.flowSequenceStart` type is PROVEN from the gate by
    `seqOpenerType_of_located_and_gate`, so the only inputs are the four locator facts plus the gate's
    mark.  The enclosure is reconstructed in place ([[ref-reconstruct-in-place-over-relocate]] /
    [[ref-prefix-gate-reconstructed-from-boundary]]): the gate's `btFold`-top `= some true` after
    `[0,a)` makes the whole `take a` fold `some S`, hence its prefix `take p` folds to `some s`
    (`btFold_some_prefix`), and a `.flowSequenceStart` at `p` pushes `true`
    (`enclosingMark_true_of_opener`) — exactly `SeqEnclosed (p+1)`.

    So the `desc` discharge owes NO `SeqEnclosed p`: the post-opener enclosure is sourced from the gate
    and the located-opener type alone.  Verified-but-unconsumed until the `desc` driver (B2b — the
    carrier↔producer width recursion R317 flagged) lands: composes only landed lemmas, references no
    sorry site, frontier sorry count unchanged at 4. -/
theorem seqEnclosed_succ_of_located_opener
    (tokens : Array (Positioned YamlToken)) (a p : Nat)
    (h_pa : p < a) (h_a_sz : a ≤ tokens.size)
    (h_delta : flowBracketDelta tokens[p]!.val = 1)
    (h_bal : flowBracketBalance tokens (p + 1) a = 0)
    (h_floor : ∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0)
    (h_mark : (btFold (some []) (tokens.toList.take a)).bind (·.head?) = some true) :
    SeqEnclosed tokens (p + 1) := by
  have h_p_sz : p < tokens.size := by omega
  -- the located opener is a `.flowSequenceStart` (from the gate's mark + the locator floor).
  have h_open : tokens[p]!.val = .flowSequenceStart :=
    seqOpenerType_of_located_and_gate tokens a p h_pa h_a_sz h_delta h_bal h_floor h_mark
  -- the gate makes the whole `take a` fold `some S`, hence its prefix `take p` folds to `some s`.
  obtain ⟨S, hS⟩ : ∃ S, btFold (some []) (tokens.toList.take a) = some S := by
    cases hc : btFold (some []) (tokens.toList.take a) with
    | none => rw [hc] at h_mark; simp at h_mark
    | some S => exact ⟨S, rfl⟩
  have h_split : tokens.toList.take a
      = tokens.toList.take p ++ (tokens.toList.drop p).take (a - p) := by
    rw [← List.take_add]; congr 1; omega
  obtain ⟨s, hs⟩ := btFold_some_prefix (tokens.toList.take p)
    ((tokens.toList.drop p).take (a - p)) S (by rw [← h_split]; exact hS)
  -- the opener pushes `true`, so the post-opener stack top is `true` = `SeqEnclosed (p+1)`.
  exact enclosingMark_true_of_opener tokens p h_p_sz s hs h_open

/-- **The WINDOW-LOCAL seq carrier reduced to the width supplier** — `(i'-b-B2c-(d) — STEP D)`, R446:
    the window-parametric generalization of `seqRoot_carrier_of_widthEnc` (below).  Produces
    `SeqInteriorSeparators tokens lo hi` at an ARBITRARY seq window `[lo, hi)` — not just the root span
    `[2, size - 2)` — from a window-local `SafeBodyUnit` `h_safe` and a width supplier `h_widthEnc`
    re-based to `[lo, hi)`.  This is the LOCAL-CARRIER half (part (a)) of the R447 carrier↔recursion
    co-construction.

    **What was root-specific, and the one swap that generalizes it.**  `seqRoot_carrier_of_widthEnc`
    drove its `desc` through `seqRoot_seqInteriorSeparators`, which bakes in BOTH the literal span
    `lo = 2`, `hi = size - 2` AND the FLAT root `SafeBodyUnit` (`seqRoot_safeBodyUnit`, scanned straight
    off emission, no recursion).  That flat-`SafeBodyUnit` assembly is the ONLY root-specific part: the
    descent route it threads (`seqEnclosingOpener_of_gate` → `h_widthEnc` →
    `seqEnclosed_succ_of_located_opener` → `seqDescent_provider_of_located`) is ALREADY
    window-parametric — every lemma in it takes the window bounds `a`/`b`/`p`/`hi` as arguments and
    none reads the literal `2`/`size - 2`.  So the generalization is exactly one swap: replace the root
    assembler `seqRoot_seqInteriorSeparators` with the window-parametric
    `seqInteriorSeparators_of_safebody_and_descent`, LIFTING the window's `SafeBodyUnit` as the
    hypothesis `h_safe` ([[ref-parametric-assembler-extraction]] /
    [[ref-additive-parallel-type-over-shared-edit]]), and re-base `h_widthEnc`'s bounds from
    `[2, size - 2)` to `[lo, hi)`.  The proof body is otherwise term-for-term
    `seqRoot_carrier_of_widthEnc`'s — and `seqRoot_carrier_of_widthEnc` becomes the thin `lo := 2`,
    `hi := size - 2` instance, fed `seqRoot_safeBodyUnit` for `h_safe`.

    **Why it is the co-construction's part (a).**  The R447 joint width induction (the last seq
    residual) produces, per seq window `[lo, hi)`, the pair
    `SeqInteriorSeparators tokens lo hi ∧ RecSeqBody ((take hi).drop lo)`.  This brick is its local
    carrier half: it builds `SeqInteriorSeparators tokens lo hi` given (i) that window's own
    `SafeBodyUnit` — from `RecSeqBody.toSafeBodyUnit` of the window's own body, the recursion's output
    at `[lo, hi)` — and (ii) `h_widthEnc`, the enclosing-facts + strictly-narrower `RecSeqBody`-IH
    supplier the joint IH discharges.  Every gated sub-window `[a, b) ⊂ [lo, hi)` the carrier descends
    into is STRICTLY narrower than `[lo, hi)` (`#guard`-backed, `SeqLocalCarrierWidthProbe`): the only
    place a `RecSeqBody`-IH is genuinely consumed is `seqChild_safeBodyUnit`, at the located genuine
    seq child body `[p + 1, j) ⊂ [lo, hi)`, gated `hi' - lo' < hi_E - p` — and even on `[[1, 2], 9]`,
    where the enclosing window `[p, hi_E) = [2, 9) = [lo, hi)` itself (the self-instantiation the task
    flagged), the IH callee `[3, 6)` has width `3 < 7`, so the joint width IH covers it with no
    circular self-call.

    Verified-but-unconsumed until R447's joint induction discharges `h_widthEnc`: composes only landed
    lemmas, references no sorry site, frontier sorry count unchanged at 4; axiom-clean. -/
theorem seqLocalCarrier_of_widthEnc
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat) (h_hi : hi ≤ tokens.size)
    (h_safe : SafeBodyUnit ContentStartTok ((tokens.toList.take hi).drop lo))
    (h_widthEnc : ∀ a b p, lo ≤ a → a ≤ b → b ≤ hi →
        flowBracketBalance tokens lo a ≠ 0 →
        SeqTypedInterior tokens a b →
        p < a → flowBracketDelta tokens[p]!.val = 1 →
        flowBracketBalance tokens (p + 1) a = 0 →
        (∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) →
        ∃ hiE, b ≤ hiE ∧ hiE ≤ tokens.size ∧
          FlowBodyWindow tokens p hiE ∧ FlowBodyContentDeep tokens p hiE ∧
          FlowBodyContent tokens p hiE ∧
          (∀ lo' hi', hi' - lo' < hiE - p → p ≤ lo' → hi' ≤ hiE →
            FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' →
            SeqEnclosed tokens lo' → tokens[hi']!.val = .flowSequenceEnd →
            RecSeqBody ((tokens.toList.take hi').drop lo'))) :
    SeqInteriorSeparators tokens lo hi := by
  apply seqInteriorSeparators_of_safebody_and_descent tokens lo hi h_hi h_safe
  intro a b ha hab hb _hbal hgate
  have h_a_sz : a ≤ tokens.size := Nat.le_trans (Nat.le_trans hab hb) h_hi
  obtain ⟨p, h_pa, h_delta, h_body_bal, h_loc_floor⟩ :=
    seqEnclosingOpener_of_gate tokens a b h_a_sz hgate
  obtain ⟨hiE, h_b_hi, h_hiE_sz, h_window, h_deep, h_content, h_ih⟩ :=
    h_widthEnc a b p ha hab hb _hbal hgate h_pa h_delta h_body_bal h_loc_floor
  have h_q_succ : SeqEnclosed tokens (p + 1) :=
    seqEnclosed_succ_of_located_opener tokens a p h_pa h_a_sz h_delta h_body_bal h_loc_floor hgate.2.1
  exact seqDescent_provider_of_located tokens a b p hiE h_pa hab h_b_hi h_delta h_body_bal
    h_loc_floor hgate h_window h_deep h_content (SeqEnclosed tokens) h_q_succ h_ih

/-- **The window-local seq carrier, `FlowBodyContentDeepSeq`-keyed** — `(i'-b-B2c-(d)-seq)`, R496:
    the `_seq`-family twin of `seqLocalCarrier_of_widthEnc` (above), the consumer-chain link ABOVE the
    descent provider in the `_seq` re-thread ([[ref-rethread-stays-in-weaker-twin-family]]).  It produces
    the SAME local carrier `SeqInteriorSeparators tokens lo hi` from a window-local `SafeBodyUnit` and a
    width supplier `h_widthEnc` whose enclosing-window + IH deep facts are re-keyed onto the root-TRUE
    `FlowBodyContentDeepSeq`.

    **A CLEAN lift — the climb has been ABSORBED below.**  By [[ref-lift-rekeys-by-guard-keyed-child-names]]
    (R493) a transporting LIFT's re-key cost is one NAME swap per guard-KEYED child it invokes.  Here the
    descent route threads three children: `seqEnclosingOpener_of_gate` (LOCATE — reads only the gate, no
    deep field, guard-NEUTRAL), `seqEnclosed_succ_of_located_opener` (the `SeqEnclosed (p+1)` IH seed —
    gate + opener-type only, guard-NEUTRAL), and `seqDescent_provider_of_located` (the lone guard-KEYED
    child).  So the body is a single swap `seqDescent_provider_of_located ↦ _seq`, and the signature
    re-keys `h_widthEnc`'s two `FlowBodyContentDeep` occurrences (the enclosing-window fact and the inner
    IH premise) to `FlowBodyContentDeepSeq` — supplied by the producer side (R493) re-keyed to match.

    **The climbing premise does NOT re-emerge here.**  R494 ([[ref-dropped-derivation-premise-climbs-lift-chain]])
    showed the non-emptiness premise `h_ne` CLIMBED the lift chain because the leaf could not source it,
    and R495 ([[ref-climbing-premise-terminates-at-case-split]]) showed it TERMINATED one level below — at
    `seqDescent_provider_of_located_seq`, which case-splits on `p + 1 < j` and self-handles the degenerate
    empty-seq window the weaker guard admits.  That terminus is an ABSORPTION boundary: its conclusion is
    premise-FREE (it produces the descent existential UNCONDITIONALLY, having internalised the case split),
    so THIS lift sees a clean premise-free interface — NO `h_ne` to forward, NO case split to restore.  The
    lift reverts to the pure R493 form, confirming R495's "Next step" prediction that the terminus restores
    a clean interface upward.  The whole proof body is therefore term-for-term `seqLocalCarrier_of_widthEnc`
    with the single descent-name swap ([[ref-transporting-lemma-twin-zero-body-edits]]).

    Verified-but-unconsumed until R447's joint induction (the `_seq` side) discharges `h_widthEnc`:
    composes only landed lemmas (the R495 descent twin), references no sorry site, frontier sorry count
    unchanged at 4; axiom-clean. -/
theorem seqLocalCarrier_of_widthEnc_seq
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat) (h_hi : hi ≤ tokens.size)
    (h_safe : SafeBodyUnit ContentStartTok ((tokens.toList.take hi).drop lo))
    (h_widthEnc : ∀ a b p, lo ≤ a → a ≤ b → b ≤ hi →
        flowBracketBalance tokens lo a ≠ 0 →
        SeqTypedInterior tokens a b →
        p < a → flowBracketDelta tokens[p]!.val = 1 →
        flowBracketBalance tokens (p + 1) a = 0 →
        (∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) →
        ∃ hiE, b ≤ hiE ∧ hiE ≤ tokens.size ∧
          FlowBodyWindow tokens p hiE ∧ FlowBodyContentDeepSeq tokens p hiE ∧
          FlowBodyContent tokens p hiE ∧
          (∀ lo' hi', hi' - lo' < hiE - p → p ≤ lo' → hi' ≤ hiE →
            FlowBodyWindow tokens lo' hi' → FlowBodyContentDeepSeq tokens lo' hi' →
            SeqEnclosed tokens lo' → tokens[hi']!.val = .flowSequenceEnd →
            RecSeqBody ((tokens.toList.take hi').drop lo'))) :
    SeqInteriorSeparators tokens lo hi := by
  apply seqInteriorSeparators_of_safebody_and_descent tokens lo hi h_hi h_safe
  intro a b ha hab hb _hbal hgate
  have h_a_sz : a ≤ tokens.size := Nat.le_trans (Nat.le_trans hab hb) h_hi
  obtain ⟨p, h_pa, h_delta, h_body_bal, h_loc_floor⟩ :=
    seqEnclosingOpener_of_gate tokens a b h_a_sz hgate
  obtain ⟨hiE, h_b_hi, h_hiE_sz, h_window, h_deep, h_content, h_ih⟩ :=
    h_widthEnc a b p ha hab hb _hbal hgate h_pa h_delta h_body_bal h_loc_floor
  have h_q_succ : SeqEnclosed tokens (p + 1) :=
    seqEnclosed_succ_of_located_opener tokens a p h_pa h_a_sz h_delta h_body_bal h_loc_floor hgate.2.1
  exact seqDescent_provider_of_located_seq tokens a b p hiE h_pa hab h_b_hi h_delta h_body_bal
    h_loc_floor hgate h_window h_deep h_content (SeqEnclosed tokens) h_q_succ h_ih

/-- **The seq ROOT CARRIER reduced to the width CO-CONSTRUCTION** — `(i'-b-B2c-(d) — STEP D)`, R443.
    Produces `SeqInteriorSeparators tokens 2 (tokens.size - 2)` (the root carrier
    `seqRoot_seqInteriorSeparators` builds from its `desc` argument) from a SINGLE residual hypothesis
    `h_widthEnc` — the per-window enclosing-facts + width-recursion IH supplier.

    **As of R446 this is the thin `lo := 2`, `hi := size - 2` instance of the window-parametric
    `seqLocalCarrier_of_widthEnc`** (above), fed the flat root `SafeBodyUnit` `seqRoot_safeBodyUnit`
    for the lifted `h_safe`.  The narrative below records the original standalone construction; the
    body now delegates, keeping this signature stable for its consumers
    ([[ref-additive-parallel-type-over-shared-edit]]).

    **This brick CORRECTS the stale "residual = LOCATE half" framing.**  The R442 blueprint Next step
    scoped `desc`'s genuine residual as the backward enclosing-opener LOCATE; reading the landed code
    shows the locate is ALREADY DONE (`seqEnclosingOpener_of_gate`, R319, term-for-term) and the assemble
    too (`seqDescent_provider_of_located`, the ASSEMBLE half).  This bridge composes both into the `desc`
    shape directly ([[ref-reduction-by-import]] / [[ref-fold-consumer-chain-to-producer-contract]]) — for
    each gated window `[a,b)` it (1) LOCATES the enclosing opener `p` from the gate
    (`seqEnclosingOpener_of_gate`), (2) DISCHARGES the descent IH seed `SeqEnclosed (p+1)` from the gate's
    own mark + the located-opener type (`seqEnclosed_succ_of_located_opener`, so `h_widthEnc` need NOT
    supply it — [[ref-conjunct-of-projection-is-free-field]]), (3) DRAWS the enclosing window `[p, hi)`'s
    `FlowBodyWindow`/`Deep`/`Content` and the width IH from `h_widthEnc`, and (4) ASSEMBLES via
    `seqDescent_provider_of_located`.  So the genuine residual is `h_widthEnc`, NOT the locate; the
    `flowBracketBalance tokens 2 a ≠ 0` failed-root discriminator `desc` carries is UNUSED on the gate
    route (the gate alone gives positivity via `flowBracketBalance_pos_of_seqTypedInterior`).

    **`h_widthEnc`'s IH is term-for-term `seqWindowRecSeqBody` minus the root carrier, bounded by width.**
    Its body `FlowBodyWindow lo' hi' → FlowBodyContentDeep lo' hi' → SeqEnclosed lo' →
    tokens[hi']! = .flowSequenceEnd → RecSeqBody ((take hi').drop lo')` is EXACTLY
    `seqWindowRecSeqBody`'s signature (R323), gated by `hi' - lo' < hi - p`.  But `seqWindowRecSeqBody`
    consumes `h_root_carrier : SeqInteriorSeparators tokens 2 (size-2)` — the very carrier this brick is
    BUILDING.  So discharging `h_widthEnc` is the carrier↔recursion CO-CONSTRUCTION: a strong induction on
    window width producing the local carrier and `RecSeqBody` jointly, where the descent's enclosing
    window `[p, hi)` lies within the span and the IH covers its strictly-smaller sub-windows.  That
    co-construction — NOT the locate — is the last seq residual; this bridge names its exact interface.

    Verified-but-unconsumed until the co-construction discharges `h_widthEnc`: composes only landed
    lemmas, references no sorry site, frontier sorry count unchanged at 4; axiom-clean. -/
theorem seqRoot_carrier_of_widthEnc
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v)
    (h_widthEnc : ∀ a b p, 2 ≤ a → a ≤ b → b ≤ tokens.size - 2 →
        flowBracketBalance tokens 2 a ≠ 0 →
        SeqTypedInterior tokens a b →
        p < a → flowBracketDelta tokens[p]!.val = 1 →
        flowBracketBalance tokens (p + 1) a = 0 →
        (∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) →
        ∃ hi, b ≤ hi ∧ hi ≤ tokens.size ∧
          FlowBodyWindow tokens p hi ∧ FlowBodyContentDeep tokens p hi ∧
          FlowBodyContent tokens p hi ∧
          (∀ lo' hi', hi' - lo' < hi - p → p ≤ lo' → hi' ≤ hi →
            FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' →
            SeqEnclosed tokens lo' → tokens[hi']!.val = .flowSequenceEnd →
            RecSeqBody ((tokens.toList.take hi').drop lo'))) :
    SeqInteriorSeparators tokens 2 (tokens.size - 2) :=
  seqLocalCarrier_of_widthEnc tokens 2 (tokens.size - 2) (Nat.sub_le tokens.size 2)
    (seqRoot_safeBodyUnit items tokens h_scan h_ne h_all) h_widthEnc

/-- **The seq ROOT CARRIER, `FlowBodyContentDeepSeq`-keyed — the producer/consumer MEET** —
    `(i'-b-B2c-(d)-seq-root)`, R497: the `_seq`-family twin of `seqRoot_carrier_of_widthEnc` (above),
    the thin `lo := 2`, `hi := tokens.size - 2` instance of the now-re-keyed window-parametric
    `seqLocalCarrier_of_widthEnc_seq` (R496), fed the FLAT root `SafeBodyUnit` `seqRoot_safeBodyUnit`
    for `h_safe`.  Produces the SAME root carrier `SeqInteriorSeparators tokens 2 (tokens.size - 2)`
    from a single residual `h_widthEnc`, but with `h_widthEnc`'s enclosing-window + IH deep facts
    re-keyed onto the root-TRUE `FlowBodyContentDeepSeq` ([[ref-root-seed-needs-root-true-guard]] R488).

    **This brick is the MEET — where the re-threaded producer and consumer become ONE type.**  The
    whole `_seq` re-thread (R488→R496) existed to reconcile a TYPE MISMATCH at this very interface: the
    producer side (`seqWidthEnc_of_enclosingLocate_and_recIH_seq`, R492→R493) delivers an `h_widthEnc`
    whose enclosing-window + IH facts are keyed on `FlowBodyContentDeepSeq`, but the OLD consumer root
    carrier `seqRoot_carrier_of_widthEnc` (above) demanded an `h_widthEnc` keyed on the root-FALSE
    `FlowBodyContentDeep` — so the producer's deliverable could NOT plug into the consumer's slot.  This
    twin re-keys the consumer's hypothesis to `FlowBodyContentDeepSeq`, so the producer's `h_widthEnc`
    type and the consumer's `h_widthEnc` type now COINCIDE.  The re-thread's purpose was this
    reconciliation; the root seed is where the two types meet.

    **A thin-instance lift is the CHEAPEST link in a re-thread — it has no proof BODY.**  Unlike the
    window-parametric carrier (R496) or the descent provider (R495), the root carrier carries NO proof
    logic: its body is a SINGLE application of the window-parametric parent at `lo := 2`,
    `hi := size - 2`.  So its `_seq` cost is the degenerate floor of [[ref-lift-rekeys-by-guard-keyed-child-names]]
    (R493) / [[ref-transporting-lemma-twin-zero-body-edits]] (R492): exactly ONE guard-keyed child-name
    swap (`seqLocalCarrier_of_widthEnc ↦ seqLocalCarrier_of_widthEnc_seq`) and the guard re-key of the
    forwarded residual hypothesis `h_widthEnc` (its two `FlowBodyContentDeep` ⤳ `FlowBodyContentDeepSeq`).
    The guard-NEUTRAL instantiation arguments transport verbatim: the width bound `Nat.sub_le`, and the
    flat root `SafeBodyUnit` `seqRoot_safeBodyUnit` (content-guard-agnostic — it scans straight off
    emission, no `RecSeqBody`, so it is the SAME for either content guard).  There is nothing else to
    port; the body is term-for-term `seqRoot_carrier_of_widthEnc` with the single parent-name swap.

    Verified-but-unconsumed until the carrier↔recursion co-construction (`windowWidth_strongRecOn` over
    body width) supplies `h_widthEnc` for the `_seq` side: composes only landed lemmas (R496's
    re-keyed parent), references no sorry site, frontier sorry count unchanged at 4; axiom-clean. -/
theorem seqRoot_carrier_of_widthEnc_seq
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v)
    (h_widthEnc : ∀ a b p, 2 ≤ a → a ≤ b → b ≤ tokens.size - 2 →
        flowBracketBalance tokens 2 a ≠ 0 →
        SeqTypedInterior tokens a b →
        p < a → flowBracketDelta tokens[p]!.val = 1 →
        flowBracketBalance tokens (p + 1) a = 0 →
        (∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) →
        ∃ hi, b ≤ hi ∧ hi ≤ tokens.size ∧
          FlowBodyWindow tokens p hi ∧ FlowBodyContentDeepSeq tokens p hi ∧
          FlowBodyContent tokens p hi ∧
          (∀ lo' hi', hi' - lo' < hi - p → p ≤ lo' → hi' ≤ hi →
            FlowBodyWindow tokens lo' hi' → FlowBodyContentDeepSeq tokens lo' hi' →
            SeqEnclosed tokens lo' → tokens[hi']!.val = .flowSequenceEnd →
            RecSeqBody ((tokens.toList.take hi').drop lo'))) :
    SeqInteriorSeparators tokens 2 (tokens.size - 2) :=
  seqLocalCarrier_of_widthEnc_seq tokens 2 (tokens.size - 2) (Nat.sub_le tokens.size 2)
    (seqRoot_safeBodyUnit items tokens h_scan h_ne h_all) h_widthEnc

/-- **`h_widthEnc` ASSEMBLED from the enclosing-locate residual + the joint width IH** —
    `(i'-b-B2c-(d)-seq-widthEnc-assemble)`, R475: the per-step ASSEMBLE that the eventual body-width
    joint induction invokes to discharge `seqLocalCarrier_of_widthEnc`'s `h_widthEnc` hypothesis at
    one body window `[lo, hi)`.  It composes the two genuine residuals into the exact `h_widthEnc`
    shape, PROVING the width-descent wiring (the arithmetic R473
    [[ref-dropped-branch-guard-mis-measures-recursion]] flagged) and ISOLATING the enclosing-locate as
    the single remaining residual ([[ref-parametric-assembler-extraction]] /
    [[ref-probe-provider-satisfiable-before-assembler]]).

    **What `h_widthEnc`'s deliverable actually is** (read off `seqLocalCarrier_of_widthEnc`'s
    hypothesis, above): for each gated window `[a, b)` whose enclosing opener is `p`, the
    ENCLOSING-WINDOW facts of `[p, hiE)` (`FlowBodyWindow` / `FlowBodyContentDeep` / `FlowBodyContent`)
    PLUS a width-gated `RecSeqBody` IH for the sub-windows of `[p, hiE)` (gate `hi' - lo' < hiE - p`).
    So the deliverable splits cleanly into a LOCATE part and an IH part, and this lemma supplies each
    from one hypothesis:

    * `enclosingLocate` — the LOCATE residual.  Given the gate + located-opener facts it returns the
      enclosing window `[p, hiE)`'s three content facts, the bound `b ≤ hiE ≤ tokens.size`, AND the two
      containments `lo ≤ p` and `hiE ≤ hi` (the enclosing window lies WITHIN the body `[lo, hi)`).
      Those two containments are what make the descent well-founded — they are the genuine residual the
      backward enclosing-opener locator + `seqClose_of_located_and_enclosing` produce (the body is the
      recursion window, the enclosing seq a contained sub-bracket).
    * `recIH` — the joint width IH.  A `RecSeqBody` producer for every body window STRICTLY NARROWER
      than `[lo, hi)` (gate `hi' - lo' < hi - lo`, containment `lo ≤ lo'`, `hi' ≤ hi`), exactly the IH a
      `windowWidth_strongRecOn` over the body width hands its step (cf. `seqWindowRecSeqBody_general`'s
      `G`-guard `lo0 ≤ lo ∧ hi ≤ hi0`).

    **The one piece of real content — the width bridge** (`body_ih_covers_frame_ih`, R473).  The
    deliverable's inner IH is gated `hi' - lo' < hiE - p`; the joint IH `recIH` is gated
    `hi' - lo' < hi - lo`.  The two containments `lo ≤ p` and `hiE ≤ hi` give
    `hiE - p ≤ hi - lo`, so the inner gate IMPLIES the joint gate
    (`hi' - lo' < hiE - p ≤ hi - lo`) — `omega` from the four facts.  The same containments lift the
    inner quantifier's `p ≤ lo'` / `hi' ≤ hiE` to `recIH`'s `lo ≤ lo'` / `hi' ≤ hi`.  No `SafeBodyUnit`
    is touched here: this assemble is exactly the half of the joint induction that sidesteps the
    `SafeBodyUnit` ↔ carrier ↔ `RecSeqBody` circularity (the carrier construction, which needs
    `h_safe`, is the SEPARATE `seqLocalCarrier_of_widthEnc` step).

    Verified-but-unconsumed until the joint induction supplies `enclosingLocate` + `recIH` and feeds
    the result to `seqLocalCarrier_of_widthEnc`: composes only landed lemmas + `omega`, references no
    sorry site, frontier sorry count unchanged at 4; axiom-clean. -/
theorem seqWidthEnc_of_enclosingLocate_and_recIH
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (enclosingLocate : ∀ a b p, lo ≤ a → a ≤ b → b ≤ hi →
        flowBracketBalance tokens lo a ≠ 0 →
        SeqTypedInterior tokens a b →
        p < a → flowBracketDelta tokens[p]!.val = 1 →
        flowBracketBalance tokens (p + 1) a = 0 →
        (∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) →
        lo ≤ p ∧ ∃ hiE, b ≤ hiE ∧ hiE ≤ tokens.size ∧ hiE ≤ hi ∧
          FlowBodyWindow tokens p hiE ∧ FlowBodyContentDeep tokens p hiE ∧
          FlowBodyContent tokens p hiE)
    (recIH : ∀ lo' hi', hi' - lo' < hi - lo → lo ≤ lo' → hi' ≤ hi →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' →
        SeqEnclosed tokens lo' → tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo')) :
    ∀ a b p, lo ≤ a → a ≤ b → b ≤ hi →
        flowBracketBalance tokens lo a ≠ 0 →
        SeqTypedInterior tokens a b →
        p < a → flowBracketDelta tokens[p]!.val = 1 →
        flowBracketBalance tokens (p + 1) a = 0 →
        (∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) →
        ∃ hiE, b ≤ hiE ∧ hiE ≤ tokens.size ∧
          FlowBodyWindow tokens p hiE ∧ FlowBodyContentDeep tokens p hiE ∧
          FlowBodyContent tokens p hiE ∧
          (∀ lo' hi', hi' - lo' < hiE - p → p ≤ lo' → hi' ≤ hiE →
            FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' →
            SeqEnclosed tokens lo' → tokens[hi']!.val = .flowSequenceEnd →
            RecSeqBody ((tokens.toList.take hi').drop lo')) := by
  intro a b p ha hab hb hbal hgate hpa h_delta h_body_bal h_loc_floor
  obtain ⟨h_lo_p, hiE, h_b_hiE, h_hiE_sz, h_hiE_hi, h_win, h_deep, h_content⟩ :=
    enclosingLocate a b p ha hab hb hbal hgate hpa h_delta h_body_bal h_loc_floor
  refine ⟨hiE, h_b_hiE, h_hiE_sz, h_win, h_deep, h_content, ?_⟩
  intro lo' hi' h_width h_p_lo' h_hi'_hiE h_w h_d h_q h_c
  exact recIH lo' hi' (by omega) (by omega) (by omega) h_w h_d h_q h_c

/-- **The `_seq` twin of the width-enc ASSEMBLE — a TRANSPORTING lemma re-threads with ZERO body edits.**
    `(i'-b-B2c-(d)-seq-widthEnc-assemble-seq)`, R492: the `FlowBodyContentDeepSeq`-keyed twin of R475
    `seqWidthEnc_of_enclosingLocate_and_recIH`, re-keyed off the root-FALSE strong content guard onto its
    root-TRUE weaker twin ([[ref-root-seed-needs-root-true-guard]] R488, [[ref-rethread-stays-in-weaker-twin-family]]
    R489).  This is the next link of the `_seq` re-thread after the leaf assemble
    `seqEnclosingLocate_of_seqOpener_nested_seq` (R491): it takes a `_seq`-keyed `enclosingLocate` residual
    plus a `_seq`-keyed body-width `recIH` and lifts them into the `_seq`-keyed `widthEnc` deliverable.

    **The find — a TRANSPORTING lemma's twin is a SIGNATURE-ONLY swap, even cheaper than a constructing
    one.**  R491's leaf assemble had TWO body edits because it CONSTRUCTS the deliverable's guard conjuncts
    at the child-bracket constructors — the guard hypothesis is READ wherever a conjunct is built
    ([[ref-rescope-assemble-cost-is-guard-read-sites]]).  R475 is different in kind: it never CONSTRUCTS the
    guard, it only TRANSPORTS one — `obtain`s `h_deep : FlowBodyContentDeep tokens p hiE` from the
    `enclosingLocate` hypothesis, `refine`s it straight into the conclusion's matching slot, and threads
    the conclusion's IH premise `h_d` straight into `recIH`.  The guard is never matched, destructured, or
    inspected.  Grep `FlowBodyContentDeep` in R475's BODY: ZERO hits — every occurrence is in the
    SIGNATURE (the `enclosingLocate` deliverable, the `recIH` premise, the conclusion deliverable, the
    conclusion IH premise — 4 positions, all transported).  So:

      cost(re-scope a TRANSPORTING lemma) = swap the guard TYPE at its signature positions,
        BODY copies byte-identical (0 edits).

    The body below is character-for-character R475's; only the four `FlowBodyContentDeep` in the signature
    became `FlowBodyContentDeepSeq`.  This is the FLOOR of the grep-bounded cost
    ([[ref-rescope-assemble-cost-is-guard-read-sites]]): a constructing assemble pays (read sites) body
    swaps; a transporting plumbing lemma pays ZERO — its read-site count is literally 0 because the guard
    is carried, not consumed.  The transport/construct distinction is WHY a whole re-thread chain is cheap:
    its cost concentrates in the few CONSTRUCTING leaves (R489/R490/R491), while every PLUMBING link
    (R475→R492) re-keys for free.

    Verified-but-unconsumed until `seqWidthEnc_of_recIH_seq` (the R486-twin) feeds it: that twin
    reconstructs the typed opener via `seqOpenerType_of_located_and_gate` (unchanged from R486) and supplies
    THIS lemma's `enclosingLocate` residual from `seqEnclosingLocate_of_seqOpener_nested_seq` (R491).
    Composes nothing but transports its two hypotheses (pure plumbing), references no sorry site, frontier
    sorry count unchanged at 4; axioms identical to R475 (the body is byte-identical). -/
theorem seqWidthEnc_of_enclosingLocate_and_recIH_seq
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (enclosingLocate : ∀ a b p, lo ≤ a → a ≤ b → b ≤ hi →
        flowBracketBalance tokens lo a ≠ 0 →
        SeqTypedInterior tokens a b →
        p < a → flowBracketDelta tokens[p]!.val = 1 →
        flowBracketBalance tokens (p + 1) a = 0 →
        (∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) →
        lo ≤ p ∧ ∃ hiE, b ≤ hiE ∧ hiE ≤ tokens.size ∧ hiE ≤ hi ∧
          FlowBodyWindow tokens p hiE ∧ FlowBodyContentDeepSeq tokens p hiE ∧
          FlowBodyContent tokens p hiE)
    (recIH : ∀ lo' hi', hi' - lo' < hi - lo → lo ≤ lo' → hi' ≤ hi →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeepSeq tokens lo' hi' →
        SeqEnclosed tokens lo' → tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo')) :
    ∀ a b p, lo ≤ a → a ≤ b → b ≤ hi →
        flowBracketBalance tokens lo a ≠ 0 →
        SeqTypedInterior tokens a b →
        p < a → flowBracketDelta tokens[p]!.val = 1 →
        flowBracketBalance tokens (p + 1) a = 0 →
        (∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) →
        ∃ hiE, b ≤ hiE ∧ hiE ≤ tokens.size ∧
          FlowBodyWindow tokens p hiE ∧ FlowBodyContentDeepSeq tokens p hiE ∧
          FlowBodyContent tokens p hiE ∧
          (∀ lo' hi', hi' - lo' < hiE - p → p ≤ lo' → hi' ≤ hiE →
            FlowBodyWindow tokens lo' hi' → FlowBodyContentDeepSeq tokens lo' hi' →
            SeqEnclosed tokens lo' → tokens[hi']!.val = .flowSequenceEnd →
            RecSeqBody ((tokens.toList.take hi').drop lo')) := by
  intro a b p ha hab hb hbal hgate hpa h_delta h_body_bal h_loc_floor
  obtain ⟨h_lo_p, hiE, h_b_hiE, h_hiE_sz, h_hiE_hi, h_win, h_deep, h_content⟩ :=
    enclosingLocate a b p ha hab hb hbal hgate hpa h_delta h_body_bal h_loc_floor
  refine ⟨hiE, h_b_hiE, h_hiE_sz, h_win, h_deep, h_content, ?_⟩
  intro lo' hi' h_width h_p_lo' h_hi'_hiE h_w h_d h_q h_c
  exact recIH lo' hi' (by omega) (by omega) (by omega) h_w h_d h_q h_c

/-- **The load-bearing containment `lo ≤ p` of the `enclosingLocate` residual** — the FIRST sub-piece of
    the (α) locate boundary that `seqWidthEnc_of_enclosingLocate_and_recIH` lifts.  Per R475 the
    assemble's whole well-foundedness rides on the located enclosing frame `[p, hiE)` being CONTAINED in
    the body window `[lo, hi)` (`lo ≤ p`, `hiE ≤ hi`); this brick discharges the LOWER containment
    purely from balance arithmetic — no content structure, no close location.

    The argument is a balance-additivity contradiction.  Suppose `p < lo` (i.e. `p + 1 ≤ lo`).  The
    body window's Dyck floor gives `flowBracketBalance tokens lo a ≥ 0` at the nested start `a`, and the
    gate's `≠ 0` lifts it to `≥ 1` (the window `[a,b)` is genuinely nested, so `a` sits at depth ≥ 1
    relative to `lo`).  Composing the located body balance across `lo`
    (`flowBracketBalance_compose tokens (p+1) lo a`):
    `0 = flowBracketBalance tokens (p+1) a = flowBracketBalance tokens (p+1) lo + flowBracketBalance tokens lo a`,
    so `flowBracketBalance tokens (p+1) lo = -(flowBracketBalance tokens lo a) ≤ -1 < 0`.  But the
    locator's own Dyck floor `h_loc_floor` instantiated at `lo` (which sits in `[p+1, a]` under the
    `p + 1 ≤ lo ≤ a` assumption) says `flowBracketBalance tokens (p+1) lo ≥ 0` — contradiction.  Hence
    `lo ≤ p`: the enclosing opener cannot lie before the body window's start, because doing so would
    force the locator's interior to dip below its own floor at `lo`.

    The body Dyck floor (`h_dyck`, supplied by `FlowBodyWindow tokens lo hi` in the eventual joint
    induction) and the locator floor (`h_loc_floor`, delivered alongside `p` by
    `seqEnclosingOpener_of_gate`) are the only structural inputs; everything else is `omega` over `Int`.
    The containment is LOAD-BEARING, not bookkeeping ([[ref-contained-frame-ih-from-outer-ih]]): it is
    one of the two facts that make the assemble's inner frame-width IH dischargeable from the outer
    body-width IH.

    Verified-but-unconsumed until the `enclosingLocate` builder wires it together with the close locator
    (`seqClose_of_located_and_enclosing`) and the three content-structure constructions; composes only
    `flowBracketBalance_compose` + `omega`, references no sorry site, frontier sorry count unchanged at
    4; axiom-clean. -/
theorem seqLocatedOpener_within_body
    (tokens : Array (Positioned YamlToken)) (lo hi a p : Nat)
    (h_lo_a : lo ≤ a) (h_a_hi : a ≤ hi)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_bal_ne : flowBracketBalance tokens lo a ≠ 0)
    (_h_pa : p < a)
    (h_body_bal : flowBracketBalance tokens (p + 1) a = 0)
    (h_loc_floor : ∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) :
    lo ≤ p := by
  rcases Nat.lt_or_ge p lo with h_lt | h_ge
  · -- `p < lo`, i.e. `p + 1 ≤ lo`, is the case to refute.
    have h_p1_lo : p + 1 ≤ lo := by omega
    -- `a` sits at depth ≥ 1 relative to `lo`: Dyck floor ≥ 0, plus the gate's `≠ 0`.
    have h_floor_a : flowBracketBalance tokens lo a ≥ 0 := h_dyck a h_lo_a h_a_hi
    -- Split the located body balance across `lo`.
    have h_comp : flowBracketBalance tokens (p + 1) a
        = flowBracketBalance tokens (p + 1) lo + flowBracketBalance tokens lo a :=
      flowBracketBalance_compose tokens (p + 1) lo a h_p1_lo h_lo_a
    -- The locator's own floor at `lo` forbids the negative segment forced above.
    have h_floor_lo : flowBracketBalance tokens (p + 1) lo ≥ 0 :=
      h_loc_floor lo h_p1_lo h_lo_a
    omega
  · exact h_ge

/-- **The load-bearing containment `hiE ≤ hi` of the `enclosingLocate` residual** — the END-DUAL of
    `seqLocatedOpener_within_body`, and the SECOND of the two containments R475 needs.  Where the LOWER
    containment `lo ≤ p` falls out of the OPENER-locator's interior floor (over `[p+1, a]`), the UPPER
    containment `hiE ≤ hi` falls out of the CLOSE-locator's interior floor (over `[p+1, hiE]`) against
    the SAME enclosing window facts — same floor-conflict shape, mirrored to the other end.  No content
    structure, no separate close arithmetic — purely balance.

    The argument is the symmetric balance-additivity contradiction.  Suppose `hi < hiE` (i.e.
    `p + 1 ≤ hi ≤ hiE`).  The close-locator's own interior floor `h_inner_floor` instantiated at `hi`
    (which sits in `[p+1, hiE]`) gives `flowBracketBalance tokens (p+1) hi ≥ 0`.  But the enclosing
    window forces it negative: split the enclosing total across `p` and `p+1`
    (`flowBracketBalance_compose tokens lo p hi`, then `… tokens p (p+1) hi`):
    `0 = flowBracketBalance tokens lo hi = flowBracketBalance tokens lo p + 1 + flowBracketBalance tokens (p+1) hi`,
    so `flowBracketBalance tokens (p+1) hi = -1 - flowBracketBalance tokens lo p ≤ -1 < 0` (using the
    enclosing Dyck floor `h_dyck` at `p` for `flowBracketBalance tokens lo p ≥ 0`, and the opener delta
    `h_open` for the `+1`).  Contradiction.  Hence `hiE ≤ hi`: the enclosing opener at `p` is matched
    BEFORE the window ends, because the located frame's interior cannot dip below its own floor while
    the enclosing window is already paying back the opener's `+1` by `hi`.

    **The inner floor `h_inner_floor` is the close-locator's SILENTLY-DROPPED output.**
    `flowBracketBalance_matching_close_seq` (WellBracketed.lean:2107) computes BOTH `j < hi` and the
    interior floor `∀ p', p+1 ≤ p' → p' ≤ j → flowBracketBalance tokens (p+1) p' ≥ 0`, but
    `seqClose_of_located_and_enclosing`'s return type (SeqInteriorSeparators.lean:538) erases both — it
    re-exports only `a ≤ hiS`, `b ≤ hiS`, `hiS ≤ size`, `balance (p+1) hiS = 0`, the typed close.  So
    the UPPER containment needs NO new machinery: re-thread the dropped floor (strengthen the
    close-locator's return, or call `flowBracketBalance_matching_close_seq` directly) and this brick
    closes it.  (In fact the dropped `j < hi` gives `hiE ≤ hi` outright; this brick is the route that
    survives even when the close is located relative to the opener's OWN frame at arbitrary nesting
    depth, where the `lo`-relative `j < hi` is not directly in hand — see the depth caveat on
    `seqClose_of_located_and_enclosing`'s `h_p_depth : balance lo p = 0`.)

    Verified-but-unconsumed until the `enclosingLocate` builder wires it with the close locator and the
    three content-structure constructions; composes only `flowBracketBalance_compose` + `omega`,
    references no sorry site, frontier sorry count unchanged at 4; axiom-clean. -/
theorem seqLocatedClose_within_body
    (tokens : Array (Positioned YamlToken)) (lo hi p hiE : Nat)
    (h_lo_p : lo ≤ p) (h_p_hi : p < hi)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_open : flowBracketBalance tokens p (p + 1) = 1)
    (h_inner_floor : ∀ i, p + 1 ≤ i → i ≤ hiE → flowBracketBalance tokens (p + 1) i ≥ 0) :
    hiE ≤ hi := by
  rcases Nat.lt_or_ge hi hiE with h_gt | h_ge
  · -- `hi < hiE`, i.e. `p + 1 ≤ hi ≤ hiE`, is the case to refute.
    have h_p1_hi : p + 1 ≤ hi := by omega
    -- The close-locator's interior floor at `hi` (which lies in `[p+1, hiE]`).
    have h_floor_hi : flowBracketBalance tokens (p + 1) hi ≥ 0 :=
      h_inner_floor hi h_p1_hi (by omega)
    -- The enclosing window's Dyck floor at `p`.
    have h_floor_p : flowBracketBalance tokens lo p ≥ 0 := h_dyck p h_lo_p (by omega)
    -- Split the enclosing total across `p`, then across `p + 1`.
    have h_comp1 : flowBracketBalance tokens lo hi
        = flowBracketBalance tokens lo p + flowBracketBalance tokens p hi :=
      flowBracketBalance_compose tokens lo p hi h_lo_p (by omega)
    have h_comp2 : flowBracketBalance tokens p hi
        = flowBracketBalance tokens p (p + 1) + flowBracketBalance tokens (p + 1) hi :=
      flowBracketBalance_compose tokens p (p + 1) hi (by omega) h_p1_hi
    omega
  · exact h_ge

/-- **The close locator that RE-EXPORTS what `seqClose_of_located_and_enclosing` drops** —
    `(i'-b-locator-glue-close-within)`, the α.1-remaining sub-piece of the (α) `enclosingLocate`
    residual.  `seqClose_of_located_and_enclosing` (SeqInteriorSeparators.lean:526) calls
    `flowBracketBalance_matching_close_seq`, which delivers BOTH `j < hi` and the located interior's own
    Dyck floor `∀ i ∈ [p+1, j], flowBracketBalance tokens (p+1) i ≥ 0` — but it then `_`-drops the floor
    (its line 543) and omits `j < hi` from its return type.  Per
    [[ref-additive-parallel-type-over-shared-edit]] this is a NEW parallel locator (the original is
    consumed by `seqEnclosingFacts_provider_of_located`; we do NOT edit its return type in place) whose
    return strengthens the original with the two dropped facts: the UPPER containment `hiS ≤ hi` and the
    interior floor.  It lives HERE (after `seqLocatedClose_within_body`, R477) rather than next to its
    sibling because consuming R477 forbids the forward reference.

    Those two facts are EXACTLY what the `enclosingLocate` existential still owes after the two
    containment bricks: R475's `seqWidthEnc_of_enclosingLocate_and_recIH` consumes
    `lo ≤ p ∧ ∃ hiE, b ≤ hiE ∧ hiE ≤ tokens.size ∧ hiE ≤ hi ∧ FlowBodyWindow/Deep/Content`, and the
    `hiE ≤ hi` conjunct is precisely the upper containment this locator now hands back directly (the
    `FlowBody…` conjuncts are α.2, derived from this located close + the body-window fields).

    **This consumes R477** ([[ref-reduction-by-import]]: wiring the verified-but-unconsumed brick
    retypes the residual — the retype is the progress).  The UPPER containment is discharged by
    `seqLocatedClose_within_body` fed the re-exported floor (with `flowBracketBalance tokens p (p+1) = 1`
    recovered from the typed opener `h_open` via the single-step `flowBracketBalance_single` bridge).
    The matching-close's own `j < hi` would give `hiS ≤ hi` outright at this depth-1 locator; routing
    through `seqLocatedClose_within_body` instead exercises the floor→containment principle on real
    `flowBracketBalance` data and is the route that survives the multi-level re-base, where the close is
    located relative to the opener's OWN frame and the `lo`-relative `j < hi` is not directly in hand
    (the depth caveat on `h_p_depth : flowBracketBalance tokens lo p = 0` — a re-base of
    [[ref-rebase-fact-from-enclosing-window]]).

    Everything else mirrors `seqClose_of_located_and_enclosing` verbatim: same hypotheses, same `a ≤ j`
    / `balance a j = 0` / `b ≤ j` derivations from the locator and gate floors.  Verified-but-unconsumed
    until the `enclosingLocate` builder calls it: composes only landed lemmas + `omega`, references no
    sorry site, frontier sorry count unchanged at 4; axiom-clean. -/
theorem seqClose_of_located_and_enclosing_within
    (tokens : Array (Positioned YamlToken)) (a b lo p hi : Nat)
    (h_lo_p : lo ≤ p) (h_pa : p < a) (h_ab : a ≤ b) (h_b_hi : b ≤ hi)
    (h_hi_sz : hi ≤ tokens.size)
    (h_p_depth : flowBracketBalance tokens lo p = 0)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_win_floor : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_open : tokens[p]!.val = .flowSequenceStart)
    (h_body_bal : flowBracketBalance tokens (p + 1) a = 0)
    (h_loc_floor : ∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0)
    (h_gate_floor : ∀ i, a ≤ i → i ≤ b → flowBracketBalance tokens a i ≥ 0)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo)) :
    ∃ hiS, a ≤ hiS ∧ b ≤ hiS ∧ hiS ≤ hi ∧ hiS ≤ tokens.size ∧
      flowBracketBalance tokens (p + 1) hiS = 0 ∧
      tokens[hiS]!.val = .flowSequenceEnd ∧
      (∀ i, p + 1 ≤ i → i ≤ hiS → flowBracketBalance tokens (p + 1) i ≥ 0) := by
  have h_p_hi : p < hi := by omega
  -- Matching close + typed close + the interior floor, all in one call (base `lo`, opener `k := p`).
  -- Unlike `seqClose_of_located_and_enclosing`, we KEEP the final component `h_floor` (the floor).
  obtain ⟨j, h_pj, h_jhi, h_jclose, h_inner, h_floor⟩ :=
    flowBracketBalance_matching_close_seq tokens lo p hi h_lo_p h_p_hi h_hi_sz
      h_p_depth h_open h_total h_win_floor h_wt
  have h_jdelta : flowBracketDelta tokens[j]!.val = -1 := by rw [h_jclose]; rfl
  -- One-step balance recurrence at `j` over any base `≤ j` (mirrors `seqClose_of_located_and_enclosing`).
  have step : ∀ base, base ≤ j →
      flowBracketBalance tokens base (j + 1)
        = flowBracketBalance tokens base j + flowBracketDelta tokens[j]!.val := by
    intro base hbase
    have h_j_sz : j < tokens.size := by omega
    have hlen : j < tokens.toList.length := by rw [Array.length_toList]; exact h_j_sz
    rw [flowBracketBalance_compose tokens base j (j + 1) hbase (by omega),
        flowBracketBalance_single tokens j hlen]
    have h1 : tokens.toList[j]'hlen = tokens[j] := Array.getElem_toList h_j_sz
    have h2 : tokens[j] = tokens[j]! := (getElem!_pos tokens j h_j_sz).symm
    rw [h1, h2]
  -- (1) `a ≤ j` from the locator floor at `j + 1`.
  have h_a_j : a ≤ j := by
    rcases Nat.lt_or_ge j a with h | h
    · have h_floor' := h_loc_floor (j + 1) (by omega) (by omega)
      rw [step (p + 1) (by omega), h_inner, h_jdelta] at h_floor'
      omega
    · exact h
  -- (2) `balance a j = 0` by composition over `[p+1, a, j]`.
  have h_aj_bal : flowBracketBalance tokens a j = 0 := by
    have hc := flowBracketBalance_compose tokens (p + 1) a j (by omega) h_a_j
    rw [h_inner, h_body_bal] at hc; omega
  -- (3) `b ≤ j` from the GATE floor at `j + 1`.
  have h_b_j : b ≤ j := by
    rcases Nat.lt_or_ge j b with h | h
    · have h_floor' := h_gate_floor (j + 1) (by omega) (by omega)
      rw [step a h_a_j, h_aj_bal, h_jdelta] at h_floor'
      omega
    · exact h
  -- (4) the UPPER containment `j ≤ hi` via R477, from the re-exported interior floor `h_floor`.
  have h_open_bal : flowBracketBalance tokens p (p + 1) = 1 := by
    have h_p_sz : p < tokens.size := by omega
    have hlen : p < tokens.toList.length := by rw [Array.length_toList]; exact h_p_sz
    have h_delta : flowBracketDelta tokens[p]!.val = 1 := by rw [h_open]; rfl
    have h1 : tokens.toList[p]'hlen = tokens[p] := Array.getElem_toList h_p_sz
    have h2 : tokens[p] = tokens[p]! := (getElem!_pos tokens p h_p_sz).symm
    rw [flowBracketBalance_single tokens p hlen, h1, h2, h_delta]
  have h_j_hi : j ≤ hi :=
    seqLocatedClose_within_body tokens lo hi p j h_lo_p h_p_hi h_win_floor h_total
      h_open_bal h_floor
  exact ⟨j, h_a_j, h_b_j, h_j_hi, by omega, h_inner, h_jclose, h_floor⟩

/-- **Depth-general twin of `seqClose_of_located_and_enclosing_within`** —
    `(i'-b-locator-glue-close-within-nested)`, the R478 close-within locator with its sole depth
    obligation `h_p_depth : flowBracketBalance tokens lo p = 0` DROPPED.  Identical to R478 except the
    matching-close call swaps the depth-0 `flowBracketBalance_matching_close_seq` for R483's
    depth-general `flowBracketBalance_matching_close_seq_nested` (WellBracketed.lean:2498) — which frames
    the typed close over the enclosing opener's base stack rather than re-deriving against a depth-0
    baseline ([[ref-nested-typed-locator-is-a-frame]]).

    **Nothing else in the proof touched `h_p_depth`.**  The three positional facts (`a ≤ j`,
    `balance a j = 0`, `b ≤ j`) come from the locator/gate floors; the upper containment `j ≤ hi` comes
    from R477 `seqLocatedClose_within_body`, which reads `hiE ≤ hi` off the enclosing Dyck floor
    (`balance lo p ≥ 0`, NOT `= 0`) + the opener delta + the re-exported interior floor.  So `h_p_depth`
    was load-bearing at EXACTLY one call site, and removing it leaves the rest of the proof byte-identical.
    This is the [[ref-reduction-by-import]] consume of R483's verified-but-unconsumed
    `flowBracketBalance_matching_close_seq_nested`: wiring it retypes the close-within residual from
    depth-0-keyed to depth-general (the retype is the progress).

    Per [[ref-additive-parallel-type-over-shared-edit]] this is a NEW parallel locator, not an in-place
    edit of R478 (still consumed by R481 `seqEnclosingLocate_of_seqOpener_at_depth`, which passes
    `h_p_depth`); the next brick rewires R481 to call THIS twin and drops `h_p_depth` there (its step-(4)
    `hiS < hi` re-derives from `balance lo p ≥ 0` instead of `= 0`).  Verified-but-unconsumed: composes
    only landed lemmas (R483 nested close + R477 + `flowBracketBalance_compose`/`_single`) + `omega`,
    references no sorry site, frontier sorry count unchanged at 4; axiom-clean. -/
theorem seqClose_of_located_and_enclosing_within_nested
    (tokens : Array (Positioned YamlToken)) (a b lo p hi : Nat)
    (h_lo_p : lo ≤ p) (h_pa : p < a) (h_ab : a ≤ b) (h_b_hi : b ≤ hi)
    (h_hi_sz : hi ≤ tokens.size)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_win_floor : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_open : tokens[p]!.val = .flowSequenceStart)
    (h_body_bal : flowBracketBalance tokens (p + 1) a = 0)
    (h_loc_floor : ∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0)
    (h_gate_floor : ∀ i, a ≤ i → i ≤ b → flowBracketBalance tokens a i ≥ 0)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo)) :
    ∃ hiS, a ≤ hiS ∧ b ≤ hiS ∧ hiS ≤ hi ∧ hiS ≤ tokens.size ∧
      flowBracketBalance tokens (p + 1) hiS = 0 ∧
      tokens[hiS]!.val = .flowSequenceEnd ∧
      (∀ i, p + 1 ≤ i → i ≤ hiS → flowBracketBalance tokens (p + 1) i ≥ 0) := by
  have h_p_hi : p < hi := by omega
  -- Matching close + typed close + interior floor, at depth ≥ 0 (R483 nested locator; no `h_p_depth`).
  obtain ⟨j, h_pj, h_jhi, h_jclose, h_inner, h_floor⟩ :=
    flowBracketBalance_matching_close_seq_nested tokens lo p hi h_lo_p h_p_hi h_hi_sz
      h_open h_total h_win_floor h_wt
  have h_jdelta : flowBracketDelta tokens[j]!.val = -1 := by rw [h_jclose]; rfl
  -- One-step balance recurrence at `j` over any base `≤ j` (verbatim from R478).
  have step : ∀ base, base ≤ j →
      flowBracketBalance tokens base (j + 1)
        = flowBracketBalance tokens base j + flowBracketDelta tokens[j]!.val := by
    intro base hbase
    have h_j_sz : j < tokens.size := by omega
    have hlen : j < tokens.toList.length := by rw [Array.length_toList]; exact h_j_sz
    rw [flowBracketBalance_compose tokens base j (j + 1) hbase (by omega),
        flowBracketBalance_single tokens j hlen]
    have h1 : tokens.toList[j]'hlen = tokens[j] := Array.getElem_toList h_j_sz
    have h2 : tokens[j] = tokens[j]! := (getElem!_pos tokens j h_j_sz).symm
    rw [h1, h2]
  -- (1) `a ≤ j` from the locator floor at `j + 1`.
  have h_a_j : a ≤ j := by
    rcases Nat.lt_or_ge j a with h | h
    · have h_floor' := h_loc_floor (j + 1) (by omega) (by omega)
      rw [step (p + 1) (by omega), h_inner, h_jdelta] at h_floor'
      omega
    · exact h
  -- (2) `balance a j = 0` by composition over `[p+1, a, j]`.
  have h_aj_bal : flowBracketBalance tokens a j = 0 := by
    have hc := flowBracketBalance_compose tokens (p + 1) a j (by omega) h_a_j
    rw [h_inner, h_body_bal] at hc; omega
  -- (3) `b ≤ j` from the GATE floor at `j + 1`.
  have h_b_j : b ≤ j := by
    rcases Nat.lt_or_ge j b with h | h
    · have h_floor' := h_gate_floor (j + 1) (by omega) (by omega)
      rw [step a h_a_j, h_aj_bal, h_jdelta] at h_floor'
      omega
    · exact h
  -- (4) the UPPER containment `j ≤ hi` via R477, from the re-exported interior floor `h_floor`.
  have h_open_bal : flowBracketBalance tokens p (p + 1) = 1 := by
    have h_p_sz : p < tokens.size := by omega
    have hlen : p < tokens.toList.length := by rw [Array.length_toList]; exact h_p_sz
    have h_delta : flowBracketDelta tokens[p]!.val = 1 := by rw [h_open]; rfl
    have h1 : tokens.toList[p]'hlen = tokens[p] := Array.getElem_toList h_p_sz
    have h2 : tokens[p] = tokens[p]! := (getElem!_pos tokens p h_p_sz).symm
    rw [flowBracketBalance_single tokens p hlen, h1, h2, h_delta]
  have h_j_hi : j ≤ hi :=
    seqLocatedClose_within_body tokens lo hi p j h_lo_p h_p_hi h_win_floor h_total
      h_open_bal h_floor
  exact ⟨j, h_a_j, h_b_j, h_j_hi, by omega, h_inner, h_jclose, h_floor⟩

/-- **The (α) `enclosingLocate` assemble — seq child, given the two discriminators** —
    `(i'-b-enclosingLocate-assemble-seq)`.  Assembles the FULL `enclosingLocate` residual that
    `seqWidthEnc_of_enclosingLocate_and_recIH` (R475) consumes: from a located enclosing seq opener `p`
    of the typed interior `[a, b)` inside the body window `[lo, hi)`, it delivers
    `lo ≤ p ∧ ∃ hiE, b ≤ hiE ∧ hiE ≤ size ∧ hiE ≤ hi ∧ FlowBodyWindow/Deep/Content tokens p hiE`,
    feeding ONE located close UNIFORMLY to all three "given close" child-bracket constructors.

    **The assembly (five moves).**
    1. `lo ≤ p` from R476 `seqLocatedOpener_within_body` (the opener cannot precede the window start —
       a balance-additivity contradiction against the locator floor at `lo`).
    2. The matching close `hiS` from R478 `seqClose_of_located_and_enclosing_within`, which re-exports the
       interior balance `balance (p+1) hiS = 0`, the typed close `tokens[hiS]! = .flowSequenceEnd`, and
       the `(p+1)`-keyed interior floor `≥ 0` (R478 owns the family's sole depth obligation, `h_p_depth`).
    3. The CHILD-keyed floor `balance p i ≥ 1` on `[p+1, hiS]` by ONE `flowBracketBalance_compose`
       through the opener (`balance p (p+1) = 1`, so `balance p i = 1 + balance (p+1) i ≥ 1`).
    4. `hiS < hi` (so `hiE := hiS + 1 ≤ hi`): the located close sits at depth `1` relative to `lo`
       (`balance lo hiS = balance lo p + balance p (p+1) + balance (p+1) hiS = 0 + 1 + 0 = 1`), yet the
       window is balanced (`balance lo hi = 0`), so `hiS ≠ hi`.
    5. The three constructors at `k := p`, `j := hiS`, `hiE := hiS + 1` —
       `flowBodyWindow_child_bracket_at` (R480), `flowBodyContentDeep_child_bracket`,
       `flowBodyContent_child_bracket` (R479) — all DEPTH-FREE, fed the one located boundary
       ([[ref-scan-owns-the-depth-debt]]).  The trio's whole depth caveat is paid ONCE at R478's locator.

    **The two discriminators ARE the consume-side residual.**  `enclosingLocate`'s premise gives only
    `flowBracketDelta tokens[p]!.val = 1` (a generic opener) and carries no depth.  The SEQ assemble needs
    both strengthenings — `h_open : tokens[p]!.val = .flowSequenceStart` (R478 and the seq close require a
    `[`, not a `{`; the `{` child is the separate map-side producer) and
    `h_p_depth : flowBracketBalance tokens lo p = 0` (the family's sole depth sink).  In the consume
    context the located `p` is a top-level `[` at depth `0`, so both hold; here they are explicit
    hypotheses, isolating EXACTLY what the `enclosingLocate` wiring must still supply (the residual after
    this brick is purely "discharge the seq-opener type + depth-0 at the located `p`", no more structure).

    Verified-but-unconsumed until `seqWidthEnc_of_enclosingLocate_and_recIH` is wired with the depth +
    seq-opener discriminators: composes only landed lemmas (R476/R478 + the child-bracket trio) +
    `flowBracketBalance_compose` + `omega`, references no sorry site, frontier sorry count unchanged at 4;
    axiom-clean. -/
theorem seqEnclosingLocate_of_seqOpener_at_depth
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeep tokens lo hi)
    (a b p : Nat)
    (ha : lo ≤ a) (hab : a ≤ b) (hb : b ≤ hi)
    (hbal : flowBracketBalance tokens lo a ≠ 0)
    (hgate : SeqTypedInterior tokens a b)
    (hpa : p < a)
    (h_open : tokens[p]!.val = .flowSequenceStart)
    (h_body_bal : flowBracketBalance tokens (p + 1) a = 0)
    (h_loc_floor : ∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0)
    (h_p_depth : flowBracketBalance tokens lo p = 0) :
    lo ≤ p ∧ ∃ hiE, b ≤ hiE ∧ hiE ≤ tokens.size ∧ hiE ≤ hi ∧
      FlowBodyWindow tokens p hiE ∧ FlowBodyContentDeep tokens p hiE ∧
      FlowBodyContent tokens p hiE := by
  have h_dyck := h_win.dyck
  have h_bal := h_win.balanced
  have h_wt := h_win.wellTyped
  have h_hi_lt := h_win.hi_lt
  obtain ⟨_h_gbal, _h_gtop, h_gate_floor⟩ := hgate
  have h_a_hi : a ≤ hi := by omega
  have h_hi_sz : hi ≤ tokens.size := Nat.le_of_lt h_hi_lt
  -- (1) `lo ≤ p` — the opener cannot precede the window start.
  have h_lo_p : lo ≤ p :=
    seqLocatedOpener_within_body tokens lo hi a p ha h_a_hi h_dyck hbal hpa h_body_bal h_loc_floor
  -- (2) locate the matching close `hiS`, re-exporting the interior balance / typed close / floor.
  obtain ⟨hiS, h_a_hiS, h_b_hiS, h_hiS_hi, h_hiS_sz, h_inner, h_hiSclose, h_floor⟩ :=
    seqClose_of_located_and_enclosing_within tokens a b lo p hi h_lo_p hpa hab hb h_hi_sz
      h_p_depth h_bal h_dyck h_open h_body_bal h_loc_floor h_gate_floor h_wt
  -- opener delta + single-step balance `balance p (p+1) = 1`.
  have h_p_sz : p < tokens.size := by omega
  have h_delta : flowBracketDelta tokens[p]!.val = 1 := by rw [h_open]; rfl
  have h_open_bal : flowBracketBalance tokens p (p + 1) = 1 := by
    have hlen : p < tokens.toList.length := by rw [Array.length_toList]; exact h_p_sz
    have h1 : tokens.toList[p]'hlen = tokens[p] := Array.getElem_toList h_p_sz
    have h2 : tokens[p] = tokens[p]! := (getElem!_pos tokens p h_p_sz).symm
    rw [flowBracketBalance_single tokens p hlen, h1, h2, h_delta]
  -- (3) child-keyed floor `balance p i ≥ 1` via one compose through the opener.
  have h_childfloor : ∀ i, p + 1 ≤ i → i ≤ hiS → flowBracketBalance tokens p i ≥ 1 := by
    intro i hi1 hi2
    have hc := flowBracketBalance_compose tokens p (p + 1) i (by omega) hi1
    have hf := h_floor i hi1 hi2
    rw [h_open_bal] at hc
    omega
  -- closer delta from the typed close.
  have h_jdelta : flowBracketDelta tokens[hiS]!.val = -1 := by rw [h_hiSclose]; rfl
  -- (4) `hiS < hi` from `balance lo hiS = 1 ≠ 0 = balance lo hi`.
  have h_lo_hiS_bal : flowBracketBalance tokens lo hiS = 1 := by
    have hc1 := flowBracketBalance_compose tokens lo p hiS h_lo_p (by omega)
    have hc2 := flowBracketBalance_compose tokens p (p + 1) hiS (by omega) (by omega)
    rw [h_p_depth] at hc1
    rw [h_open_bal, h_inner] at hc2
    omega
  have h_hiS_lt_hi : hiS < hi := by
    rcases Nat.lt_or_ge hiS hi with h | h
    · exact h
    · have heq : hiS = hi := by omega
      rw [heq] at h_lo_hiS_bal
      omega
  have h_hiS1_hi : hiS + 1 ≤ hi := h_hiS_lt_hi
  -- (5) the three depth-free constructors at `k := p`, `j := hiS`, `hiE := hiS + 1`.
  refine ⟨h_lo_p, hiS + 1, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · exact flowBodyWindow_child_bracket_at tokens lo p hiS hi h_win h_lo_p
      (by omega) h_hiS1_hi h_delta h_jdelta h_inner h_childfloor
  · exact flowBodyContentDeep_child_bracket tokens lo p hiS hi h_deep h_lo_p h_delta h_hiS1_hi
  · exact flowBodyContent_child_bracket tokens lo p hiS hi h_deep h_lo_p h_hiS1_hi h_delta
      h_hiSclose h_childfloor

/-- **Depth-general twin of `seqEnclosingLocate_of_seqOpener_at_depth`** —
    `(i'-b-enclosingLocate-assemble-seq-nested)`, the R481 (α) `enclosingLocate` seq assemble with its
    sole depth obligation `h_p_depth : flowBracketBalance tokens lo p = 0` DROPPED.  This is the brick the
    `enclosingLocate` wiring actually consumes: when the seq recursion DESCENDS, the located enclosing
    opener `p` sits at the enclosing window's depth `d := flowBracketBalance tokens lo p ≥ 0`, NOT at
    depth `0` — only the OUTERMOST window's opener is depth-`0`.  ([[ref-scan-owns-the-depth-debt]]: the
    whole family's depth caveat was paid once at R483's primitive; here we shed the last depth-`0`
    convenience.)

    **The cost was exactly its EQUALITY reads, countable by grep before editing**
    ([[ref-depth-hyp-cost-is-its-equality-reads]]).  `h_p_depth` funnelled to EXACTLY two sites in R481:
    1. **The matching-close locator call** (move 2) — a FLOOR-only consumer
       (`seqClose_of_located_and_enclosing_within`), generalized by R484 to
       `seqClose_of_located_and_enclosing_within_nested`.  Pure SWAP: drop the `h_p_depth` argument; the
       lower/upper containments (`a ≤ hiS`, `b ≤ hiS`, `hiS ≤ hi`) it re-exports are all floor reads,
       depth-free.
    2. **The one EQUALITY read** — step (4)'s `rw [h_p_depth] at hc1`, which substituted the pinned
       baseline to compute `balance lo hiS = 0 + 1 + 0 = 1` (so `hiS ≠ hi = balance lo hi`'s root).  At
       depth `d ≥ 0` the substitution is gone; the SAME conclusion `hiS < hi` re-derives from the
       enclosing Dyck floor `h_dyck p : balance lo p ≥ 0` — the located close sits at
       `balance lo hiS = d + 1 + 0 ≥ 1 > 0`, still strictly above the balanced window's `balance lo hi = 0`.
       One `omega` re-derivation, witness value loosened `= 1 ↦ ≥ 1`.

    Everything else is byte-identical to R481 (moves 1, 3, 5 are floor reads / depth-free constructors).
    Per [[ref-additive-parallel-type-over-shared-edit]] landed as a NEW `_nested` sibling (R481 stays as
    the depth-`0` specialization for any caller that still has `h_p_depth` in hand); the
    `enclosingLocate` wiring into R475 `seqWidthEnc_of_enclosingLocate_and_recIH` consumes THIS one and
    discharges `h_p_depth` for free — there is no depth-`0` fact to supply.

    Verified-but-unconsumed until that wiring (R225 discipline): composes only landed lemmas (R476 +
    R484's `_nested` close + the child-bracket trio) + `flowBracketBalance_compose` + `omega`, references
    no sorry site, frontier sorry count unchanged at 4; axiom-clean. -/
theorem seqEnclosingLocate_of_seqOpener_nested
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeep tokens lo hi)
    (a b p : Nat)
    (ha : lo ≤ a) (hab : a ≤ b) (hb : b ≤ hi)
    (hbal : flowBracketBalance tokens lo a ≠ 0)
    (hgate : SeqTypedInterior tokens a b)
    (hpa : p < a)
    (h_open : tokens[p]!.val = .flowSequenceStart)
    (h_body_bal : flowBracketBalance tokens (p + 1) a = 0)
    (h_loc_floor : ∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) :
    lo ≤ p ∧ ∃ hiE, b ≤ hiE ∧ hiE ≤ tokens.size ∧ hiE ≤ hi ∧
      FlowBodyWindow tokens p hiE ∧ FlowBodyContentDeep tokens p hiE ∧
      FlowBodyContent tokens p hiE := by
  have h_dyck := h_win.dyck
  have h_bal := h_win.balanced
  have h_wt := h_win.wellTyped
  have h_hi_lt := h_win.hi_lt
  obtain ⟨_h_gbal, _h_gtop, h_gate_floor⟩ := hgate
  have h_a_hi : a ≤ hi := by omega
  have h_hi_sz : hi ≤ tokens.size := Nat.le_of_lt h_hi_lt
  -- (1) `lo ≤ p` — the opener cannot precede the window start (FLOOR read, depth-free).
  have h_lo_p : lo ≤ p :=
    seqLocatedOpener_within_body tokens lo hi a p ha h_a_hi h_dyck hbal hpa h_body_bal h_loc_floor
  -- (2) locate the matching close `hiS` — the R484 depth-general `_nested` close (pure SWAP: no `h_p_depth`).
  obtain ⟨hiS, h_a_hiS, h_b_hiS, h_hiS_hi, h_hiS_sz, h_inner, h_hiSclose, h_floor⟩ :=
    seqClose_of_located_and_enclosing_within_nested tokens a b lo p hi h_lo_p hpa hab hb h_hi_sz
      h_bal h_dyck h_open h_body_bal h_loc_floor h_gate_floor h_wt
  -- opener delta + single-step balance `balance p (p+1) = 1`.
  have h_p_sz : p < tokens.size := by omega
  have h_delta : flowBracketDelta tokens[p]!.val = 1 := by rw [h_open]; rfl
  have h_open_bal : flowBracketBalance tokens p (p + 1) = 1 := by
    have hlen : p < tokens.toList.length := by rw [Array.length_toList]; exact h_p_sz
    have h1 : tokens.toList[p]'hlen = tokens[p] := Array.getElem_toList h_p_sz
    have h2 : tokens[p] = tokens[p]! := (getElem!_pos tokens p h_p_sz).symm
    rw [flowBracketBalance_single tokens p hlen, h1, h2, h_delta]
  -- (3) child-keyed floor `balance p i ≥ 1` via one compose through the opener.
  have h_childfloor : ∀ i, p + 1 ≤ i → i ≤ hiS → flowBracketBalance tokens p i ≥ 1 := by
    intro i hi1 hi2
    have hc := flowBracketBalance_compose tokens p (p + 1) i (by omega) hi1
    have hf := h_floor i hi1 hi2
    rw [h_open_bal] at hc
    omega
  -- closer delta from the typed close.
  have h_jdelta : flowBracketDelta tokens[hiS]!.val = -1 := by rw [h_hiSclose]; rfl
  -- (4) `hiS < hi` — the ONE equality read re-derived from the enclosing Dyck floor `d := balance lo p ≥ 0`.
  --     R481 `rw [h_p_depth]`d to compute `balance lo hiS = 0 + 1 + 0 = 1`; here `balance lo hiS = d + 1 + 0 ≥ 1`,
  --     still strictly above the balanced window's `balance lo hi = 0`, so `hiS ≠ hi`.
  have h_d : flowBracketBalance tokens lo p ≥ 0 := h_dyck p h_lo_p (by omega)
  have h_lo_hiS_bal : flowBracketBalance tokens lo hiS ≥ 1 := by
    have hc1 := flowBracketBalance_compose tokens lo p hiS h_lo_p (by omega)
    have hc2 := flowBracketBalance_compose tokens p (p + 1) hiS (by omega) (by omega)
    rw [h_open_bal, h_inner] at hc2
    omega
  have h_hiS_lt_hi : hiS < hi := by
    rcases Nat.lt_or_ge hiS hi with h | h
    · exact h
    · have heq : hiS = hi := by omega
      rw [heq] at h_lo_hiS_bal
      omega
  have h_hiS1_hi : hiS + 1 ≤ hi := h_hiS_lt_hi
  -- (5) the three depth-free constructors at `k := p`, `j := hiS`, `hiE := hiS + 1`.
  refine ⟨h_lo_p, hiS + 1, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · exact flowBodyWindow_child_bracket_at tokens lo p hiS hi h_win h_lo_p
      (by omega) h_hiS1_hi h_delta h_jdelta h_inner h_childfloor
  · exact flowBodyContentDeep_child_bracket tokens lo p hiS hi h_deep h_lo_p h_delta h_hiS1_hi
  · exact flowBodyContent_child_bracket tokens lo p hiS hi h_deep h_lo_p h_hiS1_hi h_delta
      h_hiSclose h_childfloor

/-- **`_seq` re-thread of the `enclosingLocate` assemble** —
    `(i'-b-enclosingLocate-assemble-seq-nested-rethread)`, the additive-parallel twin of
    `seqEnclosingLocate_of_seqOpener_nested` (R485) keyed on the root-TRUE weaker guard
    `FlowBodyContentDeepSeq` instead of `FlowBodyContentDeep`.  This is the assemble the `_seq` carrier
    chain actually consumes: the seq recursion is SEEDED at the root window, where `FlowBodyContentDeep`
    is provably FALSE (`flowBodyContentDeep_root_seed_false`, R488) but the re-scoped
    `FlowBodyContentDeepSeq` is TRUE ([[ref-root-seed-needs-root-true-guard]]) — so the whole
    `enclosingLocate` chain must be re-threaded onto the weaker twin family
    ([[ref-rethread-stays-in-weaker-twin-family]], R489), and a RESTRICTION producer cannot upgrade the
    guard back, so every child producer keyed on the strong guard needs its `_seq` sibling.

    **The cost was exactly the two `h_deep`-reading constructor sites, countable by grep before editing.**
    `h_deep` funnels to precisely the two child-bracket constructors at the assemble's tail (sites 1 + 2);
    EVERYTHING ELSE — the `FlowBodyWindow` projections, the located opener `p`, the matching-close locator,
    the child-keyed floor, the `hiS < hi` re-derivation, site 0's `flowBodyWindow_child_bracket_at`
    (guard-NEUTRAL) — is byte-identical to R485 (none of it reads the content guard).  The two edits:

    1. **Site 1** — swap `flowBodyContentDeep_child_bracket` ↦ `flowBodyContentDeepSeq_child_bracket`
       (R489).  The `_seq` deep child producer takes the LOCATED TYPED opener
       `h_open : tokens[p]!.val = .flowSequenceStart` (which R485 already establishes and consumes for the
       close locator) in place of the weaker delta `flowBracketDelta tokens[p]!.val = 1` — strictly more
       information, freely in scope ([[ref-additive-parallel-type-over-shared-edit]]).  Produces
       `FlowBodyContentDeepSeq tokens p (hiS+1)`, the re-scoped guard at the child.
    2. **Site 2** — swap `flowBodyContent_child_bracket` ↦ `flowBodyContent_child_bracket_seq` (R490),
       which DROPS the close argument `h_hiSclose` the strong site-2 passed: the re-scope's unified residual
       routes through the child-bracket floor `h_childfloor` (whose range reaches the close `hiS`), so the
       boundary close-marker is SUBSUMED ([[ref-unified-residual-routes-through-one-invariant]]).  The
       typed `h_open` again replaces the delta.  Produces the SAME depth-`0` `FlowBodyContent tokens p (hiS+1)`.

    So the seq twin's signature swaps `FlowBodyContentDeep ↦ FlowBodyContentDeepSeq` at the `h_deep`
    hypothesis AND the conclusion's middle conjunct; the body changes exactly two `exact` lines.  **This
    CONSUMES R489 + R490** (both verified-but-unconsumed `_seq` child twins retype into consumed ones —
    [[ref-reduction-by-import]], the retype is the progress) and re-uses R485's whole locate/floor skeleton
    unchanged ([[ref-root-seed-recursive-producer-swap]]: the slice/window framing is guard-agnostic, the
    body producer is swapped in).

    Verified-but-unconsumed until `seqWidthEnc_of_recIH_seq` (the R486-twin) wires it into the
    family-NEUTRAL R475 `seqWidthEnc_of_enclosingLocate_and_recIH` to close the seq root carrier: composes
    only landed lemmas (R485's skeleton + R489 + R490 + the neutral site 0) + `omega`, references no sorry
    site, frontier sorry count unchanged at 4; axiom-clean. -/
theorem seqEnclosingLocate_of_seqOpener_nested_seq
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeepSeq tokens lo hi)
    (a b p : Nat)
    (ha : lo ≤ a) (hab : a ≤ b) (hb : b ≤ hi)
    (hbal : flowBracketBalance tokens lo a ≠ 0)
    (hgate : SeqTypedInterior tokens a b)
    (hpa : p < a)
    (h_open : tokens[p]!.val = .flowSequenceStart)
    (h_body_bal : flowBracketBalance tokens (p + 1) a = 0)
    (h_loc_floor : ∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) :
    lo ≤ p ∧ ∃ hiE, b ≤ hiE ∧ hiE ≤ tokens.size ∧ hiE ≤ hi ∧
      FlowBodyWindow tokens p hiE ∧ FlowBodyContentDeepSeq tokens p hiE ∧
      FlowBodyContent tokens p hiE := by
  have h_dyck := h_win.dyck
  have h_bal := h_win.balanced
  have h_wt := h_win.wellTyped
  have h_hi_lt := h_win.hi_lt
  obtain ⟨_h_gbal, _h_gtop, h_gate_floor⟩ := hgate
  have h_a_hi : a ≤ hi := by omega
  have h_hi_sz : hi ≤ tokens.size := Nat.le_of_lt h_hi_lt
  -- (1) `lo ≤ p` — the opener cannot precede the window start (FLOOR read, depth-free).
  have h_lo_p : lo ≤ p :=
    seqLocatedOpener_within_body tokens lo hi a p ha h_a_hi h_dyck hbal hpa h_body_bal h_loc_floor
  -- (2) locate the matching close `hiS` — the R484 depth-general `_nested` close (pure SWAP: no `h_p_depth`).
  obtain ⟨hiS, h_a_hiS, h_b_hiS, h_hiS_hi, h_hiS_sz, h_inner, h_hiSclose, h_floor⟩ :=
    seqClose_of_located_and_enclosing_within_nested tokens a b lo p hi h_lo_p hpa hab hb h_hi_sz
      h_bal h_dyck h_open h_body_bal h_loc_floor h_gate_floor h_wt
  -- opener delta + single-step balance `balance p (p+1) = 1`.
  have h_p_sz : p < tokens.size := by omega
  have h_delta : flowBracketDelta tokens[p]!.val = 1 := by rw [h_open]; rfl
  have h_open_bal : flowBracketBalance tokens p (p + 1) = 1 := by
    have hlen : p < tokens.toList.length := by rw [Array.length_toList]; exact h_p_sz
    have h1 : tokens.toList[p]'hlen = tokens[p] := Array.getElem_toList h_p_sz
    have h2 : tokens[p] = tokens[p]! := (getElem!_pos tokens p h_p_sz).symm
    rw [flowBracketBalance_single tokens p hlen, h1, h2, h_delta]
  -- (3) child-keyed floor `balance p i ≥ 1` via one compose through the opener.
  have h_childfloor : ∀ i, p + 1 ≤ i → i ≤ hiS → flowBracketBalance tokens p i ≥ 1 := by
    intro i hi1 hi2
    have hc := flowBracketBalance_compose tokens p (p + 1) i (by omega) hi1
    have hf := h_floor i hi1 hi2
    rw [h_open_bal] at hc
    omega
  -- closer delta from the typed close.
  have h_jdelta : flowBracketDelta tokens[hiS]!.val = -1 := by rw [h_hiSclose]; rfl
  -- (4) `hiS < hi` — re-derived from the enclosing Dyck floor `d := balance lo p ≥ 0`.
  have h_d : flowBracketBalance tokens lo p ≥ 0 := h_dyck p h_lo_p (by omega)
  have h_lo_hiS_bal : flowBracketBalance tokens lo hiS ≥ 1 := by
    have hc1 := flowBracketBalance_compose tokens lo p hiS h_lo_p (by omega)
    have hc2 := flowBracketBalance_compose tokens p (p + 1) hiS (by omega) (by omega)
    rw [h_open_bal, h_inner] at hc2
    omega
  have h_hiS_lt_hi : hiS < hi := by
    rcases Nat.lt_or_ge hiS hi with h | h
    · exact h
    · have heq : hiS = hi := by omega
      rw [heq] at h_lo_hiS_bal
      omega
  have h_hiS1_hi : hiS + 1 ≤ hi := h_hiS_lt_hi
  -- (5) the three constructors at `k := p`, `j := hiS`, `hiE := hiS + 1` — sites 1 + 2 are the `_seq` twins.
  refine ⟨h_lo_p, hiS + 1, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · exact flowBodyWindow_child_bracket_at tokens lo p hiS hi h_win h_lo_p
      (by omega) h_hiS1_hi h_delta h_jdelta h_inner h_childfloor
  · exact flowBodyContentDeepSeq_child_bracket tokens lo p hiS hi h_deep h_lo_p h_open h_hiS1_hi
  · exact flowBodyContent_child_bracket_seq tokens lo p hiS hi h_deep h_lo_p h_hiS1_hi h_open
      h_childfloor

/-- **The `enclosingLocate` boundary WIRED into the width-enc lift** —
    `(i'-b-enclosingLocate-wired-seq)`, R475 `seqWidthEnc_of_enclosingLocate_and_recIH` with its
    abstracted `enclosingLocate` hypothesis DISCHARGED by the now-landed depth-general assemble
    `seqEnclosingLocate_of_seqOpener_nested` (R485).  This is the (α) locate boundary's final seq
    closure: from just the body-window facts (`FlowBodyWindow`/`FlowBodyContentDeep tokens lo hi`) and
    the outer body-width `recIH`, it produces the full width-enc conclusion — no abstracted locator
    hypothesis, no depth-`0` fact, no typed-opener discriminator left to supply.

    **Two discharges, both free.**
    1. **The depth obligation** — R485's `_nested` assemble already shed `h_p_depth`
       ([[ref-depth-hyp-cost-is-its-equality-reads]]); descending the seq recursion lands the enclosing
       opener `p` at depth `d := balance lo p ≥ 0`, and the assemble re-derived every depth-`0` read
       from the enclosing Dyck floor.  So there is NO depth-`0` fact for this wiring to provide.
    2. **The typed-opener discriminator** — R485 takes `h_open : tokens[p]!.val = .flowSequenceStart`,
       but R475's `enclosingLocate` slot only offers the weaker delta
       `flowBracketDelta tokens[p]!.val = 1`.  The gap is closed FOR FREE by
       `seqOpenerType_of_located_and_gate` ([[ref-prefix-gate-reconstructed-from-boundary]]): the gate's
       `btFold`-top marker `hgate.2.1` (`SeqTypedInterior`'s middle conjunct,
       `(btFold (some []) (take a)).bind head? = some true`) plus the four locator facts force the
       located opener to a `[` — a `{` would push `false` and the interior floor cannot pop it back,
       contradicting the `= some true` head.  The delta `= 1` alone can't decide `[` vs `{`; the gate's
       enclosing-type mark is what disambiguates.

    So the residual the assemble owed (`h_open`) is RECONSTRUCTED in place from the gate, not threaded
    ([[ref-reconstruct-in-place-over-relocate]]).  **This CONSUMES R485** (the verified-but-unconsumed
    `_nested` assemble retypes into a consumed one — [[ref-reduction-by-import]], the retype is the
    progress) and applies R475 to it, eliminating the `enclosingLocate` abstraction.  Per
    [[ref-fold-consumer-chain-to-producer-contract]] the result reads off the (α) boundary's whole spec
    as one signature whose ONLY inputs are the producer's contract (the body-window facts + the
    width-recursion IH).

    Verified-but-unconsumed until the `desc`/`seqWindowRecSeqBody` driver consumes it: composes only
    landed lemmas (R475 + R485 + `seqOpenerType_of_located_and_gate`), references no sorry site, frontier
    sorry count unchanged at 4; axiom-clean. -/
theorem seqWidthEnc_of_recIH
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeep tokens lo hi)
    (recIH : ∀ lo' hi', hi' - lo' < hi - lo → lo ≤ lo' → hi' ≤ hi →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' →
        SeqEnclosed tokens lo' → tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo')) :
    ∀ a b p, lo ≤ a → a ≤ b → b ≤ hi →
        flowBracketBalance tokens lo a ≠ 0 →
        SeqTypedInterior tokens a b →
        p < a → flowBracketDelta tokens[p]!.val = 1 →
        flowBracketBalance tokens (p + 1) a = 0 →
        (∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) →
        ∃ hiE, b ≤ hiE ∧ hiE ≤ tokens.size ∧
          FlowBodyWindow tokens p hiE ∧ FlowBodyContentDeep tokens p hiE ∧
          FlowBodyContent tokens p hiE ∧
          (∀ lo' hi', hi' - lo' < hiE - p → p ≤ lo' → hi' ≤ hiE →
            FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' →
            SeqEnclosed tokens lo' → tokens[hi']!.val = .flowSequenceEnd →
            RecSeqBody ((tokens.toList.take hi').drop lo')) := by
  have h_hi_lt := h_win.hi_lt
  refine seqWidthEnc_of_enclosingLocate_and_recIH tokens lo hi ?_ recIH
  intro a b p ha hab hb hbal hgate hpa h_delta h_body_bal h_loc_floor
  -- the typed opener `[` is RECONSTRUCTED from the gate's mark (`hgate.2.1`) + the four locator facts;
  -- the weaker delta `= 1` alone cannot decide `[` vs `{`.
  have h_a_sz : a ≤ tokens.size := by omega
  have h_open : tokens[p]!.val = .flowSequenceStart :=
    seqOpenerType_of_located_and_gate tokens a p hpa h_a_sz h_delta h_body_bal h_loc_floor hgate.2.1
  -- R485's depth-general assemble: no `h_p_depth` to supply.
  exact seqEnclosingLocate_of_seqOpener_nested tokens lo hi h_win h_deep a b p
    ha hab hb hbal hgate hpa h_open h_body_bal h_loc_floor

/-- **The `_seq` twin of the wired width-enc lift — a TRANSPORT+CONSTRUCT link re-keys via two NAMED
    swaps to its already-landed children.** `(i'-b-B2c-(d)-seq-carrier-of-recIH-seq)`, R493: the
    `FlowBodyContentDeepSeq`-keyed twin of R486 `seqWidthEnc_of_recIH`, re-keyed off the root-FALSE strong
    content guard onto its root-TRUE weaker twin ([[ref-root-seed-needs-root-true-guard]] R488,
    [[ref-rethread-stays-in-weaker-twin-family]] R489).  This is the next link of the `_seq` re-thread
    after the per-step ASSEMBLE `seqWidthEnc_of_enclosingLocate_and_recIH_seq` (R492): from just the
    body-window facts (`FlowBodyWindow` / `FlowBodyContentDeepSeq tokens lo hi`) and the outer body-width
    `recIH`, it produces the full `_seq`-keyed width-enc conclusion — no abstracted locator hypothesis,
    no depth-`0` fact, no typed-opener discriminator left to supply.

    **The find — R486 is a TRANSPORT+CONSTRUCT link, so its twin is exactly TWO named swaps.**  Classify
    R486's body by what each of its three composition sites does with the guard
    ([[ref-transporting-lemma-twin-zero-body-edits]] R492):
    1. `refine seqWidthEnc_of_enclosingLocate_and_recIH tokens lo hi ?_ recIH` — the per-step assemble
       lift.  It TRANSPORTS the guard (threads the strong `recIH` straight in, refines the deliverable),
       so it never reads the guard — but its NAME is guard-keyed, so the twin swaps the call to the
       transporting twin `seqWidthEnc_of_enclosingLocate_and_recIH_seq` (R492, now in place).
    2. `seqOpenerType_of_located_and_gate …` — the typed-opener reconstruction
       ([[ref-prefix-gate-reconstructed-from-boundary]]).  Guard-NEUTRAL (it names no content guard at
       all), so it is unchanged, character-for-character from R486.
    3. `exact seqEnclosingLocate_of_seqOpener_nested tokens lo hi h_win h_deep …` — the leaf locate.  It
       CONSTRUCTS the `_seq` deliverable from the `_seq` `h_deep`, so the twin swaps the call to the
       constructing leaf twin `seqEnclosingLocate_of_seqOpener_nested_seq` (R491).

    So the body cost is exactly TWO name swaps — one to the transporting twin (R492), one to the
    constructing twin (R491) — both pointing at children landed in prior turns; the guard-neutral opener
    reconstruction is untouched.  The signature swaps the guard type at its four positions (`h_deep`, the
    `recIH` premise, the conclusion deliverable, the conclusion IH premise).  This is the chain's
    front-loading made concrete ([[ref-transporting-lemma-twin-zero-body-edits]]): every per-turn child
    twin lands first, then a lift like this one is a mechanical re-point to those twins — no proof content
    re-derived, the locate/assemble/reconstruct logic all consumed from the already-verified siblings
    ([[ref-reduction-by-import]], the retype is the progress; [[ref-fold-consumer-chain-to-producer-contract]],
    the result reads off the (α) boundary's whole seq spec as one signature).

    Verified-but-unconsumed until the seq carrier consumer (`seqLocalCarrier_of_widthEnc`'s twin) feeds
    it: composes only landed lemmas (R492 + R491 + the guard-neutral `seqOpenerType_of_located_and_gate`),
    references no sorry site, frontier sorry count unchanged at 4; axioms identical to R486 (the two swapped
    children share R485/R484's footprint). -/
theorem seqWidthEnc_of_recIH_seq
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeepSeq tokens lo hi)
    (recIH : ∀ lo' hi', hi' - lo' < hi - lo → lo ≤ lo' → hi' ≤ hi →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeepSeq tokens lo' hi' →
        SeqEnclosed tokens lo' → tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo')) :
    ∀ a b p, lo ≤ a → a ≤ b → b ≤ hi →
        flowBracketBalance tokens lo a ≠ 0 →
        SeqTypedInterior tokens a b →
        p < a → flowBracketDelta tokens[p]!.val = 1 →
        flowBracketBalance tokens (p + 1) a = 0 →
        (∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) →
        ∃ hiE, b ≤ hiE ∧ hiE ≤ tokens.size ∧
          FlowBodyWindow tokens p hiE ∧ FlowBodyContentDeepSeq tokens p hiE ∧
          FlowBodyContent tokens p hiE ∧
          (∀ lo' hi', hi' - lo' < hiE - p → p ≤ lo' → hi' ≤ hiE →
            FlowBodyWindow tokens lo' hi' → FlowBodyContentDeepSeq tokens lo' hi' →
            SeqEnclosed tokens lo' → tokens[hi']!.val = .flowSequenceEnd →
            RecSeqBody ((tokens.toList.take hi').drop lo')) := by
  have h_hi_lt := h_win.hi_lt
  refine seqWidthEnc_of_enclosingLocate_and_recIH_seq tokens lo hi ?_ recIH
  intro a b p ha hab hb hbal hgate hpa h_delta h_body_bal h_loc_floor
  -- the typed opener `[` is RECONSTRUCTED from the gate's mark (`hgate.2.1`) + the four locator facts;
  -- the weaker delta `= 1` alone cannot decide `[` vs `{`.  Guard-NEUTRAL: unchanged from R486.
  have h_a_sz : a ≤ tokens.size := by omega
  have h_open : tokens[p]!.val = .flowSequenceStart :=
    seqOpenerType_of_located_and_gate tokens a p hpa h_a_sz h_delta h_body_bal h_loc_floor hgate.2.1
  -- R491's `_seq` leaf assemble: the constructing swap (builds the `_seq` deliverable from `_seq` `h_deep`).
  exact seqEnclosingLocate_of_seqOpener_nested_seq tokens lo hi h_win h_deep a b p
    ha hab hb hbal hgate hpa h_open h_body_bal h_loc_floor

/-- **The seq local CARRIER from the body-width `recIH`** — `(i'-b-B2c-(d)-seq-carrier-of-recIH)`,
    R487: the carrier ↔ `SafeBodyUnit` half of the width co-construction, now reduced to its THREE
    genuine inputs.  Given one body window `[lo, hi)`'s own facts (`FlowBodyWindow` /
    `FlowBodyContentDeep`), that window's own `SafeBodyUnit ContentStartTok ((take hi).drop lo)`, and
    the body-width `RecSeqBody`-IH for every STRICTLY-NARROWER window, it builds the local carrier
    `SeqInteriorSeparators tokens lo hi`.

    **This CONSUMES `seqWidthEnc_of_recIH` (R486)** — the verified-but-unconsumed wired `enclosingLocate`
    boundary retypes into a consumed one ([[ref-reduction-by-import]], retype-is-progress).  The body is
    a two-step funnel that folds the whole `widthEnc` chain into one signature
    ([[ref-fold-consumer-chain-to-producer-contract]]):

    1. `seqWidthEnc_of_recIH tokens lo hi h_win h_deep recIH` turns the body-width `recIH` into the
       `h_widthEnc` deliverable — its conclusion is TERM-FOR-TERM `seqLocalCarrier_of_widthEnc`'s
       `h_widthEnc` hypothesis (the per-window enclosing-facts + narrower-`RecSeqBody`-IH supplier).
    2. `seqLocalCarrier_of_widthEnc tokens lo hi (Nat.le_of_lt h_win.hi_lt) h_safe …` consumes that plus
       the window's own `SafeBodyUnit` to assemble the carrier.

    **Why the `SafeBodyUnit` input is sibling-supplied, not external.**  Of the three inputs, the
    body-window facts and the `recIH` are genuine externals the joint induction's STEP already holds,
    but `h_safe` is the projection (`RecSeqBody.toSafeBodyUnit`) of the SIBLING half's output — the
    window's OWN `RecSeqBody ((take hi).drop lo)`, the recursion conjunct the same joint step produces.
    So this lemma names the CARRIER half of the carrier↔`RecSeqBody` co-construction whose two halves
    share ONE width measure: the recursion half produces this window's `RecSeqBody` (consuming the
    carrier only at sub-windows, gated `< hi - lo`), and THIS half projects that `RecSeqBody` to
    `h_safe` and returns the carrier.  No circularity — the sibling consumes the width-narrower IH, not
    this window's carrier ([[ref-consumer-joint-before-producer]] / [[ref-producer-dual-of-consumer-joint]]).

    Verified-but-unconsumed until the joint `windowWidth_strongRecOn` co-construction supplies `h_safe`
    (from the recursion half) + `recIH` (from the width IH) and pairs the result with the window's
    `RecSeqBody`: composes only landed lemmas (R486 + R446), references no sorry site, frontier sorry
    count unchanged at 4; axiom-clean. -/
theorem seqLocalCarrier_of_recIH
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeep tokens lo hi)
    (h_safe : SafeBodyUnit ContentStartTok ((tokens.toList.take hi).drop lo))
    (recIH : ∀ lo' hi', hi' - lo' < hi - lo → lo ≤ lo' → hi' ≤ hi →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' →
        SeqEnclosed tokens lo' → tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo')) :
    SeqInteriorSeparators tokens lo hi :=
  seqLocalCarrier_of_widthEnc tokens lo hi (Nat.le_of_lt h_win.hi_lt) h_safe
    (seqWidthEnc_of_recIH tokens lo hi h_win h_deep recIH)

/-- **The `_seq` twin of the carrier-from-recIH funnel — the CONVERGENCE NODE where the two re-threaded
    sub-chains JOIN, priced by the funnel-twin cost law (two named swaps).**
    `(i'-b-B2c-(d)-seq-localCarrier-of-recIH-seq)`, R498: the `FlowBodyContentDeepSeq`-keyed twin of R487
    `seqLocalCarrier_of_recIH`, re-keyed off the root-FALSE strong content guard onto its root-TRUE weaker
    twin ([[ref-root-seed-needs-root-true-guard]] R488, [[ref-rethread-stays-in-weaker-twin-family]] R489).
    This is the consume-ready entry point the eventual joint width induction CALLS at each window: given the
    step's own facts (`FlowBodyWindow` / `FlowBodyContentDeepSeq tokens lo hi`), that window's own
    `SafeBodyUnit` (the sibling `RecSeqBody` half's projection), and the body-width `recIH`, it returns the
    local carrier `SeqInteriorSeparators tokens lo hi` — folding the WHOLE `_seq` carrier sub-chain into one
    signature whose hypotheses are exactly what the joint step holds
    ([[ref-fold-consumer-chain-to-producer-contract]]).

    **The find — this is the CONVERGENCE NODE, and a convergence-node twin confirms the funnel cost law.**
    R487 is where the two `_seq` sub-chains MEET window-parametrically: the PRODUCER sub-chain
    (`recIH ↦ h_widthEnc`, R493 `seqWidthEnc_of_recIH_seq`) and the CONSUMER sub-chain
    (`h_widthEnc + h_safe ↦ carrier`, R496 `seqLocalCarrier_of_widthEnc_seq`).  R487's body composes exactly
    those two guard-keyed children, feeding R493's output straight into R496's input — so the producer/consumer
    MEET happens INSIDE this funnel (the window-parametric INTERNAL dual of R497's root-instance EXTERNAL meet
    [[ref-thin-instance-twin-is-producer-consumer-meet]], which specializes R496 alone and takes `h_widthEnc`
    from outside).  By the funnel-twin cost law ([[ref-lift-rekeys-by-guard-keyed-child-names]] R493) the twin
    is exactly #(guard-keyed children) = TWO named swaps:
      1. `seqLocalCarrier_of_widthEnc ↦ seqLocalCarrier_of_widthEnc_seq` (R496, the consumer half),
      2. `seqWidthEnc_of_recIH ↦ seqWidthEnc_of_recIH_seq` (R493, the producer half).
    The guard-NEUTRAL plumbing transports verbatim: the width bound `Nat.le_of_lt h_win.hi_lt` and — note,
    correcting R493's NEXT — `h_safe` is an EXPLICIT pass-through hypothesis, NOT an internal
    `RecSeqBody.toSafeBodyUnit` projection (the projection lives in the joint induction's recursion half, not
    here).  Signature re-keys the guard at its two positions (`h_deep`, the `recIH` premise).

    **A convergence-node twin can ONLY land after BOTH incoming sub-chains are twinned** — the bottom-up
    order the whole re-thread followed: constructing leaves first (R489/R490/R491, priced by guard read
    sites), then plumbing/funnels (R492/R493), then this JOIN, then the thin root instance (R497).  With this
    brick the ENTIRE `_seq` carrier-from-recIH funnel is twinned at both levels — window-parametric (this) and
    root-instance (R497) — so the carrier side of the seq co-construction is complete; the single remaining
    seq residual is the joint `windowWidth_strongRecOn` that supplies `h_safe` (recursion half) + `recIH`
    (width IH).

    Verified-but-unconsumed until that joint induction feeds it: composes only landed lemmas (R496 + R493),
    references no sorry site, frontier sorry count unchanged at 4; axioms identical to its strong R487 parent
    (the two swapped children share R446/R485's footprint). -/
theorem seqLocalCarrier_of_recIH_seq
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeepSeq tokens lo hi)
    (h_safe : SafeBodyUnit ContentStartTok ((tokens.toList.take hi).drop lo))
    (recIH : ∀ lo' hi', hi' - lo' < hi - lo → lo ≤ lo' → hi' ≤ hi →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeepSeq tokens lo' hi' →
        SeqEnclosed tokens lo' → tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo')) :
    SeqInteriorSeparators tokens lo hi :=
  seqLocalCarrier_of_widthEnc_seq tokens lo hi (Nat.le_of_lt h_win.hi_lt) h_safe
    (seqWidthEnc_of_recIH_seq tokens lo hi h_win h_deep recIH)

/-- **The per-window carrier→content consumer joint** — `(i'-b-B3-content-joint)`, the joint between
    the threaded separator carrier and the `RecSeqBody` recursion's per-window dispatch.  This is the
    de-risk finding for B3 (the `windowWidth_strongRecOn` `RecSeqBody` producer) made into a proof
    term: it pins the EXACT interface by which the recursion step obtains its `FlowBodyContent` (the
    fact `recseqentry_window_dispatch` consumes) from the carrier, and NAMES the single residual the
    step's guard `G` must still carry.

    `recseqentry_window_dispatch` needs `FlowBodyContent tokens lo hi` at every recursion window.  At a
    DESCENDED window `FlowBodyContent` is NOT obtainable by re-basing the parent's (R296: `bodySucc`
    has no all-depth balance-free form, and `flowBodyContent_advance` carries only the ADVANCE edge —
    there is deliberately no `flowBodyContent_descend`); it can only come from
    `flowBodyContent_of_deep`, which projects the recursion-stable `FlowBodyContentDeep` to
    `FlowBodyContent` USING the two separator facts (`bodySuccFact` / `noTrailingSepFact`).  Those two
    facts are exactly what `SeqInteriorSeparators` carries — instantiated at the window itself
    `(a,b) = (lo,hi)` (`bodySuccFact`/`noTrailingSepFact` are term-for-term `flowBodyContent_of_deep`'s
    `h_bodySucc`/`h_noTrailingSep` premises — [[ref-conjunct-of-projection-is-free-field]]).

    Two findings the proof embodies ([[ref-fold-consumer-chain-to-producer-contract]] — folding the
    instantiate + project chain into one lemma keyed on the dispatch's input):

    1. **The root carrier narrows to EVERY recursion window for free.**  `SeqInteriorSeparators` is a
       subset restriction (`SeqInteriorSeparators_narrow`), and `FlowBodyWindow` carries `2 ≤ lo`
       (`lo_ge`) and `hi ≤ size - 2` (`hi_le`) — the EXACT narrow bounds from the root span
       `[2, size - 2)`.  So the carrier need NOT be threaded as a `G`-conjunct: the once-seeded root
       carrier (`seqRoot_seqInteriorSeparators`) is supplied as an ambient hypothesis and narrowed in
       place at each window.  This is [[ref-narrow-from-root-breaks-rederivation-cycle]]'s coverage
       de-risk discharged structurally: every recursion window lies WITHIN the root span by the guard's
       own frame fields.

    2. **The carrier's gate `SeqTypedInterior tokens lo hi` is `⟨balanced, enclosing-btFold-top,
       dyck⟩`** — and `FlowBodyWindow` supplies the balance (`balanced`) and Dyck (`dyck`) conjuncts,
       leaving the enclosing-`[` btFold-top fact `h_enclosed` as the SINGLE residual.  This NAMES the
       one fact B3's `G` must additionally carry (a `SeqEnclosed`-style conjunct keyed only on `lo`:
       `(btFold (some []) (take lo)).bind (·.head?) = some true`) — supplied at the root window from
       `tokens[lo - 1]! = .flowSequenceStart`, and preserved across descend (the located opener at `k`
       pushes `true`) / advance (the depth-`0` separator leaves the enclosing stack top unchanged).
       The seq IH only ever descends into nested `[` (the `{` branch is the near-leaf map oracle, no
       seq IH), so every window it sees is genuinely seq-typed and this residual always holds.

    Verified-but-unconsumed until the B3 fixpoint instantiates `windowWidth_strongRecOn` and threads
    `h_enclosed` (R225 discipline): composes only landed lemmas, references no sorry site, frontier
    sorry count unchanged at 4; axiom-clean. -/
theorem seqWindow_flowBodyContent_general (tokens : Array (Positioned YamlToken))
    (lo0 hi0 lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeep tokens lo hi)
    (h_enclosed : SeqEnclosed tokens lo)
    (h_carrier0 : SeqInteriorSeparators tokens lo0 hi0)
    (h_lo0 : lo0 ≤ lo) (h_hi0 : hi ≤ hi0) :
    FlowBodyContent tokens lo hi := by
  -- The gate: balance + Dyck come from the window guard; only the enclosing-`[` btFold-top is owed.
  have h_gate : SeqTypedInterior tokens lo hi :=
    ⟨h_win.balanced, h_enclosed, h_win.dyck⟩
  -- The enclosing carrier narrows to `[lo, hi) ⊆ [lo0, hi0)` by the SUPPLIED bounds (window-absolute body).
  have h_carrier : SeqInteriorSeparators tokens lo hi :=
    SeqInteriorSeparators_narrow h_lo0 h_hi0 h_carrier0
  -- Instantiate at the window itself; the two facts are exactly `flowBodyContent_of_deep`'s premises.
  obtain ⟨h_bs, h_nts⟩ :=
    h_carrier lo hi (Nat.le_refl lo) (Nat.le_of_lt h_win.lo_lt_hi) (Nat.le_refl hi) h_gate
  exact flowBodyContent_of_deep tokens lo hi h_deep h_bs h_nts

/-- **The root-span instance of `seqWindow_flowBodyContent_general`** — `lo0 := 2`, `hi0 := size-2`,
    bounds read off `FlowBodyWindow.lo_ge`/`hi_le`.  Signature-preserving so the existing
    `seqWindowRecSeqBody` consumers (which thread the root carrier `SeqInteriorSeparators tokens 2 (size-2)`)
    are untouched. -/
theorem seqWindow_flowBodyContent (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeep tokens lo hi)
    (h_enclosed : SeqEnclosed tokens lo)
    (h_root_carrier : SeqInteriorSeparators tokens 2 (tokens.size - 2)) :
    FlowBodyContent tokens lo hi :=
  seqWindow_flowBodyContent_general tokens 2 (tokens.size - 2) lo hi
    h_win h_deep h_enclosed h_root_carrier h_win.lo_ge h_win.hi_le

/-- **The RE-SCOPED `FlowBodyContent` window projector** — `(i'-b-B2c-(d)-seq-rec)`, the `_seq` twin of
    `seqWindow_flowBodyContent` (just above) consuming `FlowBodyContentDeepSeq` (R393's root-TRUE guard) in
    place of the false-rooted `FlowBodyContentDeep`.  The first brick of the (R2) consumer re-thread the
    R415 next step queued: `seqWindowRecSeqBody`'s per-window `step` produces `FlowBodyContent` here, so this
    must migrate before the recursion does.

    Unlike R415's dispatch/oracle clones (one-line: a derived `have` becomes a supplied hypothesis), the
    re-thread of THIS consumer is NOT a one-liner — the re-scope added `tokens[k+1] ≠ .key` to the guard's
    `feContentStart`, and at the consume site that premise is exactly the content-start the field would
    deliver, so the guard can no longer self-supply the interior separator content fact.  Instead the
    uniform separator-content (every depth-`0` separator `k`, interior OR boundary, has a content successor)
    is re-sourced from the SEPARATOR CARRIER's `noTrailingSepFact` instantiated at the NARROWED window
    `[lo, k+1)` — the carrier already proves it (the guard's `feContentStart` was a redundant second source),
    and `[lo, k+1)` is seq-typed by the same balance/enclosure/floor facts the whole window carries, with the
    separator's delta-`0` returning the prefix balance to `0` ([[ref-window-absolute-gate-subset-restriction]]:
    the carrier's window-absolute body restricts to any seq-typed sub-window for free).  Only `headContentStart`
    is read off the re-scoped guard (re-scope-invariant).

    Verified-but-unconsumed until `seqWindowRecSeqBody_seq` threads it (R225): composes only landed lemmas,
    references no sorry site, frontier sorry count unchanged at 4; axiom-clean. -/
theorem seqWindow_flowBodyContent_seq_general (tokens : Array (Positioned YamlToken))
    (lo0 hi0 lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeepSeq tokens lo hi)
    (h_enclosed : SeqEnclosed tokens lo)
    (h_carrier0 : SeqInteriorSeparators tokens lo0 hi0)
    (h_lo0 : lo0 ≤ lo) (h_hi0 : hi ≤ hi0) :
    FlowBodyContent tokens lo hi := by
  -- The enclosing carrier narrows to `[lo, hi) ⊆ [lo0, hi0)` by the SUPPLIED bounds (window-absolute body).
  have h_carrier : SeqInteriorSeparators tokens lo hi :=
    SeqInteriorSeparators_narrow h_lo0 h_hi0 h_carrier0
  -- bodySucc at the whole window: gate from balance (window) + enclosure mark + floor (window).
  have h_gate : SeqTypedInterior tokens lo hi :=
    ⟨h_win.balanced, h_enclosed, h_win.dyck⟩
  have h_bodySucc :=
    (h_carrier lo hi (Nat.le_refl lo) (Nat.le_of_lt h_win.lo_lt_hi) (Nat.le_refl hi) h_gate).1
  -- uniform separator-content: every depth-`0` separator `k` has a content successor, sourced from the
  -- carrier's `noTrailingSepFact` on the NARROWED window `[lo, k+1)` (where `k` IS the boundary position).
  have h_feContent : ∀ k, lo ≤ k → k < hi →
      tokens[k]!.val = .flowEntry →
      flowBracketBalance tokens lo k = 0 →
      isFlowContentStart tokens[k + 1]!.val := by
    intro k hk1 hk2 hfe hbal
    have h_k_sz : k < tokens.size := by have := h_win.hi_lt; omega
    have h_k_len : k < tokens.toList.length := by rw [Array.length_toList]; exact h_k_sz
    have h_k_val : tokens[k]! = tokens.toList[k]'h_k_len := by
      rw [getElem!_pos tokens k h_k_sz, Array.getElem_toList]
    have h_delta_k : flowBracketDelta tokens[k]!.val = 0 := by
      rw [hfe]; exact flowBracketDelta_flowEntry
    have h_single_k : flowBracketBalance tokens k (k + 1) = flowBracketDelta tokens[k]!.val := by
      rw [flowBracketBalance_single tokens k h_k_len, ← h_k_val]
    have h_bal_k1 : flowBracketBalance tokens lo (k + 1) = 0 := by
      have hc := flowBracketBalance_compose tokens lo k (k + 1) hk1 (Nat.le_succ k)
      rw [hbal, h_single_k, h_delta_k] at hc; omega
    -- `[lo, k+1)` is seq-typed: the SAME enclosure mark (keyed on `take lo`), the restricted floor.
    have h_gate_k : SeqTypedInterior tokens lo (k + 1) :=
      ⟨h_bal_k1, h_enclosed, fun i h1 h2 => h_win.dyck i h1 (by omega)⟩
    have h_nts :=
      (h_carrier lo (k + 1) (Nat.le_refl lo) (by omega) (by omega) h_gate_k).2
    exact h_nts k hk1 rfl hfe hbal
  exact flowBodyContent_of_deepSeq tokens lo hi h_deep h_bodySucc h_feContent

/-- **The root-span instance of `seqWindow_flowBodyContent_seq_general`** — `lo0 := 2`, `hi0 := size-2`,
    bounds read off `FlowBodyWindow.lo_ge`/`hi_le`.  Signature-preserving so `seqWindowRecSeqBody_seq` is
    untouched. -/
theorem seqWindow_flowBodyContent_seq (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeepSeq tokens lo hi)
    (h_enclosed : SeqEnclosed tokens lo)
    (h_root_carrier : SeqInteriorSeparators tokens 2 (tokens.size - 2)) :
    FlowBodyContent tokens lo hi :=
  seqWindow_flowBodyContent_seq_general tokens 2 (tokens.size - 2) lo hi
    h_win h_deep h_enclosed h_root_carrier h_win.lo_ge h_win.hi_le

/-- **The CARRIER-FREE root seed for `FlowBodyContent`** — `(i'-b-B2c-desc-fixpoint)`, the base case of
    the `FlowBodyContent` thread that BREAKS the carrier↔recursion co-construction circularity (R318/R340).

    `seqWindow_flowBodyContent` (just above) sources a window's `FlowBodyContent` from the ambient root
    carrier `SeqInteriorSeparators tokens 2 (size-2)` — but that carrier is precisely what the seq
    `desc` producer is trying to BUILD (`seqRoot_seqInteriorSeparators`'s `desc` funnels through it).  So
    routing the recursion's per-window `FlowBodyContent` through it is circular.  The R341 next-step's
    probe asked: can `FlowBodyContent` instead be threaded as a recursion `G`-conjunct, seeded ONCE at
    the root from the FLAT producer and propagated by the two landed edges — never re-entering the
    carrier ([[ref-narrow-from-root-breaks-rederivation-cycle]])?  The two edges are already theorems:

    * DESCEND — `flowBodyContent_descend` (above): at a descended seq window `[p+1, j)` the child
      separator facts come from the child's OWN `SafeBodyUnit` (`seqChild_safeBodyUnit`, drawn carrier-free
      from the width IH), NOT from re-basing the parent's `bodySucc` (which has no all-depth balance-free
      form — R296), so it SIDESTEPS that obstruction by consuming the recursion's own `RecSeqBody` output;
    * ADVANCE — `flowBodyContent_advance` (`NonemptyStructure`): a pure depth-`0` re-basing, no IH.

    This brick supplies the remaining piece — the BASE case at `[2, size-2)` — by the SAME chain the
    descend edge uses (`seqSeparatorFacts_of_windowed_safebodyunit ▸ flowBodyContent_of_deep`), but fed
    the FLAT `seqRoot_safeBodyUnit` (scanned straight off emission, no `RecSeqBody`) in place of the IH's
    child `SafeBodyUnit`.  `FlowBodyContentDeep` at the root is taken as a hypothesis (the consumer
    supplies it, mirroring `seqWindowRecSeqBody`'s `h_deep0` interface).  With this, the per-window
    `FlowBodyContent` SOURCE is complete carrier-free: root seed (here) + descend + advance, the
    [[ref-universal-producer-root-seed-first]] base of a recursion whose edges are landed.

    Verified-but-unconsumed until the carrier-free `windowWidth_strongRecOn` threads `FlowBodyContent` as
    a `G`-conjunct (R225): composes only landed lemmas, references no sorry site, frontier sorry count
    unchanged at 4; axiom-clean. -/
theorem seqRoot_flowBodyContent
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v)
    (h_deep : FlowBodyContentDeep tokens 2 (tokens.size - 2)) :
    FlowBodyContent tokens 2 (tokens.size - 2) := by
  -- The flat root `SafeBodyUnit` (off emission, NO `RecSeqBody`) yields both separator facts.
  have h_safe : SafeBodyUnit ContentStartTok ((tokens.toList.take (tokens.size - 2)).drop 2) :=
    seqRoot_safeBodyUnit items tokens h_scan h_ne h_all
  obtain ⟨h_bs, h_nts⟩ :=
    seqSeparatorFacts_of_windowed_safebodyunit tokens 2 (tokens.size - 2)
      (Nat.sub_le tokens.size 2) h_safe
  exact flowBodyContent_of_deep tokens 2 (tokens.size - 2) h_deep h_bs h_nts

/-- **The CARRIER-FREE root seed for `FlowBodyContent`, RE-SCOPED twin** — `(i'-b-B2c-desc-fixpoint-seq)`,
    the `_seq` twin of `seqRoot_flowBodyContent` (just above) over the root-TRUE `FlowBodyContentDeepSeq`
    (R393), and the BASE case that — together with the descend edge `flowBodyContent_descend_seq` (R500)
    and the guard-NEUTRAL advance edge `flowBodyContent_advance` — COMPLETES the carrier-free
    `FlowBodyContent` thread for the seq axis.

    Where `seqRoot_flowBodyContent` takes the strong `FlowBodyContentDeep tokens 2 (size-2)` as its root
    hypothesis — a guard R392 proved FALSE on real emitter output ([[ref-restriction-hides-root-falsity]]),
    so that root seed is never actually instantiable — this `_seq` twin takes the root-TRUE
    `FlowBodyContentDeepSeq tokens 2 (size-2)` ([[ref-root-seed-needs-root-true-guard]], satisfiability
    machine-checked by `flowBodyContentDeepSeq_root_holds_nested_scalar`), the guard the JOINT
    `windowWidth_strongRecOn` co-construction's recursion conjunct actually threads.

    **Two swaps off the strong twin, both already validated at the descend edge (R500).**
    * The enclosing facts come from `seqEnclosingFacts_of_windowed_safebodyunit` (THREE facts:
      `bodySucc` + the INTERIOR `feContentStart` + `noTrailingSep`) in place of
      `seqSeparatorFacts_of_windowed_safebodyunit` (TWO: `bodySucc` + `noTrailingSep`), because the
      weak guard's `≠ .key`-gated `feContentStart` cannot supply the interior locally.
    * The assembler is the UNIFIED `flowBodyContent_of_deepSeq` (R393) in place of the SPLIT
      `flowBodyContent_of_deep`: its single `h_feContent` over EVERY interior `k < hi` is served by the
      unit projection's facts — INTERIOR (`k+1 < hi`) by the helper's middle conjunct (which COERCES
      `SafeBodyUnit → SafeBody` internally, [[ref-coercion-dissolves-forced-projection]] R500), BOUNDARY
      (`k+1 = hi`) VACUOUSLY by `noTrailingSepFact`.  No second, fuller projection of the deliverable is
      forced; R499's `seqChild_safeBody_seq` stays off the critical path here too.

    **This is the producer's ROOT-LEAF: it SHEDS all the descend edge's recursion machinery**
    ([[ref-near-leaf-mirror-sheds-machinery]]).  No `h_ne` forwarding, no `flowBodyContentDeepSeq_descend`,
    no width IH, no interior floor — the child `SafeBodyUnit` is the FLAT `seqRoot_safeBodyUnit` (scanned
    straight off emission, no `RecSeqBody`), and the root guard is a hypothesis, not produced.

    **Milestone — the advance edge needs NO `_seq` twin.**  `flowBodyContent_advance` (NonemptyStructure)
    operates purely on the PROJECTION `FlowBodyContent`, re-basing the depth-`0` balance; it never READS
    the deep guard, so it is GUARD-NEUTRAL and reused VERBATIM across the strong and `_seq` threads.  Only
    the guard-READING moves (DESCEND, which produces the child off the guard; ROOT, which consumes the
    root-true guard) needed `_seq` twins; the projection-re-basing move did not
    ([[ref-guard-reading-edges-need-twins]]).  So root (here) + descend (R500) + advance (verbatim) thread
    `FlowBodyContent` as a carrier-free `G`-conjunct the co-construction consumes to produce per-window
    `RecSeqBody` — discharging `recIH`, breaking the carrier↔producer circularity.

    Verified-but-unconsumed until the carrier-free `windowWidth_strongRecOn` threads `FlowBodyContent` as a
    `G`-conjunct (R225): composes only landed lemmas, references no sorry site, frontier sorry count
    unchanged at 4; axiom-clean (identical footprint to its strong twin). -/
theorem seqRoot_flowBodyContent_seq
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v)
    (h_deep : FlowBodyContentDeepSeq tokens 2 (tokens.size - 2)) :
    FlowBodyContent tokens 2 (tokens.size - 2) := by
  -- The flat root `SafeBodyUnit` (off emission, NO `RecSeqBody`) yields the three enclosing facts.
  have h_safe : SafeBodyUnit ContentStartTok ((tokens.toList.take (tokens.size - 2)).drop 2) :=
    seqRoot_safeBodyUnit items tokens h_scan h_ne h_all
  obtain ⟨h_bs, h_fe_int, h_nts⟩ :=
    seqEnclosingFacts_of_windowed_safebodyunit tokens 2 (tokens.size - 2)
      (Nat.sub_le tokens.size 2) h_safe
  -- The UNIFIED assembler: the one `h_feContent` splits INTERIOR (helper's middle conjunct, coerced)
  -- ∪ BOUNDARY (`noTrailingSepFact`, vacuous) — the R500 dissolution, no fuller projection forced.
  refine flowBodyContent_of_deepSeq tokens 2 (tokens.size - 2) h_deep h_bs ?_
  intro k hk1 hk2 hfe hbal
  rcases Nat.lt_or_ge (k + 1) (tokens.size - 2) with h | h
  · exact h_fe_int k hk1 h hfe hbal
  · exact h_nts k hk1 (by omega) hfe hbal

/-- **`FlowBodyContent` is a PROJECTION of the window's OWN `RecSeqBody`** — `(i'-b-B2c-desc-fixpoint-proj)`,
    R502: the brick that UNIFIES the three carrier-free `FlowBodyContent` edges (root R501, descend R500,
    advance reused) into ONE `RecSeqBody`-keyed projection, and the consume-side dual the JOINT
    `windowWidth_strongRecOn` co-construction reads.

    **The find — every `_seq` edge factors through the SAME projection.**  Read the two guard-READING edges
    side by side ([[ref-guard-reading-edges-need-twins]]): `seqRoot_flowBodyContent_seq` (R501) sources its
    windowed `SafeBodyUnit ContentStartTok ((take (size-2)).drop 2)` from the FLAT `seqRoot_safeBodyUnit`
    (emission), then runs `seqEnclosingFacts_of_windowed_safebodyunit ▸ flowBodyContent_of_deepSeq`;
    `flowBodyContent_descend_seq` (R500) sources the SAME windowed `SafeBodyUnit ((take j).drop (p+1))` from
    the child oracle (`seqChild_safeBodyUnit_seq`, IH-fed), then runs the IDENTICAL
    `seqEnclosingFacts_of_windowed_safebodyunit ▸ flowBodyContent_of_deepSeq` tail.  The two edges differ
    ONLY in HOW the windowed `SafeBodyUnit` is obtained; the content-assembly tail is byte-identical.  And
    that `SafeBodyUnit` is, in both cases, a window's `RecSeqBody.toSafeBodyUnit` (the root's `RecSeqBody`
    off emission, the child's off the IH).  So both edges are the SAME function of the window's own
    `RecSeqBody` — exactly the [[ref-producer-dual-of-consumer-joint]] shape: the recursion PRODUCES
    `RecSeqBody`, and reading it back as `FlowBodyContent` is one projection, reversed.

    This lemma names that projection ONCE, keyed on the window's `RecSeqBody` directly (the same composition
    `seqSeparatorFacts_of_recseqbody` already does for the TWO-fact separator bundle, here lifted to the
    full content via the THREE-fact `seqEnclosingFacts_of_windowed_safebodyunit` + the UNIFIED
    `flowBodyContent_of_deepSeq`, [[ref-coercion-dissolves-forced-projection]] R500: the interior
    `feContentStart` is recovered from the unit projection by the internal `SafeBodyUnit → SafeBody`
    coercion, the boundary vacuously by `noTrailingSepFact`).  With it, `seqRoot_flowBodyContent_seq` IS
    this lemma fed `(seqRoot_recseqbody …)` and `flowBodyContent_descend_seq` IS this lemma fed the child
    oracle's `RecSeqBody` — the windowed `SafeBodyUnit` source is the only delta, and it is the
    deliverable's own projection in BOTH ([[ref-recursive-producer-mirrors-flat-over-shared-induction]]
    consume-side dual).

    **What it buys the JOINT consume step.**  The `windowWidth_strongRecOn` IH yields, for any sub-window,
    `RecSeqBody ((take hi').drop lo')`; this lemma turns that deliverable into the sub-window's
    `FlowBodyContent` with NO second IH call and NO oracle re-entry — content is FREE wherever the
    recursion has already produced the body.  (The residual it does NOT close is the SAME-window coupling
    the dispatch still needs: producing `RecSeqBody lo hi` consumes `h_content : FlowBodyContent lo hi` for
    the head dispatch, so the CURRENT window's content is the top-down `G`-seed (root R501 + descend/advance
    edges), while the CHILDREN's content is this free projection — the two are not the same window, so no
    cycle. This is what splits the co-construction into a top-down content thread and a bottom-up body
    deliverable.)

    Verified-but-unconsumed until the JOINT carrier-free recursion projects the IH's `RecSeqBody` through
    it (R225): composes only landed lemmas (`RecSeqBody.toSafeBodyUnit` +
    `seqEnclosingFacts_of_windowed_safebodyunit` + `flowBodyContent_of_deepSeq`), references no sorry site,
    frontier sorry count unchanged at 4; axiom-clean. -/
theorem flowBodyContent_of_recseqbody_seq
    (tokens : Array (Positioned YamlToken)) (a b : Nat) (h_b : b ≤ tokens.size)
    (h_deep : FlowBodyContentDeepSeq tokens a b)
    (h_rec : RecSeqBody ((tokens.toList.take b).drop a)) :
    FlowBodyContent tokens a b := by
  -- The window's own `RecSeqBody` projects to its windowed `SafeBodyUnit`; the three enclosing facts
  -- follow, and the UNIFIED `_seq` assembler merges interior (coerced) ∪ boundary (vacuous).
  obtain ⟨h_bs, h_fe_int, h_nts⟩ :=
    seqEnclosingFacts_of_windowed_safebodyunit tokens a b h_b h_rec.toSafeBodyUnit
  refine flowBodyContent_of_deepSeq tokens a b h_deep h_bs ?_
  intro k hk1 hk2 hfe hbal
  rcases Nat.lt_or_ge (k + 1) b with h | h
  · exact h_fe_int k hk1 h hfe hbal
  · exact h_nts k hk1 (by omega) hfe hbal

/-- **The CONTENT-EMITTING seq oracle** — `(i'-b-B2c-desc-fixpoint-oracle-content)`, R503: the consume-side
    of R502's free projection ([[ref-edges-unify-as-deliverable-projection]]) realized AT the seq oracle's
    own descend site.  Where `recseqentry_seqbracket_oracle_seq` (R415) returns only the child `RecSeqBody`
    `((take j).drop (lo+1))` and the trailing separator, this twin ALSO returns the descended child's
    `FlowBodyContent tokens (lo+1) j` — the third deliverable a content-threading dispatch needs for the
    descend child's `FlowBodyContent` `G`-conjunct.

    **The child content is FREE — it is a projection of the `RecSeqBody` the oracle ALREADY produced.**  The
    oracle draws the child `RecSeqBody` off the CONTENT-FREE width IH `h_ih` (via `seqChild_safeBodyUnit_seq`,
    R494) and internally builds the child deep guard `h_deep'` (`flowBodyContentDeepSeq_descend`).  R502's
    `flowBodyContent_of_recseqbody_seq` turns exactly those two — `RecSeqBody (lo+1) j` + the child's
    `FlowBodyContentDeepSeq` — into the child `FlowBodyContent` with NO second IH call and NO re-run of the
    R500 descend edge `flowBodyContent_descend_seq` (which would re-derive the child `SafeBodyUnit` from the
    content-free IH all over again).  So this twin reuses the oracle's `h_rec` for double duty: the
    `RecSeqEntry`-assembly deliverable AND the descend child's content `G`-conjunct.  This is the concrete
    instance of [[ref-producer-dual-of-consumer-joint]] — the recursion PRODUCES the body, and reading it
    back as content is one map, the deliverable's WRITE reversed to a READ — at the seq oracle's recursion
    site, not as a standalone lemma.

    **What it does NOT close (the same-window coupling, [[ref-edges-unify-as-deliverable-projection]]).**  The
    child content here is the CHILDREN's free projection; the CURRENT window's content (`h_content`) is still
    consumed by the oracle's own dispatch BEFORE the current body deliverable exists, so it remains the
    top-down `G`-seed (root R501 + descend/advance threaded through `G`).  And the oracle's IH stays
    CONTENT-FREE: producing child content here is downstream of `h_rec`, so it cannot be fed back as the
    content the IH would consume — the content-free width IH the descend edge needs is unchanged.  This brick
    moves the descend child's content from a SEPARATE R500 derivation onto the oracle's existing `h_rec`; the
    OUTER carrier-free bridge (sourcing that content-free width IH without the carrier) is the next brick.

    Verified-but-unconsumed until the content-threading dispatch reuses the emitted child content (R225):
    composes only landed lemmas (`recseqentry_seqbracket_oracle_seq` + `flowBodyContentDeepSeq_descend` +
    R502 `flowBodyContent_of_recseqbody_seq`), references no sorry site, frontier sorry count unchanged at 4;
    axiom-clean. -/
theorem recseqentry_seqbracket_oracle_seq_content (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_window : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeepSeq tokens lo hi)
    (h_content : FlowBodyContent tokens lo hi)
    (h_open : tokens[lo]!.val = .flowSequenceStart)
    (h_ne : tokens[lo + 1]!.val ≠ .flowSequenceEnd)
    (Q : Nat → Prop) (h_q_succ : Q (lo + 1))
    (h_ih : ∀ lo' hi', hi' - lo' < hi - lo → lo ≤ lo' → hi' ≤ hi →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeepSeq tokens lo' hi' → Q lo' →
        tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo')) :
    ∀ j, lo < j → j < hi → tokens[j]!.val = .flowSequenceEnd →
        flowBracketBalance tokens (lo + 1) j = 0 →
        (∀ i, lo < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) →
        RecSeqBody ((tokens.toList.take j).drop (lo + 1)) ∧
        FlowBodyContent tokens (lo + 1) j ∧
        (j + 1 = hi ∨ tokens[j + 1]!.val = .flowEntry) := by
  intro j h_lo_j h_j_hi h_close h_inner h_floor
  -- The existing seq oracle delivers the child `RecSeqBody` (off the CONTENT-FREE IH) + trailing separator.
  obtain ⟨h_rec, h_sep⟩ :=
    recseqentry_seqbracket_oracle_seq tokens lo hi h_window h_deep h_content h_open h_ne Q h_q_succ h_ih
      j h_lo_j h_j_hi h_close h_inner h_floor
  -- Interior non-emptiness `lo + 1 < j` from the supplied `h_ne` (refutes the empty close `j = lo + 1`).
  have h_lo1_j : lo + 1 < j := by
    rcases Nat.lt_or_ge (lo + 1) j with h | h
    · exact h
    · exfalso; have h_eq : j = lo + 1 := by omega
      rw [h_eq] at h_close; exact h_ne h_close
  -- The child deep guard `[lo+1, j)` (the parent's, restricted) — exactly the oracle's internal `h_deep'`.
  have h_deep' : FlowBodyContentDeepSeq tokens (lo + 1) j :=
    flowBodyContentDeepSeq_descend tokens lo lo j hi h_deep (Nat.le_refl lo) h_open h_ne h_lo1_j
      (Nat.le_of_lt h_j_hi)
  -- R502 free projection: the child content is a PROJECTION of the child `RecSeqBody` already in hand —
  -- no second IH call, no re-run of `seqChild_safeBodyUnit_seq` (R500's descend-edge machinery).
  have h_child_content : FlowBodyContent tokens (lo + 1) j :=
    flowBodyContent_of_recseqbody_seq tokens (lo + 1) j (by have := h_window.hi_lt; omega) h_deep' h_rec
  exact ⟨h_rec, h_child_content, h_sep⟩

/-- **The CONTENT-SURFACING located seq entry** — `(i'-b-B2c-desc-fixpoint-located-content)`, R504: the
    located-level companion of R503's content-emitting oracle (`recseqentry_seqbracket_oracle_seq_content`),
    lifting it through the close-locator `matchingClose_full_seq` so the descend close `j` — which
    `recseqentry_seqbracket_located` (R283) BURIES inside its `∃ m` (the entry END, not the descend
    close) — is EXPOSED alongside the descended child's free `FlowBodyContent tokens (lo+1) j`.

    Where `recseqentry_seqbracket_located` returns only `∃ m, … RecSeqEntry ((take m).drop lo)` (the first
    located entry, `m` its trailing boundary), this twin returns that SAME entry AND a second existential
    `∃ j, lo+1 < j ∧ j < hi ∧ tokens[j]! = .flowSequenceEnd ∧ balance (lo+1) j = 0 ∧
    FlowBodyContent tokens (lo+1) j` — the located bracket close `j` with the child window's content.  The
    child content is FREE (R503 reads it off the oracle's already-produced child `RecSeqBody` via R502); this
    brick merely propagates it past the close-locator, surfacing the `j` the entry-shaped output hides.  The
    interior non-emptiness `lo+1 < j` is recovered from the forwarded `h_ne` (the empty close `j = lo+1`
    would make `tokens[j]! = .flowSequenceEnd` contradict `h_ne`).

    **Honest scope — this does NOT advance the carrier-free recursion's descend.**  Reading the carrier-based
    `_seq` recursion (`seqWindowRecSeqBody_seq_general`) against `seqChild_safeBodyUnit_seq` settles the
    architecture precisely: that recursion's guard `G` is ALREADY content-free
    (`FlowBodyWindow ∧ FlowBodyContentDeepSeq ∧ SeqEnclosed ∧ close ∧ bounds`), and the carrier
    `SeqInteriorSeparators` is consumed in EXACTLY ONE place — sourcing the CURRENT window's
    `FlowBodyContent` (`seqWindow_flowBodyContent_seq_general`).  The descend itself is content-FREE: the seq
    oracle draws the child `RecSeqBody` from the content-free width IH (`seqChild_safeBodyUnit_seq` calls the
    oracle ONCE on `(lo+1, j)`), so the descended child needs NO content.  Hence R503's — and this brick's —
    surfaced child content is genuinely free but is NOT consumed by the descend recursive call.

    The ONE real obstacle is therefore isolated: the CURRENT window's content, the carrier's sole job.  It is
    intrinsically TOP-DOWN / path-dependent — R500 `flowBodyContent_descend_seq` produces a child's content
    from the PARENT's content (`h_content : FlowBodyContent tokens p hi`) plus a content-free body IH — so a
    pure `windowWidth_strongRecOn` (bottom-up by WIDTH, no parent in scope) cannot thread it.  Closing it
    carrier-free needs either `P := FlowBodyContent → RecSeqBody` (content as ANTECEDENT) with a nested
    content-free body IH that itself carries parent content down the descent, or a custom recursor on the
    descent that carries parent content — a JOINT/mutual construction (content top-down, body bottom-up), not
    single-theorem wiring.  This brick is the seq-branch unit a content-threading dispatch twin will consume
    to surface the child content; it is NOT itself the bridge.

    Verified-but-unconsumed until that content-threading dispatch consumes the surfaced child content (R225):
    composes only landed lemmas (`matchingClose_full_seq` + R503's content-emitting oracle +
    `recseqentry_classify`), references no sorry site, frontier sorry count unchanged at 4; axiom-clean. -/
theorem recseqentry_seqbracket_located_content (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo_hi : lo < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_open : tokens[lo]!.val = .flowSequenceStart)
    (h_ne : tokens[lo + 1]!.val ≠ .flowSequenceEnd)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo))
    (h_oracle : ∀ j, lo < j → j < hi → tokens[j]!.val = .flowSequenceEnd →
        flowBracketBalance tokens (lo + 1) j = 0 →
        (∀ i, lo < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) →
        RecSeqBody ((tokens.toList.take j).drop (lo + 1)) ∧
        FlowBodyContent tokens (lo + 1) j ∧
        (j + 1 = hi ∨ tokens[j + 1]!.val = .flowEntry)) :
    (∃ m, lo < m ∧ m ≤ hi ∧
      flowBracketBalance tokens lo m = 0 ∧
      (m = hi ∨ tokens[m]!.val = .flowEntry) ∧
      (∀ k, lo < k → k < m →
        ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry))) ∧
      RecSeqEntry ((tokens.toList.take m).drop lo)) ∧
    (∃ j, lo + 1 < j ∧ j < hi ∧ tokens[j]!.val = .flowSequenceEnd ∧
      flowBracketBalance tokens (lo + 1) j = 0 ∧
      FlowBodyContent tokens (lo + 1) j) := by
  obtain ⟨j, h_lo_j, h_j_hi, h_close, h_inner, h_pos⟩ :=
    matchingClose_full_seq tokens lo hi h_lo_hi h_hi_sz h_open h_total h_dyck h_wt
  obtain ⟨h_rec, h_child_content, h_succ⟩ := h_oracle j h_lo_j h_j_hi h_close h_inner h_pos
  -- Interior non-emptiness `lo + 1 < j` from the forwarded `h_ne` (refutes the empty close `j = lo + 1`).
  have h_lo1_j : lo + 1 < j := by
    rcases Nat.lt_or_ge (lo + 1) j with h | h
    · exact h
    · exfalso; have h_eq : j = lo + 1 := by omega
      rw [h_eq] at h_close; exact h_ne h_close
  refine ⟨?_, ⟨j, h_lo1_j, h_j_hi, h_close, h_inner, h_child_content⟩⟩
  exact recseqentry_classify tokens lo hi h_lo_hi h_hi_sz h_total
    (Or.inr (Or.inr (Or.inr ⟨j, h_open, h_lo_j, h_j_hi, h_close, h_inner, h_pos, h_rec, h_succ⟩)))

/-- **The combined `windowWidth_strongRecOn` `RecSeqBody` producer** — `(i'-b-B3-fixpoint)`, the LAST
    seq brick and the convergence point of all the landed descent/edge bricks.  At every body window
    `[lo, hi)` that is a `FlowBodyWindow ∧ FlowBodyContentDeep ∧ SeqEnclosed lo` whose `hi` is the
    enclosing sequence's matching close, it produces the recursive interior `RecSeqBody`.

    Drives `windowWidth_strongRecOn` with the four-conjunct guard `G`.  Each per-window `step`:
    `seqWindow_flowBodyContent` (R320) projects the threaded carrier to the dispatch's
    `FlowBodyContent`; `recseqentry_window_dispatch` (R322, `Q`-parametric) classifies the first entry,
    `Q := SeqEnclosed tokens` bound here with the descend edge `seqEnclosed_descend`; the IH adapter
    re-packages the four `G` conjuncts as the dispatch's separate-arrow IH; and
    `recseqbody_window_assemble` folds the first entry with the advance tail (the IH at `[m+1, hi)`),
    its three guard fields re-established by `flowBodyWindow_advance` / `flowBodyContentDeep_advance` /
    `seqEnclosed_advance` (the last over the `WellTyped` segment `[lo, m+1)`, projected by
    `WellTyped_subrange`).

    **The `tokens[hi]! = .flowSequenceEnd` fourth conjunct is load-bearing (R323).**  The advance branch
    must exclude a *trailing separator* (`m + 1 = hi`): the assembler's tail oracle would then demand
    `RecSeqBody []`, which is uninhabited.  The carrier's `noTrailingSepFact` does NOT close this — it
    only yields `isFlowContentStart tokens[hi]`, which is *consistent* when `tokens[hi]` is content, and
    the three-conjunct `G` genuinely admits a trailing-comma window (balanced + Dyck + seq-enclosed with
    `tokens[hi]` a scalar).  The recursion in fact maintains "`hi` is the enclosing close" as an
    invariant `G` did not carry; threading `tokens[hi]! = .flowSequenceEnd` through the descent chain's
    IH (the R322 plumbing extended one conjunct, the oracle supplying it from its located `h_close`)
    makes the boundary `isFlowContentStart tokens[hi]` contradictory, closing `m + 1 < hi`.

    Verified-but-unconsumed until `seqRoot_seqInteriorSeparators`'s `desc` lands and
    `flowSubrangesOk_of_window_producers` is wired (R225): references no sorry site, frontier sorry
    count unchanged at 4; axiom-clean. -/
theorem seqWindowRecSeqBody_general (tokens : Array (Positioned YamlToken))
    (lo0 hi0 : Nat)
    (h_carrier : SeqInteriorSeparators tokens lo0 hi0)
    (lo hi : Nat)
    (h_win0 : FlowBodyWindow tokens lo hi) (h_deep0 : FlowBodyContentDeep tokens lo hi)
    (h_enc0 : SeqEnclosed tokens lo) (h_close0 : tokens[hi]!.val = .flowSequenceEnd)
    (h_lo0 : lo0 ≤ lo) (h_hi0 : hi ≤ hi0) :
    RecSeqBody ((tokens.toList.take hi).drop lo) := by
  have key := windowWidth_strongRecOn
    (P := fun lo hi => RecSeqBody ((tokens.toList.take hi).drop lo))
    (G := fun lo hi => FlowBodyWindow tokens lo hi ∧ FlowBodyContentDeep tokens lo hi
      ∧ SeqEnclosed tokens lo ∧ tokens[hi]!.val = .flowSequenceEnd ∧ lo0 ≤ lo ∧ hi ≤ hi0)
    (step := ?step)
  case step =>
    intro lo hi h_g ih
    obtain ⟨h_win, h_deep, h_enc, h_close_hi, h_lo0_lo, h_hi_hi0⟩ := h_g
    have h_hi_sz : hi < tokens.size := h_win.hi_lt
    have h_lo_sz : lo < tokens.size := by
      have := h_win.lo_lt_hi; omega
    have h_content : FlowBodyContent tokens lo hi :=
      seqWindow_flowBodyContent_general tokens lo0 hi0 lo hi h_win h_deep h_enc h_carrier h_lo0_lo h_hi_hi0
    obtain ⟨m, h_lo_m, h_m_hi, h_bal_m, h_marker, h_min, h_entry⟩ :=
      recseqentry_window_dispatch tokens lo hi h_win h_deep h_content
        (SeqEnclosed tokens)
        (fun h_open => seqEnclosed_descend tokens lo h_enc h_lo_sz h_open)
        (fun lo' hi' h_lt h_cont_lo h_cont_hi h_w h_d h_q h_c =>
          ih lo' hi' h_lt ⟨h_w, h_d, h_q, h_c,
            Nat.le_trans h_lo0_lo h_cont_lo, Nat.le_trans h_cont_hi h_hi_hi0⟩)
    refine recseqbody_window_assemble tokens lo m hi h_lo_m h_m_hi h_win.hi_lt h_marker h_entry ?_
    intro h_m_lt_hi
    have h_sep : tokens[m]!.val = .flowEntry := h_marker.resolve_left (by omega)
    -- balance lo (m+1) = 0 (the comma has delta 0)
    have h_m_len : m < tokens.toList.length := by rw [Array.length_toList]; omega
    have h_m_val : tokens[m]! = tokens.toList[m]'h_m_len := by
      rw [getElem!_pos tokens m (by omega), Array.getElem_toList]
    have h_delta_m : flowBracketDelta tokens[m]!.val = 0 := by
      rw [h_sep]; exact flowBracketDelta_flowEntry
    have h_single_m : flowBracketBalance tokens m (m + 1) = flowBracketDelta tokens[m]!.val := by
      rw [flowBracketBalance_single tokens m h_m_len, ← h_m_val]
    have h_bal_m1 : flowBracketBalance tokens lo (m + 1) = 0 := by
      have hc := flowBracketBalance_compose tokens lo m (m + 1) (by omega) (Nat.le_succ m)
      rw [h_bal_m, h_single_m, h_delta_m] at hc; omega
    -- O1: no trailing separator — `m + 1 = hi` would force `isFlowContentStart tokens[hi]`, but
    -- `tokens[hi]! = .flowSequenceEnd` (the enclosing close) is not a content start.
    have h_m1_hi : m + 1 < hi := by
      rcases Nat.lt_or_ge (m + 1) hi with h | h
      · exact h
      · exfalso
        have h_eq : m + 1 = hi := by omega
        obtain ⟨_, h_cs⟩ :=
          h_content.feContentStart m (Nat.le_of_lt h_lo_m) h_m_lt_hi h_sep h_bal_m
        rw [h_eq, h_close_hi] at h_cs
        simp [isFlowContentStart] at h_cs
    -- O2: WellTyped segment [lo, m+1)
    have h_wt_seg : WellTyped ((tokens.toList.take (m + 1)).drop lo) :=
      WellTyped_subrange tokens lo lo (m + 1) hi (Nat.le_refl lo) (by omega) (by omega)
        (Nat.le_of_lt h_win.hi_lt) h_win.wellTyped h_bal_m1
        (fun p hp1 hp2 => h_win.dyck p hp1 (by omega))
    have h_win' : FlowBodyWindow tokens (m + 1) hi :=
      flowBodyWindow_advance tokens lo m hi h_win (Nat.le_of_lt h_lo_m) h_m1_hi h_bal_m h_sep
    have h_deep' : FlowBodyContentDeep tokens (m + 1) hi :=
      flowBodyContentDeep_advance tokens lo m hi h_deep (Nat.le_of_lt h_lo_m) h_sep h_m1_hi
    have h_enc' : SeqEnclosed tokens (m + 1) :=
      seqEnclosed_advance tokens lo (m + 1) h_enc (by omega) h_wt_seg
    exact ih (m + 1) hi (by omega) ⟨h_win', h_deep', h_enc', h_close_hi, by omega, h_hi_hi0⟩
  exact key lo hi ⟨h_win0, h_deep0, h_enc0, h_close0, h_lo0, h_hi0⟩

/-- **The root-span instance of `seqWindowRecSeqBody_general`** — `lo0 := 2`, `hi0 := size-2`, bounds
    read off `FlowBodyWindow.lo_ge`/`hi_le`.  Signature-preserving so the existing `seqWindowRecSeqBody`
    consumers (which thread the root carrier `SeqInteriorSeparators tokens 2 (size-2)`) are untouched.
    ROUTE A (R445): the carrier-span generalization now rides the recursion — its descend edge narrows
    the parametric carrier `[lo0, hi0]` using the containment `lo ≤ lo' ∧ hi' ≤ hi` exposed through the
    dispatch's `h_ih`. -/
theorem seqWindowRecSeqBody (tokens : Array (Positioned YamlToken))
    (h_root_carrier : SeqInteriorSeparators tokens 2 (tokens.size - 2))
    (lo hi : Nat)
    (h_win0 : FlowBodyWindow tokens lo hi) (h_deep0 : FlowBodyContentDeep tokens lo hi)
    (h_enc0 : SeqEnclosed tokens lo) (h_close0 : tokens[hi]!.val = .flowSequenceEnd) :
    RecSeqBody ((tokens.toList.take hi).drop lo) :=
  seqWindowRecSeqBody_general tokens 2 (tokens.size - 2) h_root_carrier lo hi
    h_win0 h_deep0 h_enc0 h_close0 h_win0.lo_ge h_win0.hi_le

/-- **Carrier-PARAMETRIC `_seq` recursion** — `(i'-b-B2c-desc-fixpoint-provider)`, R505: the
    `seqWindowRecSeqBody_seq_general` recursion (below) with its SOLE carrier use lifted into an abstract
    per-window content PROVIDER hypothesis `h_provider`.  [[ref-parametric-assembler-extraction]] at the
    recursion level.

    Reading `seqWindowRecSeqBody_seq_general` against `seqChild_safeBodyUnit_seq`, the carrier
    `SeqInteriorSeparators` is consumed in EXACTLY ONE place — sourcing the CURRENT window's
    `FlowBodyContent` (`seqWindow_flowBodyContent_seq_general … h_carrier`).  Everything else is already
    carrier-free: the DESCEND draws the child `RecSeqBody` off the content-free width IH (the seq oracle,
    `seqChild_safeBodyUnit_seq`), and the ADVANCE edge `flowBodyContentDeepSeq_advance`'s `≠ .key` premise
    is paid in-place from the content guard's own `feContentStart` separator fact.  So the recursion is
    carrier-free MODULO a per-window content provider, and this lemma states exactly that: ANY `h_provider`
    that supplies each window's `FlowBodyContent` from its guard (`FlowBodyWindow` + `FlowBodyContentDeepSeq`
    + `SeqEnclosed` + the `[lo0, hi0]` containment bounds) drives the recursion.  The carrier is one such
    provider: `seqWindowRecSeqBody_seq_general` below is the carrier INSTANCE of this lemma, fed
    `h_provider := fun lo hi … => seqWindow_flowBodyContent_seq_general … h_carrier` (kept as the standalone
    carrier recursion so its existing consumers are untouched — [[ref-additive-parallel-type-over-shared-edit]]).

    **What it isolates** (the single remaining carrier-free obligation).  Producing `h_provider` without the
    carrier IS the fixpoint ([[ref-width-recursion-cannot-thread-topdown-fact]]).  Per R502
    ([[ref-edges-unify-as-deliverable-projection]], `flowBodyContent_of_recseqbody_seq`) the provider for
    the CHILDREN is free off the body the IH already produced; only the CURRENT window's content is the
    genuine TOP-DOWN seed — its `bodySucc` (the depth-`0` separator-successor fact) has NO descend-stable,
    balance-free form (unlike `FlowBodyContentDeepSeq`'s opener/separator fields), so it cannot be sourced
    bottom-up from the window's own guard and must be threaded from the parent (root R501 +
    descend/advance) or read off a navigated body.  This brick does NOT close that — it NAMES it as the one
    hypothesis a carrier-free driver must still discharge, and proves the rest of the recursion needs
    nothing else.  Verified: the recursion body is the landed
    `seqWindowRecSeqBody_seq_general`'s verbatim, references no sorry site, frontier sorry count unchanged
    at 4; axiom-clean. -/
theorem seqWindowRecSeqBody_seq_of_provider (tokens : Array (Positioned YamlToken))
    (lo0 hi0 : Nat)
    (h_provider : ∀ lo hi, FlowBodyWindow tokens lo hi → FlowBodyContentDeepSeq tokens lo hi →
        SeqEnclosed tokens lo → lo0 ≤ lo → hi ≤ hi0 → FlowBodyContent tokens lo hi)
    (lo hi : Nat)
    (h_win0 : FlowBodyWindow tokens lo hi) (h_deep0 : FlowBodyContentDeepSeq tokens lo hi)
    (h_enc0 : SeqEnclosed tokens lo) (h_close0 : tokens[hi]!.val = .flowSequenceEnd)
    (h_lo0 : lo0 ≤ lo) (h_hi0 : hi ≤ hi0) :
    RecSeqBody ((tokens.toList.take hi).drop lo) := by
  have key := windowWidth_strongRecOn
    (P := fun lo hi => RecSeqBody ((tokens.toList.take hi).drop lo))
    (G := fun lo hi => FlowBodyWindow tokens lo hi ∧ FlowBodyContentDeepSeq tokens lo hi
      ∧ SeqEnclosed tokens lo ∧ tokens[hi]!.val = .flowSequenceEnd ∧ lo0 ≤ lo ∧ hi ≤ hi0)
    (step := ?step)
  case step =>
    intro lo hi h_g ih
    obtain ⟨h_win, h_deep, h_enc, h_close_hi, h_lo0_lo, h_hi_hi0⟩ := h_g
    have h_hi_sz : hi < tokens.size := h_win.hi_lt
    have h_lo_sz : lo < tokens.size := by
      have := h_win.lo_lt_hi; omega
    have h_content : FlowBodyContent tokens lo hi :=
      h_provider lo hi h_win h_deep h_enc h_lo0_lo h_hi_hi0
    obtain ⟨m, h_lo_m, h_m_hi, h_bal_m, h_marker, h_min, h_entry⟩ :=
      recseqentry_window_dispatch_seq tokens lo hi h_win h_deep h_content
        (SeqEnclosed tokens)
        (fun h_open => seqEnclosed_descend tokens lo h_enc h_lo_sz h_open)
        (fun lo' hi' h_lt h_cont_lo h_cont_hi h_w h_d h_q h_c =>
          ih lo' hi' h_lt ⟨h_w, h_d, h_q, h_c,
            Nat.le_trans h_lo0_lo h_cont_lo, Nat.le_trans h_cont_hi h_hi_hi0⟩)
    refine recseqbody_window_assemble tokens lo m hi h_lo_m h_m_hi h_win.hi_lt h_marker h_entry ?_
    intro h_m_lt_hi
    have h_sep : tokens[m]!.val = .flowEntry := h_marker.resolve_left (by omega)
    have h_m_len : m < tokens.toList.length := by rw [Array.length_toList]; omega
    have h_m_val : tokens[m]! = tokens.toList[m]'h_m_len := by
      rw [getElem!_pos tokens m (by omega), Array.getElem_toList]
    have h_delta_m : flowBracketDelta tokens[m]!.val = 0 := by
      rw [h_sep]; exact flowBracketDelta_flowEntry
    have h_single_m : flowBracketBalance tokens m (m + 1) = flowBracketDelta tokens[m]!.val := by
      rw [flowBracketBalance_single tokens m h_m_len, ← h_m_val]
    have h_bal_m1 : flowBracketBalance tokens lo (m + 1) = 0 := by
      have hc := flowBracketBalance_compose tokens lo m (m + 1) (by omega) (Nat.le_succ m)
      rw [h_bal_m, h_single_m, h_delta_m] at hc; omega
    have h_m1_hi : m + 1 < hi := by
      rcases Nat.lt_or_ge (m + 1) hi with h | h
      · exact h
      · exfalso
        have h_eq : m + 1 = hi := by omega
        obtain ⟨_, h_cs⟩ :=
          h_content.feContentStart m (Nat.le_of_lt h_lo_m) h_m_lt_hi h_sep h_bal_m
        rw [h_eq, h_close_hi] at h_cs
        simp [isFlowContentStart] at h_cs
    have h_wt_seg : WellTyped ((tokens.toList.take (m + 1)).drop lo) :=
      WellTyped_subrange tokens lo lo (m + 1) hi (Nat.le_refl lo) (by omega) (by omega)
        (Nat.le_of_lt h_win.hi_lt) h_win.wellTyped h_bal_m1
        (fun p hp1 hp2 => h_win.dyck p hp1 (by omega))
    have h_win' : FlowBodyWindow tokens (m + 1) hi :=
      flowBodyWindow_advance tokens lo m hi h_win (Nat.le_of_lt h_lo_m) h_m1_hi h_bal_m h_sep
    have h_m1_content : isFlowContentStart tokens[m + 1]!.val :=
      (h_content.feContentStart m (Nat.le_of_lt h_lo_m) h_m_lt_hi h_sep h_bal_m).2
    have h_m1_ne_key : tokens[m + 1]!.val ≠ .key := by
      unfold isFlowContentStart at h_m1_content
      rcases h_m1_content with ⟨c, s, h⟩ | h | h <;> simp [h]
    have h_deep' : FlowBodyContentDeepSeq tokens (m + 1) hi :=
      flowBodyContentDeepSeq_advance tokens lo m hi h_deep (Nat.le_of_lt h_lo_m) h_sep h_m1_ne_key h_m1_hi
    have h_enc' : SeqEnclosed tokens (m + 1) :=
      seqEnclosed_advance tokens lo (m + 1) h_enc (by omega) h_wt_seg
    exact ih (m + 1) hi (by omega) ⟨h_win', h_deep', h_enc', h_close_hi, by omega, h_hi_hi0⟩
  exact key lo hi ⟨h_win0, h_deep0, h_enc0, h_close0, h_lo0, h_hi0⟩

/-- **Located-entry → content bridge** — `(i'-b-B2c-desc-fixpoint-navigator-read)`, R506: the consume
    side of the carrier-free PROVIDER route ([[ref-width-recursion-cannot-thread-topdown-fact]] /
    [[ref-edges-unify-as-deliverable-projection]]).  R505 (`seqWindowRecSeqBody_seq_of_provider`)
    reduced the carrier-free `RecSeqBody` recursion to one obligation: a per-window content provider
    `∀ lo hi, <guards> → FlowBodyContent tokens lo hi`.  The fixpoint-free way to discharge it is the
    NAVIGATOR — navigate the root `RecSeqBody` (known off emission, `seqRoot_recseqbody`) down to each
    window and READ its content off the body it already holds, never PRODUCING the body from content
    (which needs content for its own dispatch — the same-window self-cycle).

    This brick is the navigator's terminal READ, and it pins the navigator's deliverable precisely:
    the emission-spine-walk navigator (R350–R359, the slice-keyed LEAF/DESCEND/ADVANCE arms, awaiting
    only the `Nat.strongRecOn` wrapper) LOCATES the enclosing seq ENTRY at the target window — output
    `RecSeqEntry (op :: (interior ++ [cl]))` + opener + nonempty interior + the window-identity slice
    `(take (hi+1)).drop lo_e = op :: (interior ++ [cl])` with `lo_e + 1 = lo`.  THIS lemma turns that
    located entry into `FlowBodyContent tokens lo hi` with NO carrier, composing three landed lemmas:
    `recseqentry_seq_extract` (the seq-opener entry stores `RecSeqBody interior`),
    `nestedSeq_recseqentry_locate_descend` (R353, the interior re-slices to `(take hi).drop lo` — the
    pure drop-algebra, here run with `rest = []` so the entry IS the whole window), and R502
    `flowBodyContent_of_recseqbody_seq` (the interior body projects to content).

    **The architectural payoff** (sharpens [[ref-edges-unify-as-deliverable-projection]]).  The
    carrier-free provider does NOT need to PRODUCE a sub-`RecSeqBody` at every window (that would re-pose
    R505's own recursion).  It needs only to LOCATE the enclosing seq entry — which the spine-walk
    navigator's three arms already step — because the entry's stored interior `RecSeqBody` IS the window
    body, and R502 reads its content.  So the navigator's deliverable is the located ENTRY (the
    `RecSeqEntry`), not the body; content is a free projection off it.  This collapses "navigator
    produces window bodies" to "navigator locates window entries + this 3-lemma read."

    Verified-but-unconsumed until the spine-walk `Nat.strongRecOn` wrapper produces the located entry and
    feeds it here, yielding `h_provider` for R505 (R225): composes only landed lemmas, references no sorry
    site, frontier sorry count unchanged at 4; axiom-clean. -/
theorem flowBodyContent_of_located_seq_entry (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_hi_sz : hi < tokens.size)
    (h_deep : FlowBodyContentDeepSeq tokens lo hi)
    (lo_e : Nat) (op cl : Positioned YamlToken) (interior : List (Positioned YamlToken))
    (h_a : lo_e + 1 = lo)
    (h_entry : RecSeqEntry (op :: (interior ++ [cl])))
    (h_open : op.val = .flowSequenceStart) (h_int_ne : interior ≠ [])
    (h_window_id : (tokens.toList.take (hi + 1)).drop lo_e = op :: (interior ++ [cl])) :
    FlowBodyContent tokens lo hi := by
  -- 1. The seq-opener entry stores its interior `RecSeqBody` (the three non-`seq` shapes are excluded).
  have h_rec : RecSeqBody interior :=
    recseqentry_seq_extract h_entry op cl interior rfl h_open h_int_ne
  -- 2. The interior re-slices to the window `[lo, hi)` — pure drop-algebra, run with `rest = []`.
  have h_elen : (op :: (interior ++ [cl])).length = interior.length + 2 := by
    simp [List.length_append]
  have h_len : lo_e + (op :: (interior ++ [cl])).length = hi + 1 := by
    have hc := congrArg List.length h_window_id
    rw [List.length_drop, List.length_take, Array.length_toList,
        Nat.min_eq_left (by omega : hi + 1 ≤ tokens.size)] at hc
    omega
  have h_slice : interior = (tokens.toList.take (lo_e + 1 + interior.length)).drop (lo_e + 1) :=
    nestedSeq_recseqentry_locate_descend tokens (op :: (interior ++ [cl])) [] interior op cl lo_e (hi + 1)
      h_window_id.symm (Nat.le_of_eq h_len) (List.append_nil _).symm
  have h_bplus : lo_e + 1 + interior.length = hi := by omega
  rw [h_bplus, h_a] at h_slice
  -- 3. The window body projects to content (R502) — no carrier.
  exact flowBodyContent_of_recseqbody_seq tokens lo hi (Nat.le_of_lt h_hi_sz) h_deep (h_slice ▸ h_rec)

/-- **The RE-SCOPED combined `RecSeqBody` producer** — `(i'-b-B2c-(d)-seq-rec)`, the `_seq` twin of
    `seqWindowRecSeqBody` (R323) threading R393's root-TRUE `FlowBodyContentDeepSeq` in place of the
    false-rooted `FlowBodyContentDeep`.  The CONSUMER half of the (R2) re-thread (its dispatch CORE landed
    R415 as `recseqentry_window_dispatch_seq` + `recseqentry_seqbracket_oracle_seq`); this completes the
    chain so the recursion no longer touches the false guard, leaving only (R3) the per-window field
    producers and (R1) the root carrier before `flowSubrangesOk_of_window_producers` can wire.

    The clone is R415's "one clone-per-consumer-with-one-line" with two delta points beyond the literal
    guard swap, both forced by the re-scope ([[ref-additive-parallel-type-over-shared-edit]] — the old
    theorem and its `FlowBodyContentDeep` guard stay untouched):

    * the per-window `FlowBodyContent` comes from `seqWindow_flowBodyContent_seq` (not `_…`), which
      re-sources the interior separator-content from the carrier rather than the now-gated guard field; and
    * the ADVANCE edge `flowBodyContentDeepSeq_advance` carries a NEW premise `tokens[m+1] ≠ .key` (the
      re-scope's `feContentStart` gate), which is FREE at the advance site — the content guard's
      `feContentStart` at the separator `m` already gives `isFlowContentStart tokens[m+1]`, and a
      content-start head is never a `.key` ([[ref-guarded-universal-fold-relocates-guard]]: the guard's new
      premise is the consumer's debt, paid here from a fact the step already holds).

    Everything else — the `windowWidth_strongRecOn` plumbing, the four-conjunct `G` (with
    `FlowBodyContentDeepSeq` swapped in), the `recseqbody_window_assemble` fold, the no-trailing-separator
    `m + 1 < hi` argument off `tokens[hi]! = .flowSequenceEnd`, the `flowBodyWindow_advance` /
    `seqEnclosed_advance` edges — is verbatim.

    Verified-but-unconsumed until `seqRoot_seqInteriorSeparators`'s `desc` lands and
    `flowSubrangesOk_of_window_producers` is wired (R225): references no sorry site, frontier sorry count
    unchanged at 4; axiom-clean. -/
theorem seqWindowRecSeqBody_seq_general (tokens : Array (Positioned YamlToken))
    (lo0 hi0 : Nat)
    (h_carrier : SeqInteriorSeparators tokens lo0 hi0)
    (lo hi : Nat)
    (h_win0 : FlowBodyWindow tokens lo hi) (h_deep0 : FlowBodyContentDeepSeq tokens lo hi)
    (h_enc0 : SeqEnclosed tokens lo) (h_close0 : tokens[hi]!.val = .flowSequenceEnd)
    (h_lo0 : lo0 ≤ lo) (h_hi0 : hi ≤ hi0) :
    RecSeqBody ((tokens.toList.take hi).drop lo) := by
  have key := windowWidth_strongRecOn
    (P := fun lo hi => RecSeqBody ((tokens.toList.take hi).drop lo))
    (G := fun lo hi => FlowBodyWindow tokens lo hi ∧ FlowBodyContentDeepSeq tokens lo hi
      ∧ SeqEnclosed tokens lo ∧ tokens[hi]!.val = .flowSequenceEnd ∧ lo0 ≤ lo ∧ hi ≤ hi0)
    (step := ?step)
  case step =>
    intro lo hi h_g ih
    obtain ⟨h_win, h_deep, h_enc, h_close_hi, h_lo0_lo, h_hi_hi0⟩ := h_g
    have h_hi_sz : hi < tokens.size := h_win.hi_lt
    have h_lo_sz : lo < tokens.size := by
      have := h_win.lo_lt_hi; omega
    have h_content : FlowBodyContent tokens lo hi :=
      seqWindow_flowBodyContent_seq_general tokens lo0 hi0 lo hi h_win h_deep h_enc h_carrier h_lo0_lo h_hi_hi0
    obtain ⟨m, h_lo_m, h_m_hi, h_bal_m, h_marker, h_min, h_entry⟩ :=
      recseqentry_window_dispatch_seq tokens lo hi h_win h_deep h_content
        (SeqEnclosed tokens)
        (fun h_open => seqEnclosed_descend tokens lo h_enc h_lo_sz h_open)
        (fun lo' hi' h_lt h_cont_lo h_cont_hi h_w h_d h_q h_c =>
          ih lo' hi' h_lt ⟨h_w, h_d, h_q, h_c,
            Nat.le_trans h_lo0_lo h_cont_lo, Nat.le_trans h_cont_hi h_hi_hi0⟩)
    refine recseqbody_window_assemble tokens lo m hi h_lo_m h_m_hi h_win.hi_lt h_marker h_entry ?_
    intro h_m_lt_hi
    have h_sep : tokens[m]!.val = .flowEntry := h_marker.resolve_left (by omega)
    -- balance lo (m+1) = 0 (the comma has delta 0)
    have h_m_len : m < tokens.toList.length := by rw [Array.length_toList]; omega
    have h_m_val : tokens[m]! = tokens.toList[m]'h_m_len := by
      rw [getElem!_pos tokens m (by omega), Array.getElem_toList]
    have h_delta_m : flowBracketDelta tokens[m]!.val = 0 := by
      rw [h_sep]; exact flowBracketDelta_flowEntry
    have h_single_m : flowBracketBalance tokens m (m + 1) = flowBracketDelta tokens[m]!.val := by
      rw [flowBracketBalance_single tokens m h_m_len, ← h_m_val]
    have h_bal_m1 : flowBracketBalance tokens lo (m + 1) = 0 := by
      have hc := flowBracketBalance_compose tokens lo m (m + 1) (by omega) (Nat.le_succ m)
      rw [h_bal_m, h_single_m, h_delta_m] at hc; omega
    -- O1: no trailing separator — `m + 1 = hi` would force `isFlowContentStart tokens[hi]`, but
    -- `tokens[hi]! = .flowSequenceEnd` (the enclosing close) is not a content start.
    have h_m1_hi : m + 1 < hi := by
      rcases Nat.lt_or_ge (m + 1) hi with h | h
      · exact h
      · exfalso
        have h_eq : m + 1 = hi := by omega
        obtain ⟨_, h_cs⟩ :=
          h_content.feContentStart m (Nat.le_of_lt h_lo_m) h_m_lt_hi h_sep h_bal_m
        rw [h_eq, h_close_hi] at h_cs
        simp [isFlowContentStart] at h_cs
    -- O2: WellTyped segment [lo, m+1)
    have h_wt_seg : WellTyped ((tokens.toList.take (m + 1)).drop lo) :=
      WellTyped_subrange tokens lo lo (m + 1) hi (Nat.le_refl lo) (by omega) (by omega)
        (Nat.le_of_lt h_win.hi_lt) h_win.wellTyped h_bal_m1
        (fun p hp1 hp2 => h_win.dyck p hp1 (by omega))
    have h_win' : FlowBodyWindow tokens (m + 1) hi :=
      flowBodyWindow_advance tokens lo m hi h_win (Nat.le_of_lt h_lo_m) h_m1_hi h_bal_m h_sep
    -- the re-scoped ADVANCE edge needs `tokens[m+1] ≠ .key`, FREE from the content guard's separator fact.
    have h_m1_content : isFlowContentStart tokens[m + 1]!.val :=
      (h_content.feContentStart m (Nat.le_of_lt h_lo_m) h_m_lt_hi h_sep h_bal_m).2
    have h_m1_ne_key : tokens[m + 1]!.val ≠ .key := by
      unfold isFlowContentStart at h_m1_content
      rcases h_m1_content with ⟨c, s, h⟩ | h | h <;> simp [h]
    have h_deep' : FlowBodyContentDeepSeq tokens (m + 1) hi :=
      flowBodyContentDeepSeq_advance tokens lo m hi h_deep (Nat.le_of_lt h_lo_m) h_sep h_m1_ne_key h_m1_hi
    have h_enc' : SeqEnclosed tokens (m + 1) :=
      seqEnclosed_advance tokens lo (m + 1) h_enc (by omega) h_wt_seg
    exact ih (m + 1) hi (by omega) ⟨h_win', h_deep', h_enc', h_close_hi, by omega, h_hi_hi0⟩
  exact key lo hi ⟨h_win0, h_deep0, h_enc0, h_close0, h_lo0, h_hi0⟩

/-- **The seq navigator's DESCEND-TAIL edge, extracted** — `(γ‴, R511)`: the per-window guard descent
    past a depth-`0` separator, lifted out of `seqWindowRecSeqBody_seq_general`'s (R415) inline ADVANCE
    block as a standalone, reusable lemma.  This is the guard-threading skeleton
    ([[ref-guard-threading-skeleton-before-grammar]]) — the genuine analytical brick that
    `recseqbody_navigator_driver` (R510) named as `descend_tail`.

    **What it discharges.**  The R510 driver reduces the whole seq navigator to two obligations,
    `locate` + `descend_tail`.  THIS is `descend_tail`: given the per-window seq guard at `[lo, hi)`
    and a depth-`0` separator located at `m` (`flowBracketBalance tokens lo m = 0`,
    `tokens[m] = .flowEntry`), it narrows the three structural guards (`FlowBodyWindow`,
    `FlowBodyContentDeepSeq`, `SeqEnclosed`) to the SUFFIX `[m+1, hi)` and proves the suffix is
    non-degenerate (`m + 1 < hi`).  It composes only landed advance edges — `flowBodyWindow_advance`,
    `flowBodyContentDeepSeq_advance`, `seqEnclosed_advance` — over the depth-`0` re-basing
    (`flowBracketBalance_compose` on the delta-`0` comma) verbatim from the inline block.

    **The finding it records** (sharpens the R510 reflection,
    [[ref-probe-deferred-universal-before-producing]]).  `descend_tail` is NOT keyed on
    `tokens[m] = .flowEntry` alone — as the R510 driver's signature naively typed it.  A `.flowEntry`
    can sit at any bracket depth, so the descend genuinely CONSUMES two extra facts the bare marker
    doesn't carry: `h_bal_m` (the depth-`0` balance, which `locate`/the dispatch DOES emit) and
    `h_content` (the CURRENT window's `FlowBodyContent`, used twice — to rule out the trailing comma
    `m + 1 = hi` via `feContentStart` + `tokens[hi] = .flowSequenceEnd`, and to discharge the
    re-scoped advance edge's `tokens[m+1] ≠ .key` premise).  So the driver's `descend_tail` must be
    re-typed to receive the located-separator balance, and the per-window guard `G` it threads must
    carry the window's content provider — exactly the carrier-free top-down-content obstacle of
    [[ref-width-recursion-cannot-thread-topdown-fact]], here pinned to its precise entry point.
    Note `h_content` is CONSUMED, not reproduced: the next window's content is re-sourced from the
    carrier/navigator, so the descend need not output `FlowBodyContent (m+1) hi`.

    Verified-but-unconsumed until the driver is re-typed and wired: composes only landed lemmas,
    references no sorry site, frontier sorry count unchanged at 4; axioms
    `[propext, Classical.choice, Quot.sound]` (seq-family profile, Classical inherited from the
    advance edges' WellTyped plumbing), no `sorryAx`. -/
theorem recseqbody_seq_descend_tail (tokens : Array (Positioned YamlToken)) (lo hi m : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeepSeq tokens lo hi)
    (h_enc : SeqEnclosed tokens lo)
    (h_content : FlowBodyContent tokens lo hi)
    (h_close : tokens[hi]!.val = .flowSequenceEnd)
    (h_lo_m : lo < m) (h_m_hi : m < hi)
    (h_bal_m : flowBracketBalance tokens lo m = 0)
    (h_sep : tokens[m]!.val = .flowEntry) :
    m + 1 < hi
      ∧ FlowBodyWindow tokens (m + 1) hi
      ∧ FlowBodyContentDeepSeq tokens (m + 1) hi
      ∧ SeqEnclosed tokens (m + 1) := by
  have h_hi_sz : hi < tokens.size := h_win.hi_lt
  have h_m_len : m < tokens.toList.length := by rw [Array.length_toList]; omega
  have h_m_val : tokens[m]! = tokens.toList[m]'h_m_len := by
    rw [getElem!_pos tokens m (by omega), Array.getElem_toList]
  have h_delta_m : flowBracketDelta tokens[m]!.val = 0 := by
    rw [h_sep]; exact flowBracketDelta_flowEntry
  have h_single_m : flowBracketBalance tokens m (m + 1) = flowBracketDelta tokens[m]!.val := by
    rw [flowBracketBalance_single tokens m h_m_len, ← h_m_val]
  have h_bal_m1 : flowBracketBalance tokens lo (m + 1) = 0 := by
    have hc := flowBracketBalance_compose tokens lo m (m + 1) (by omega) (Nat.le_succ m)
    rw [h_bal_m, h_single_m, h_delta_m] at hc; omega
  have h_m1_hi : m + 1 < hi := by
    rcases Nat.lt_or_ge (m + 1) hi with h | h
    · exact h
    · exfalso
      have h_eq : m + 1 = hi := by omega
      obtain ⟨_, h_cs⟩ :=
        h_content.feContentStart m (Nat.le_of_lt h_lo_m) h_m_hi h_sep h_bal_m
      rw [h_eq, h_close] at h_cs
      simp [isFlowContentStart] at h_cs
  have h_wt_seg : WellTyped ((tokens.toList.take (m + 1)).drop lo) :=
    WellTyped_subrange tokens lo lo (m + 1) hi (Nat.le_refl lo) (by omega) (by omega)
      (Nat.le_of_lt h_win.hi_lt) h_win.wellTyped h_bal_m1
      (fun p hp1 hp2 => h_win.dyck p hp1 (by omega))
  have h_win' : FlowBodyWindow tokens (m + 1) hi :=
    flowBodyWindow_advance tokens lo m hi h_win (Nat.le_of_lt h_lo_m) h_m1_hi h_bal_m h_sep
  have h_m1_content : isFlowContentStart tokens[m + 1]!.val :=
    (h_content.feContentStart m (Nat.le_of_lt h_lo_m) h_m_hi h_sep h_bal_m).2
  have h_m1_ne_key : tokens[m + 1]!.val ≠ .key := by
    unfold isFlowContentStart at h_m1_content
    rcases h_m1_content with ⟨c, s, h⟩ | h | h <;> simp [h]
  have h_deep' : FlowBodyContentDeepSeq tokens (m + 1) hi :=
    flowBodyContentDeepSeq_advance tokens lo m hi h_deep (Nat.le_of_lt h_lo_m) h_sep h_m1_ne_key h_m1_hi
  have h_enc' : SeqEnclosed tokens (m + 1) :=
    seqEnclosed_advance tokens lo (m + 1) h_enc (by omega) h_wt_seg
  exact ⟨h_m1_hi, h_win', h_deep', h_enc'⟩

/-- **The MAP navigator's DESCEND-TAIL edge** — the map twin of `recseqbody_seq_descend_tail` (R511),
    the per-window guard descent past a depth-`0` pair-end separator, lifted out of the map driver's
    inline ADVANCE block exactly as the seq edge was lifted out of `seqWindowRecSeqBody_seq_general`.
    This is the map `descend_tail` brick the width-recursion `mapWindowRecMapBody_map_general` (the
    R415 analog) consumes: given the per-window map guard at `[lo, hi)` and a depth-`0` `.flowEntry`
    pair-end `m` (`flowBracketBalance tokens lo m = 0`, `tokens[m] = .flowEntry`), it narrows the three
    structural map guards (`FlowBodyWindow`, `FlowBodyContentDeepMap`, `MapEnclosed`) to the SUFFIX
    `[m+1, hi)` and proves the suffix non-degenerate (`m + 1 < hi`).

    **The seq/map asymmetry — ONE per-window separator-successor fact, dual obligation, opposite
    polarity** ([[ref-descend-tail-dual-use-separator-successor]]).  The seq descend-tail reads its two
    head-shape facts from the window's `FlowBodyContent.feContentStart` (a depth-`0`-gated derived fact):
    it serves both (O1) the no-trailing-separator argument — `m + 1 = hi` would force
    `isFlowContentStart tokens[hi]`, contradicting `tokens[hi] = .flowSequenceEnd` — and (O2) the deep
    advance's `tokens[m+1] ≠ .key` premise.  The map descend-tail reads the DUAL fact from
    `MapBodyProps.after_fe` (M2, the unconditional `,→.key` form, [[ref-threading-form-vs-assemble-form]]):
    at the located separator it yields `tokens[m+1] = .key` directly, and that single fact discharges
    BOTH obligations — (O1) `m + 1 = hi` would force `tokens[hi] = .key`, contradicting
    `tokens[hi] = .flowMappingEnd`; (O2) `flowBodyContentDeepMap_advance`'s child-head premise IS
    `tokens[m+1] = .key`, supplied verbatim.  So the map edge is structurally SIMPLER than the seq
    edge: there is no `isFlowContentStart`-unfold to extract `≠ .key` (the map deep guard is
    advance-only, its child head is the positive `.key`, [[ref-mirror-reads-conjunct-not-projection]]),
    and it takes the per-window grammar bundle `MapBodyProps` where the seq edge takes
    `FlowBodyContent`.  The balance-`0` re-basing of the comma (`flowBracketBalance_compose` on the
    delta-`0` `.flowEntry`) and the `WellTyped` segment for `mapEnclosed_advance` are verbatim from the
    seq edge.

    Verified-but-unconsumed until the map width-recursion driver is wired: composes only landed advance
    edges (`flowBodyWindow_advance`, `flowBodyContentDeepMap_advance`, `mapEnclosed_advance`) over the
    depth-`0` re-basing, references no sorry site, frontier sorry count unchanged at 4.  `sorryAx`-free
    — it reads only `MapBodyProps.after_fe` and pure bracket-balance/`WellTyped` plumbing, never the
    tainted structure lemma ([[ref-mirror-inherits-dependency-axioms]]). -/
theorem recmapbody_map_descend_tail (tokens : Array (Positioned YamlToken)) (lo hi m : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeepMap tokens lo hi)
    (h_enc : MapEnclosed tokens lo)
    (h_props : MapBodyProps tokens lo hi)
    (h_close : tokens[hi]!.val = .flowMappingEnd)
    (h_lo_m : lo < m) (h_m_hi : m < hi)
    (h_bal_m : flowBracketBalance tokens lo m = 0)
    (h_sep : tokens[m]!.val = .flowEntry) :
    m + 1 < hi
      ∧ FlowBodyWindow tokens (m + 1) hi
      ∧ FlowBodyContentDeepMap tokens (m + 1) hi
      ∧ MapEnclosed tokens (m + 1) := by
  have h_hi_sz : hi < tokens.size := h_win.hi_lt
  -- balance lo (m+1) = 0 (the comma separator carries bracket-delta `0`)
  have h_m_len : m < tokens.toList.length := by rw [Array.length_toList]; omega
  have h_m_val : tokens[m]! = tokens.toList[m]'h_m_len := by
    rw [getElem!_pos tokens m (by omega), Array.getElem_toList]
  have h_delta_m : flowBracketDelta tokens[m]!.val = 0 := by
    rw [h_sep]; exact flowBracketDelta_flowEntry
  have h_single_m : flowBracketBalance tokens m (m + 1) = flowBracketDelta tokens[m]!.val := by
    rw [flowBracketBalance_single tokens m h_m_len, ← h_m_val]
  have h_bal_m1 : flowBracketBalance tokens lo (m + 1) = 0 := by
    have hc := flowBracketBalance_compose tokens lo m (m + 1) (by omega) (Nat.le_succ m)
    rw [h_bal_m, h_single_m, h_delta_m] at hc; omega
  -- `after_fe` (M2) at the located separator: the child head is `.key`, the DUAL of the seq edge's
  -- `feContentStart` — one fact serving both the no-trailing-separator horn and the deep advance.
  obtain ⟨_h_m1_le, h_m1_key⟩ := h_props.after_fe m (Nat.le_of_lt h_lo_m) h_m_hi h_bal_m h_sep
  -- O1: no trailing separator — `m + 1 = hi` would force `tokens[hi] = .key`, but it is `.flowMappingEnd`.
  have h_m1_hi : m + 1 < hi := by
    rcases Nat.lt_or_ge (m + 1) hi with h | h
    · exact h
    · exfalso
      have h_eq : m + 1 = hi := by omega
      rw [h_eq, h_close] at h_m1_key
      exact absurd h_m1_key (by decide)
  -- O2: WellTyped segment [lo, m+1) for the enclosure frame.
  have h_wt_seg : WellTyped ((tokens.toList.take (m + 1)).drop lo) :=
    WellTyped_subrange tokens lo lo (m + 1) hi (Nat.le_refl lo) (by omega) (by omega)
      (Nat.le_of_lt h_win.hi_lt) h_win.wellTyped h_bal_m1
      (fun p hp1 hp2 => h_win.dyck p hp1 (by omega))
  have h_win' : FlowBodyWindow tokens (m + 1) hi :=
    flowBodyWindow_advance tokens lo m hi h_win (Nat.le_of_lt h_lo_m) h_m1_hi h_bal_m h_sep
  -- the map deep advance takes the child head `tokens[m+1] = .key` straight from `after_fe`.
  have h_deep' : FlowBodyContentDeepMap tokens (m + 1) hi :=
    flowBodyContentDeepMap_advance tokens lo m hi h_deep (Nat.le_of_lt h_lo_m) h_sep h_m1_key h_m1_hi
  have h_enc' : MapEnclosed tokens (m + 1) :=
    mapEnclosed_advance tokens lo (m + 1) h_enc (by omega) h_wt_seg
  exact ⟨h_m1_hi, h_win', h_deep', h_enc'⟩

/-- **The JOINT navigator DESCEND-TAIL edge** — `(i'-b-B2c-desc-joint-descend-tail)`, R530.  The
    `descend_tail` companion of `recbody_joint_navigator_driver` (R529): the seq edge
    `recseqbody_seq_descend_tail` (R511) and the map edge `recmapbody_map_descend_tail` (R526) folded
    into ONE descend, **dispatched on the window close token** — the analytical core the joint driver's
    `descend_tail` slot consumes.

    **What it produces.**  The joint guard's REPRODUCED part at the suffix `[m+1, hi)`: the shared
    `FlowBodyWindow`, the close-token-dispatched deep-content + enclosure pair
    (`FlowBodyContentDeepSeq ∧ SeqEnclosed` on the seq close, `FlowBodyContentDeepMap ∧ MapEnclosed` on
    the map close), and the close-token disjunction itself (preserved verbatim — the suffix shares the
    window's close `hi`).  Each half is exactly what its single edge reproduces; the conjunctive shape
    is the joint guard of [[ref-joint-navigator-cross-deliverable]] viewed at the descend layer.

    **What it CONSUMES but does NOT reproduce — the two visible debts.**  The single edges read facts
    the recursion cannot thread top-down ([[ref-width-recursion-cannot-thread-topdown-fact]]), so they
    appear here as *explicit hypotheses*, not stored in the reproduced guard:
    * `h_bal_m` — the located separator's depth-`0` balance.  The bare marker `tokens[m] = .flowEntry`
      does NOT pin depth `0` (a comma can sit inside a nested collection), so both single edges genuinely
      consume it ([[ref-probe-deferred-universal-before-producing]], the R511 finding).  Wiring this into
      the driver requires the driver's `locate` marker to carry the balance and its `descend_tail` slot
      to receive it — the marker-strengthening brick.
    * `h_seq_pack` / `h_map_pack` — the per-window content provider (`FlowBodyContent` on the seq close,
      `MapBodyProps` on the map close), which the single edges consume to rule out the trailing separator
      and to discharge the deep-advance child-head premise, but which they CANNOT reproduce at the suffix
      (the carrier-free obstacle).  Here they are close-token-GATED inputs; the future concrete
      `descend_tail` sources them from the fixed outer carrier per-window (via
      `seqWindow_flowBodyContent_seq_general` and its map twin), exactly as the inline R415 recursions do.

    **The dispatch.**  `rcases` the close disjunction; in each branch unpack the matching content pack,
    call the matching single edge, and reassemble.  The OFF-branch implication is discharged *vacuously*
    by close-token disjointness: in the seq branch a `tokens[hi] = .flowMappingEnd` premise contradicts
    `tokens[hi] = .flowSequenceEnd` (`by decide` on the constructor equality), so the map half holds for
    any goal, and symmetrically.  No new analytical content beyond the two landed single edges — this is
    [[ref-navigator-driver-stitch-two-obligations]] applied to `descend_tail`: one obligation, two
    collection-keyed halves, stitched by the discriminator.

    Verified-but-unconsumed until the driver is re-typed (marker carries `h_bal_m`) and the carrier feeds
    the content packs: composes only `recseqbody_seq_descend_tail` + `recmapbody_map_descend_tail`,
    references no sorry site, frontier sorry count unchanged at 4; axioms
    `[propext, Classical.choice, Quot.sound]` (inherited from the two single edges' WellTyped plumbing),
    no `sorryAx`.  Demo `Tests/Reflections/JointDescendTailDispatch.lean`. -/
theorem recbody_joint_descend_tail (tokens : Array (Positioned YamlToken)) (lo hi m : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_close : tokens[hi]!.val = .flowSequenceEnd ∨ tokens[hi]!.val = .flowMappingEnd)
    (h_seq_pack : tokens[hi]!.val = .flowSequenceEnd →
        FlowBodyContentDeepSeq tokens lo hi ∧ SeqEnclosed tokens lo ∧ FlowBodyContent tokens lo hi)
    (h_map_pack : tokens[hi]!.val = .flowMappingEnd →
        FlowBodyContentDeepMap tokens lo hi ∧ MapEnclosed tokens lo ∧ MapBodyProps tokens lo hi)
    (h_lo_m : lo < m) (h_m_hi : m < hi)
    (h_bal_m : flowBracketBalance tokens lo m = 0)
    (h_sep : tokens[m]!.val = .flowEntry) :
    FlowBodyWindow tokens (m + 1) hi
      ∧ (tokens[hi]!.val = .flowSequenceEnd →
          FlowBodyContentDeepSeq tokens (m + 1) hi ∧ SeqEnclosed tokens (m + 1))
      ∧ (tokens[hi]!.val = .flowMappingEnd →
          FlowBodyContentDeepMap tokens (m + 1) hi ∧ MapEnclosed tokens (m + 1))
      ∧ (tokens[hi]!.val = .flowSequenceEnd ∨ tokens[hi]!.val = .flowMappingEnd) := by
  rcases h_close with h_seqEnd | h_mapEnd
  · obtain ⟨h_deep, h_enc, h_content⟩ := h_seq_pack h_seqEnd
    obtain ⟨_, h_win', h_deep', h_enc'⟩ :=
      recseqbody_seq_descend_tail tokens lo hi m h_win h_deep h_enc h_content h_seqEnd
        h_lo_m h_m_hi h_bal_m h_sep
    exact ⟨h_win', fun _ => ⟨h_deep', h_enc'⟩,
      fun h_mapEnd => absurd (h_mapEnd.symm.trans h_seqEnd) (by decide), Or.inl h_seqEnd⟩
  · obtain ⟨h_deep, h_enc, h_props⟩ := h_map_pack h_mapEnd
    obtain ⟨_, h_win', h_deep', h_enc'⟩ :=
      recmapbody_map_descend_tail tokens lo hi m h_win h_deep h_enc h_props h_mapEnd
        h_lo_m h_m_hi h_bal_m h_sep
    exact ⟨h_win', fun h_seqEnd => absurd (h_seqEnd.symm.trans h_mapEnd) (by decide),
      fun _ => ⟨h_deep', h_enc'⟩, Or.inr h_mapEnd⟩

/-- **The JOINT per-window CONTENT-PACK provider** — `(i'-b-B2c-desc-joint-content-pack)`, R531.  The
    carrier→content feed for the joint descend `recbody_joint_descend_tail` (R530): it manufactures
    EXACTLY R530's two close-gated content packs (`h_seq_pack` / `h_map_pack`) from the navigator
    guard's close-gated deep/enclosure pieces plus the two fixed outer carriers — **discharging the
    second of R530's two visible debts** (the top-down content provider).

    **What it discharges.**  R530 takes `h_seq_pack : seqEnd → DeepSeq ∧ SeqEnc ∧ FlowBodyContent` and
    `h_map_pack : mapEnd → DeepMap ∧ MapEnc ∧ MapBodyProps` as opaque close-gated inputs — the
    carrier-free obstacle ([[ref-width-recursion-cannot-thread-topdown-fact]]): the single edges consume
    `FlowBodyContent` / `MapBodyProps` to rule out a trailing separator and to discharge the deep-advance
    child-head premise, but cannot reproduce them at the suffix.  This provider supplies them per-window
    from a FIXED OUTER carrier seeded once at the root and narrowed in place
    ([[ref-narrow-from-root-breaks-rederivation-cycle]]) — exactly as the inline R415 recursions do —
    composing `seqWindow_flowBodyContent_seq_general` (seq close, `SeqInteriorSeparators` carrier) and
    `mapWindow_mapBodyProps_general` (map close, `MapInteriorSeparators` carrier).  The deep/enclosure
    conjuncts are NOT re-derived: they pass straight through from the guard's close-gated halves
    (`h_seq_guard` / `h_map_guard`, the shape `recbody_joint_descend_tail` produces and the joint driver
    threads).  So this lemma's OUTPUT is precisely R530's `h_seq_pack` / `h_map_pack` inputs — the two
    compose end-to-end.

    **The remaining map-carrier debt, kept legible.**  The map provider needs ONE fact neither carrier
    bundles: `h_after_fe` (M2 — every depth-`0` comma is followed by a `.key`).  The seq carrier
    `SeqInteriorSeparators` self-sources its comma-successor fact (`noTrailingSepFact`), but the map
    carrier `MapInteriorSeparators` defers M2 ([[ref-additive-field-cost-by-keying]] — the asymmetry
    `mapWindow_mapBodyProps_general` records), so it stays an EXPLICIT supplied hypothesis here rather
    than being hidden in a carrier.  This is the map analog of R530's debt-exposure discipline: a fact
    the recursion cannot reproduce is a visible interface input, not a silent gap.  R530's OTHER debt —
    the located separator's depth-`0` balance `h_bal_m` — is orthogonal to content and stays the
    driver-marker-strengthening brick; this provider touches only the content debt.

    Verified-but-unconsumed until the joint driver threads the two carriers (+ M2) per-window and pairs
    this with R530: composes only `seqWindow_flowBodyContent_seq_general` +
    `mapWindow_mapBodyProps_general`, references no sorry site, frontier sorry count unchanged at 4;
    axioms `[propext, Classical.choice, Quot.sound]` (inherited from the map provider's typed-locator
    plumbing — the seq half is axiom-clean), no `sorryAx`.  Demo
    `Tests/Reflections/JointContentPackFromCarrier.lean`. -/
theorem recbody_joint_content_pack (tokens : Array (Positioned YamlToken))
    (lo0 hi0 lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_seq_guard : tokens[hi]!.val = .flowSequenceEnd →
        FlowBodyContentDeepSeq tokens lo hi ∧ SeqEnclosed tokens lo)
    (h_map_guard : tokens[hi]!.val = .flowMappingEnd →
        FlowBodyContentDeepMap tokens lo hi ∧ MapEnclosed tokens lo)
    (h_seq_carrier : SeqInteriorSeparators tokens lo0 hi0)
    (h_map_carrier : MapInteriorSeparators tokens lo0 hi0)
    (h_after_fe : ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .flowEntry →
        k + 1 ≤ hi ∧ tokens[k + 1]!.val = .key)
    (h_lo0 : lo0 ≤ lo) (h_hi0 : hi ≤ hi0) :
    (tokens[hi]!.val = .flowSequenceEnd →
        FlowBodyContentDeepSeq tokens lo hi ∧ SeqEnclosed tokens lo ∧ FlowBodyContent tokens lo hi)
      ∧ (tokens[hi]!.val = .flowMappingEnd →
          FlowBodyContentDeepMap tokens lo hi ∧ MapEnclosed tokens lo ∧ MapBodyProps tokens lo hi) := by
  refine ⟨fun h_seqEnd => ?_, fun h_mapEnd => ?_⟩
  · obtain ⟨h_deep, h_enc⟩ := h_seq_guard h_seqEnd
    exact ⟨h_deep, h_enc,
      seqWindow_flowBodyContent_seq_general tokens lo0 hi0 lo hi h_win h_deep h_enc
        h_seq_carrier h_lo0 h_hi0⟩
  · obtain ⟨h_deep, h_enc⟩ := h_map_guard h_mapEnd
    exact ⟨h_deep, h_enc,
      mapWindow_mapBodyProps_general tokens lo0 hi0 lo hi h_win h_deep h_enc h_mapEnd
        h_after_fe h_map_carrier h_lo0 h_hi0⟩

/-- **The carrier-fed concrete JOINT descend-tail** — `(i'-b-B2c-desc-joint-carrier)`, R532.  The
    composition of the two landed joint bricks: `recbody_joint_content_pack` (R531) feeds its output
    into `recbody_joint_descend_tail` (R530)'s OPAQUE content slot, yielding the concrete `descend_tail`
    the strengthened joint driver (R529) needs — no longer asking for the irreproducible top-down content
    fact, but for the root carriers (reproducible by narrowing in place).

    **Why this is the next brick.**  R530 takes its content packs `h_seq_pack` / `h_map_pack`
    (`Deep* ∧ *Enc ∧ Content*`) as opaque close-gated inputs because the width recursion cannot reproduce
    `FlowBodyContent` / `MapBodyProps` at a descended suffix
    ([[ref-width-recursion-cannot-thread-topdown-fact]]).  R531 manufactures EXACTLY those packs from the
    guard's close-gated deep/enclosure halves plus the two fixed outer carriers
    ([[ref-content-pack-passthrough-manufacture]]).  Because R531's OUTPUT type is, conjunct for conjunct,
    R530's pack INPUT type, the two compose with no glue: `obtain ⟨h_seq_pack, h_map_pack⟩ := R531 …; exact
    R530 … h_seq_pack h_map_pack …`.

    **What the composition BUYS — the interface retype** ([[ref-reduction-by-import]]).  Importing the
    provider into the consumer's opaque slot does not shrink the sorry count; it RETYPES the descend's
    interface.  R530 stated bare took two debts: the content packs (top-down, irreproducible) and the
    marker's depth-`0` balance `h_bal_m`.  This lemma DISCHARGES the content debt by importing R531, so the
    surviving inputs are the carrier interface — the two outer carriers
    `SeqInteriorSeparators` / `MapInteriorSeparators tokens lo0 hi0` (root-seeded, narrowed per window via
    the frame bounds `lo0 ≤ lo ∧ hi ≤ hi0`, [[ref-narrow-from-root-breaks-rederivation-cycle]]), the
    map-carrier-deferred fact `h_after_fe` (M2, the asymmetric input the map carrier defers,
    [[ref-additive-field-cost-by-keying]]), and the still-explicit `h_bal_m`.  The descend now asks only
    for facts the recursion CAN supply: the carrier is reproducible top-down, and `h_bal_m` is what the
    driver's strengthened `locate` marker will carry.  That retype — top-down content → root carrier — is
    the progress.

    **What it produces.**  Exactly R530's deliverable at the suffix `[m+1, hi)`: the shared
    `FlowBodyWindow`, the close-token-dispatched deep+enclosure pair, and the close disjunction — i.e. the
    suffix value of the joint guard `G (m+1) hi` of [[ref-joint-navigator-cross-deliverable]].  So this is
    the concrete `descend_tail` slot for the strengthened driver once `G` projects to the close-gated
    halves and threads the carriers + M2 + the marker balance.

    Verified-but-unconsumed until the driver's `locate` markers carry `h_bal_m` and `G` is folded:
    composes only `recbody_joint_content_pack` + `recbody_joint_descend_tail`, references no sorry site,
    frontier sorry count unchanged at 4; axioms `[propext, Classical.choice, Quot.sound]` (inherited from
    R530/R531's typed-locator plumbing), no `sorryAx`.  Demo
    `Tests/Reflections/JointDescendTailCarrier.lean`. -/
theorem recbody_joint_descend_tail_carrier (tokens : Array (Positioned YamlToken))
    (lo0 hi0 lo hi m : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_seq_guard : tokens[hi]!.val = .flowSequenceEnd →
        FlowBodyContentDeepSeq tokens lo hi ∧ SeqEnclosed tokens lo)
    (h_map_guard : tokens[hi]!.val = .flowMappingEnd →
        FlowBodyContentDeepMap tokens lo hi ∧ MapEnclosed tokens lo)
    (h_close : tokens[hi]!.val = .flowSequenceEnd ∨ tokens[hi]!.val = .flowMappingEnd)
    (h_seq_carrier : SeqInteriorSeparators tokens lo0 hi0)
    (h_map_carrier : MapInteriorSeparators tokens lo0 hi0)
    (h_after_fe : ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .flowEntry →
        k + 1 ≤ hi ∧ tokens[k + 1]!.val = .key)
    (h_lo0 : lo0 ≤ lo) (h_hi0 : hi ≤ hi0)
    (h_lo_m : lo < m) (h_m_hi : m < hi)
    (h_bal_m : flowBracketBalance tokens lo m = 0)
    (h_sep : tokens[m]!.val = .flowEntry) :
    FlowBodyWindow tokens (m + 1) hi
      ∧ (tokens[hi]!.val = .flowSequenceEnd →
          FlowBodyContentDeepSeq tokens (m + 1) hi ∧ SeqEnclosed tokens (m + 1))
      ∧ (tokens[hi]!.val = .flowMappingEnd →
          FlowBodyContentDeepMap tokens (m + 1) hi ∧ MapEnclosed tokens (m + 1))
      ∧ (tokens[hi]!.val = .flowSequenceEnd ∨ tokens[hi]!.val = .flowMappingEnd) := by
  obtain ⟨h_seq_pack, h_map_pack⟩ :=
    recbody_joint_content_pack tokens lo0 hi0 lo hi h_win h_seq_guard h_map_guard
      h_seq_carrier h_map_carrier h_after_fe h_lo0 h_hi0
  exact recbody_joint_descend_tail tokens lo hi m h_win h_close h_seq_pack h_map_pack
    h_lo_m h_m_hi h_bal_m h_sep

/-- **The concrete JOINT navigator guard** — `(i'-b-B2c-desc-joint-guard)`, R533.  The named predicate
    `recbody_joint_navigator_driver`'s abstract `G : Nat → Nat → Prop` is instantiated to, folding the
    REPRODUCIBLE part of the joint recursion into one window-keyed conjunction: the frame bounds
    `lo0 ≤ lo ∧ hi ≤ hi0` (the per-window narrowing witnesses for the two root carriers,
    [[ref-narrow-from-root-breaks-rederivation-cycle]]), the shared `FlowBodyWindow`, the two
    close-token-gated deep+enclosure halves, and the close-token disjunction itself.

    Each conjunct is exactly what `recbody_joint_descend_tail_carrier` (R532) consumes from / produces at
    a window: bundling them into one named `G` is [[ref-consumer-joint-before-producer]] at the guard
    layer — the conjunctive guard that lets ONE `windowWidth_strongRecOn` feed both close-keyed bodies.
    The two outer carriers + the map-deferred M2 (`h_after_fe`) are NOT folded in: they are fixed-at-root
    and reproduced top-down by narrowing, so they stay the driver's outer inputs, not the per-window
    guard. -/
def RecBodyJointGuard (tokens : Array (Positioned YamlToken)) (lo0 hi0 lo hi : Nat) : Prop :=
  lo0 ≤ lo ∧ hi ≤ hi0
    ∧ FlowBodyWindow tokens lo hi
    ∧ (tokens[hi]!.val = .flowSequenceEnd →
        FlowBodyContentDeepSeq tokens lo hi ∧ SeqEnclosed tokens lo)
    ∧ (tokens[hi]!.val = .flowMappingEnd →
        FlowBodyContentDeepMap tokens lo hi ∧ MapEnclosed tokens lo)
    ∧ (tokens[hi]!.val = .flowSequenceEnd ∨ tokens[hi]!.val = .flowMappingEnd)

/-- **The descend-tail at the concrete guard** — `(i'-b-B2c-desc-joint-guard-descend)`, R533.  Lifts the
    carrier-fed concrete descend `recbody_joint_descend_tail_carrier` (R532) from the UNPACKED window
    halves to the PACKED named guard `RecBodyJointGuard` — the shape
    `recbody_joint_navigator_driver`'s `descend_tail` slot demands (`G lo hi → … → G (m+1) hi`).

    **What it does.**  Project `G lo hi` to its six conjuncts (frame bounds + window + the two close-gated
    halves + close disjunction), feed window + halves + close + the two fixed outer carriers + M2 +
    marker facts into R532, and re-pack R532's four-way suffix deliverable as `G (m+1) hi`.  The only
    non-pass-through is the suffix frame LOWER bound `lo0 ≤ m+1`, re-established by `omega` from
    `lo0 ≤ lo` and `lo < m`; the UPPER bound `hi ≤ hi0` is shared with the window's close `hi` and carries
    verbatim.  So the guard's frame half narrows exactly as the carriers need at the descended window.

    **What it RETYPES, not discharges** ([[ref-reduction-by-import]], [[ref-opaque-edge-imports-provider]]).
    This is the guard-fold half of the driver re-type (brick (2) piece (i)).  R532 already retyped the
    descend from "needs top-down content" to "needs the root carriers"; this lemma packages that retyped
    edge against the named `G`, so the surviving inputs beyond the driver's bare `descend_tail` signature
    are precisely the still-explicit plumbing the driver must thread: the two carriers (fixed at root),
    the map-deferred `h_after_fe` (M2, [[ref-additive-field-cost-by-keying]]), and the marker balance
    `h_bal_m` (what the driver's strengthened `locate` will carry, [[ref-joint-navigator-cross-deliverable]]).
    Everything the recursion CAN reproduce is now inside `G`; everything it cannot is a named outer input.

    Verified-but-unconsumed until the driver's `locate` markers carry `h_bal_m`, the carriers are threaded
    per-window, and `h_after_fe` is narrowed from a global M2: composes only
    `recbody_joint_descend_tail_carrier`, references no sorry site, frontier sorry count unchanged at 4;
    axioms `[propext, Classical.choice, Quot.sound]` (inherited from R532), no `sorryAx`.  Demo
    `Tests/Reflections/JointGuardDescendTail.lean`. -/
theorem recbody_joint_guard_descend_tail (tokens : Array (Positioned YamlToken))
    (lo0 hi0 lo hi m : Nat)
    (h_seq_carrier : SeqInteriorSeparators tokens lo0 hi0)
    (h_map_carrier : MapInteriorSeparators tokens lo0 hi0)
    (h_after_fe : ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .flowEntry →
        k + 1 ≤ hi ∧ tokens[k + 1]!.val = .key)
    (h_g : RecBodyJointGuard tokens lo0 hi0 lo hi)
    (h_lo_m : lo < m) (h_m_hi : m < hi)
    (h_bal_m : flowBracketBalance tokens lo m = 0)
    (h_sep : tokens[m]!.val = .flowEntry) :
    RecBodyJointGuard tokens lo0 hi0 (m + 1) hi := by
  unfold RecBodyJointGuard at h_g ⊢
  obtain ⟨h_lo0, h_hi0, h_win, h_seq_guard, h_map_guard, h_close⟩ := h_g
  obtain ⟨h_win', h_seq_guard', h_map_guard', h_close'⟩ :=
    recbody_joint_descend_tail_carrier tokens lo0 hi0 lo hi m h_win h_seq_guard h_map_guard
      h_close h_seq_carrier h_map_carrier h_after_fe h_lo0 h_hi0 h_lo_m h_m_hi h_bal_m h_sep
  exact ⟨by omega, h_hi0, h_win', h_seq_guard', h_map_guard', h_close'⟩

/-- **The CARRIER-specialised JOINT body navigator driver** — `(i'-b-B2c-desc-joint-navigator-carrier)`,
    R534.  The concrete instantiation of `recbody_joint_navigator_driver` (R529) at the named guard
    `G := RecBodyJointGuard tokens lo0 hi0`, with the `descend_tail` slot DISCHARGED by R533
    `recbody_joint_guard_descend_tail` and the two root carriers + the map-deferred `h_after_fe` (M2)
    threaded as fixed inputs.

    **What collapses.**  Where the abstract driver R529 left `G`, `locate_seq`, `locate_map`, AND
    `descend_tail` all open, this brick fixes `G` to the folded guard and supplies `descend_tail` from
    R533 — so the remaining obligations shrink to exactly the two collection-`locate`s.  Each is now
    STRENGTHENED to emit the located separator's depth-`0` balance `flowBracketBalance tokens lo m = 0`
    (the extra `∃`-conjunct), because R533's `h_bal_m` consumes that balance to narrow the carrier.  The
    driver ROUTES the balance straight from the locate output into the guard descend
    ([[ref-route-producer-fact-to-consumer-slot-through-recursion]]): the recursion combinator is
    agnostic to it, so a producer-side fact (the locate knows where `m` sits and at what depth) reaches a
    consumer-side premise (the descend narrows the carrier there) purely by widening the locate's `∃` and
    the descend's premise in lockstep — the body merely carries it across the `oracle`/`assemble` stitch.

    **What is threaded vs deferred.**  The two carriers are keyed at the fixed outer span `lo0 hi0` and
    narrowed per window by the guard's frame bounds (R533).  `h_after_fe` (M2) is taken per-window-keyed
    ON the guard, deferring the global→per-window narrowing (the `flowBracketBalance tokens lo k`
    re-basing across windows) to a later brick.  `h_hi_sz` is no longer a separate input — it is the
    trivial projection `(·.2.2.1.hi_lt)` off the guard's window invariant.

    Verified-but-unconsumed until the two strengthened `locate`s are supplied (R527-fed seq dispatch +
    the map pair locator, each emitting the balance) and M2 is narrowed from the global field: composes
    `windowWidth_strongRecOn` + both window assemblers + `recbody_joint_guard_descend_tail`, references no
    sorry site, frontier sorry count unchanged at 4; axioms `[propext, Classical.choice, Quot.sound]`
    (inherited from R532/R533 and the assemblers). -/
theorem recbody_joint_navigator_driver_carrier (tokens : Array (Positioned YamlToken))
    (lo0 hi0 : Nat)
    (h_seq_carrier : SeqInteriorSeparators tokens lo0 hi0)
    (h_map_carrier : MapInteriorSeparators tokens lo0 hi0)
    (h_after_fe : ∀ lo hi, RecBodyJointGuard tokens lo0 hi0 lo hi →
        ∀ k, lo ≤ k → k < hi →
          flowBracketBalance tokens lo k = 0 →
          tokens[k]!.val = .flowEntry →
          k + 1 ≤ hi ∧ tokens[k + 1]!.val = .key)
    (locate_seq : ∀ lo hi, RecBodyJointGuard tokens lo0 hi0 lo hi →
        tokens[hi]!.val = .flowSequenceEnd →
        (∀ lo' hi', hi' - lo' < hi - lo → RecBodyJointGuard tokens lo0 hi0 lo' hi' →
          (tokens[hi']!.val = .flowSequenceEnd → RecSeqBody ((tokens.toList.take hi').drop lo')) ∧
          (tokens[hi']!.val = .flowMappingEnd → RecMapBody ((tokens.toList.take hi').drop lo'))) →
        ∃ m, lo < m ∧ m ≤ hi ∧
          (m = hi ∨ tokens[m]!.val = .flowEntry) ∧
          flowBracketBalance tokens lo m = 0 ∧
          RecSeqEntry ((tokens.toList.take m).drop lo))
    (locate_map : ∀ lo hi, RecBodyJointGuard tokens lo0 hi0 lo hi →
        tokens[hi]!.val = .flowMappingEnd →
        (∀ lo' hi', hi' - lo' < hi - lo → RecBodyJointGuard tokens lo0 hi0 lo' hi' →
          (tokens[hi']!.val = .flowSequenceEnd → RecSeqBody ((tokens.toList.take hi').drop lo')) ∧
          (tokens[hi']!.val = .flowMappingEnd → RecMapBody ((tokens.toList.take hi').drop lo'))) →
        ∃ m, lo < m ∧ m ≤ hi ∧
          (m = hi ∨ tokens[m]!.val = .flowEntry) ∧
          flowBracketBalance tokens lo m = 0 ∧
          RecMapPair ((tokens.toList.take m).drop lo)) :
    ∀ lo hi, RecBodyJointGuard tokens lo0 hi0 lo hi →
      (tokens[hi]!.val = .flowSequenceEnd → RecSeqBody ((tokens.toList.take hi).drop lo)) ∧
      (tokens[hi]!.val = .flowMappingEnd → RecMapBody ((tokens.toList.take hi).drop lo)) := by
  refine windowWidth_strongRecOn (RecBodyJointGuard tokens lo0 hi0) (fun lo hi h_g oracle => ?_)
  refine ⟨fun h_seqEnd => ?_, fun h_mapEnd => ?_⟩
  · -- seq-closing window: locate first ENTRY (carrying its balance), assemble, descend via R533.
    obtain ⟨m, h_lo_m, h_m_hi, h_marker, h_bal, h_entry⟩ := locate_seq lo hi h_g h_seqEnd oracle
    refine recseqbody_window_assemble tokens lo m hi h_lo_m h_m_hi h_g.2.2.1.hi_lt
      h_marker h_entry (fun h_lt => ?_)
    have h_fe : tokens[m]!.val = .flowEntry := h_marker.resolve_left (by omega)
    exact (oracle (m + 1) hi (by omega)
      (recbody_joint_guard_descend_tail tokens lo0 hi0 lo hi m h_seq_carrier h_map_carrier
        (h_after_fe lo hi h_g) h_g h_lo_m h_lt h_bal h_fe)).1 h_seqEnd
  · -- map-closing window: locate first PAIR (carrying its balance), assemble, descend via R533.
    obtain ⟨m, h_lo_m, h_m_hi, h_marker, h_bal, h_pair⟩ := locate_map lo hi h_g h_mapEnd oracle
    refine recmapbody_window_assemble tokens lo m hi h_lo_m h_m_hi h_g.2.2.1.hi_lt
      h_marker h_pair (fun h_lt => ?_)
    have h_fe : tokens[m]!.val = .flowEntry := h_marker.resolve_left (by omega)
    exact (oracle (m + 1) hi (by omega)
      (recbody_joint_guard_descend_tail tokens lo0 hi0 lo hi m h_seq_carrier h_map_carrier
        (h_after_fe lo hi h_g) h_g h_lo_m h_lt h_bal h_fe)).2 h_mapEnd

/-- **The joint oracle → seq-only IH adapter** (Phase J — the cross-deliverable knot's SEQ half, the
    first concrete brick of the two `locate`s `recbody_joint_navigator_driver_carrier` (R534) still
    takes as inputs).  The carrier-specialised driver hands its per-window step a JOINT `oracle` — at
    every strictly-narrower sub-window `[lo', hi')` it delivers BOTH deliverables, keyed on the close
    marker: `(seqEnd → RecSeqBody) ∧ (mapEnd → RecMapBody)`.  But the seq first-entry dispatch
    `recseqentry_window_dispatch_seq` (R527) — and the map locate's single-entry sub-block producer
    `recseqentry_whole_window_seq` — consume a SEQ-ONLY induction hypothesis `h_ih` that delivers a bare
    `RecSeqBody` from window facts and an enclosure predicate `Q lo'`.  This lemma is the adapter between
    the two: instantiate the dispatch's `Q := SeqEnclosed tokens`, and this produces its exact `h_ih`
    from the joint `oracle`.

    **The move is guard RECONSTRUCTION + seq-side PROJECTION** ([[ref-reduction-by-import]] read at the
    oracle interface).  The joint oracle wants a `RecBodyJointGuard tokens lo0 hi0 lo' hi'` at the
    sub-window; the dispatch's `h_ih` hands over the loose pieces — `FlowBodyWindow tokens lo' hi'`,
    `FlowBodyContentDeepSeq tokens lo' hi'`, `SeqEnclosed tokens lo'` (the `Q lo'` choice), the close
    `tokens[hi']!.val = .flowSequenceEnd`, and the span/bound facts — so the proof FOLDS them back into
    the guard: the two outer bounds compose (`lo0 ≤ lo ≤ lo'`, `hi' ≤ hi ≤ hi0`); the window is verbatim;
    the seq conditional is discharged by `⟨h_deep, h_encl⟩` exactly because we are in the seq-close case;
    the map conditional is VACUOUS — its `tokens[hi']!.val = .flowMappingEnd` premise contradicts the
    seq close, so the marker disjointness collapses it ([[ref-converse-forward-invariant-asymmetry]]
    read as marker exclusivity); and the disjunct is `Or.inl` the seq close.  Folding done, the joint
    deliverable's `.1` applied to the seq close is the `RecSeqBody` the IH owes.

    **Why this is the seq half of the cross-deliverable knot.**  `seqWindowRecSeqBody_seq_general`
    already produces `RecSeqBody` for a window's seq IH — but only on the **all-seq PATH** domain
    (`SeqPathAllSeq`, every enclosing frame a `[`), because it sources nested deliverables from the seq
    carrier alone and a carrier cannot speak for a `{`-enclosed frame.  Drawing the IH from the JOINT
    oracle instead lifts that path restriction: the oracle delivers `RecSeqBody`/`RecMapBody` at EVERY
    narrower window regardless of enclosing-bracket type, so the dispatch threaded through this adapter
    is path-agnostic.  The map deliverable the oracle also carries is not consumed HERE — it flows on to
    the dispatch's `{`-bracket branch (the nested-map entry), the symmetric brick.

    Verified-but-unconsumed until `locate_seq`/`locate_map` are assembled (each = its dispatch at
    `Q := SeqEnclosed` fed this adapter, plus the per-window `FlowBodyContent` source): references no
    sorry site, frontier sorry count unchanged at 4.  `sorryAx`-free — pure guard folding over
    `RecBodyJointGuard` plus the oracle, no structure lemma and no choice, so it audits to the minimal
    `[propext, Quot.sound]`.  Demo `Tests/Reflections/JointOracleSeqIh.lean`. -/
theorem recbody_joint_oracle_seq_ih (tokens : Array (Positioned YamlToken))
    (lo0 hi0 lo hi : Nat) (h_lo0_lo : lo0 ≤ lo) (h_hi_hi0 : hi ≤ hi0)
    (oracle : ∀ lo' hi', hi' - lo' < hi - lo → RecBodyJointGuard tokens lo0 hi0 lo' hi' →
      (tokens[hi']!.val = .flowSequenceEnd → RecSeqBody ((tokens.toList.take hi').drop lo')) ∧
      (tokens[hi']!.val = .flowMappingEnd → RecMapBody ((tokens.toList.take hi').drop lo'))) :
    ∀ lo' hi', hi' - lo' < hi - lo → lo ≤ lo' → hi' ≤ hi →
      FlowBodyWindow tokens lo' hi' → FlowBodyContentDeepSeq tokens lo' hi' →
      SeqEnclosed tokens lo' → tokens[hi']!.val = .flowSequenceEnd →
      RecSeqBody ((tokens.toList.take hi').drop lo') := by
  intro lo' hi' h_span h_lo_lo' h_hi'_hi h_win h_deep h_encl h_seqEnd
  refine (oracle lo' hi' h_span ?_).1 h_seqEnd
  refine ⟨by omega, by omega, h_win, fun _ => ⟨h_deep, h_encl⟩, fun h_mapEnd => ?_, Or.inl h_seqEnd⟩
  rw [h_seqEnd] at h_mapEnd
  exact absurd h_mapEnd (by decide)

/-- **The joint oracle → map-only IH adapter** (Phase J — the cross-deliverable knot's MAP half, the
    SYMMETRIC twin of `recbody_joint_oracle_seq_ih` (R535) and the second concrete brick of the two
    `locate`s `recbody_joint_navigator_driver_carrier` (R534) takes as inputs).  Identical move, opposite
    axis: the carrier-specialised driver hands its per-window step the same JOINT `oracle` —
    `(seqEnd → RecSeqBody) ∧ (mapEnd → RecMapBody)` at every strictly-narrower sub-window — and the
    dispatch's `{`-bracket branch (the nested-map first-entry, served by `recmapentry_pair_located`'s
    sub-block producers) consumes a MAP-ONLY induction hypothesis `h_ih` that delivers a bare
    `RecMapBody` from window facts and a `Q lo'` enclosure predicate.  Instantiate the dispatch's
    `Q := MapEnclosed tokens`, and this produces its exact `h_ih` from the joint `oracle`.

    **The move is guard RECONSTRUCTION + map-side PROJECTION** ([[ref-reduction-by-import]] at the oracle
    interface), the exact mirror of R535.  The dispatch's `h_ih` hands over the loose pieces —
    `FlowBodyWindow tokens lo' hi'`, `FlowBodyContentDeepMap tokens lo' hi'`, `MapEnclosed tokens lo'`
    (the `Q lo'` choice), the close `tokens[hi']!.val = .flowMappingEnd`, and the span/bound facts — so
    the proof FOLDS them back into `RecBodyJointGuard tokens lo0 hi0 lo' hi'`: the two outer bounds
    compose by `omega`; the window is verbatim; the MAP conditional is discharged by `⟨h_deep, h_encl⟩`
    because we are in the map-close case; the SEQ conditional is now the VACUOUS one — its
    `tokens[hi']!.val = .flowSequenceEnd` premise contradicts the map close, so marker exclusivity
    (`decide` on `.flowMappingEnd = .flowSequenceEnd`, [[ref-converse-forward-invariant-asymmetry]] read
    as marker exclusivity) collapses it without any seq fact; and the disjunct is `Or.inr` the map close.
    Folding done, the joint deliverable's `.2` applied to the map close is the `RecMapBody` the IH owes.

    **Why this is the map half of the knot.**  A carrier-only map producer (the future
    `mapWindowRecMapBody_map_general`) would deliver `RecMapBody` for a window's map IH only on the
    all-map PATH (every enclosing frame a `{`); drawing the IH from the JOINT oracle is path-agnostic —
    the oracle delivers both bodies at EVERY narrower window regardless of enclosing-bracket type.  With
    this twin landed, BOTH branches of each dispatch (the `[`-nested seq entry via R535, the `{`-nested
    map entry via this) draw a path-general IH from the one joint oracle; the only surviving brick to
    assemble `locate_seq`/`locate_map` is a per-window `FlowBodyContent` source (the non-deep content the
    guard does not carry).

    Verified-but-unconsumed until the `locate`s are assembled: references no sorry site, frontier sorry
    count unchanged at 4.  `sorryAx`-free — pure guard folding plus the oracle, no structure lemma and no
    choice, so it audits to the minimal `[propext, Quot.sound]` exactly as the seq twin.  Demo
    `Tests/Reflections/JointOracleSeqIh.lean` (the `mapIhOfOracle` companion). -/
theorem recbody_joint_oracle_map_ih (tokens : Array (Positioned YamlToken))
    (lo0 hi0 lo hi : Nat) (h_lo0_lo : lo0 ≤ lo) (h_hi_hi0 : hi ≤ hi0)
    (oracle : ∀ lo' hi', hi' - lo' < hi - lo → RecBodyJointGuard tokens lo0 hi0 lo' hi' →
      (tokens[hi']!.val = .flowSequenceEnd → RecSeqBody ((tokens.toList.take hi').drop lo')) ∧
      (tokens[hi']!.val = .flowMappingEnd → RecMapBody ((tokens.toList.take hi').drop lo'))) :
    ∀ lo' hi', hi' - lo' < hi - lo → lo ≤ lo' → hi' ≤ hi →
      FlowBodyWindow tokens lo' hi' → FlowBodyContentDeepMap tokens lo' hi' →
      MapEnclosed tokens lo' → tokens[hi']!.val = .flowMappingEnd →
      RecMapBody ((tokens.toList.take hi').drop lo') := by
  intro lo' hi' h_span h_lo_lo' h_hi'_hi h_win h_deep h_encl h_mapEnd
  refine (oracle lo' hi' h_span ?_).2 h_mapEnd
  refine ⟨by omega, by omega, h_win, fun h_seqEnd => ?_, fun _ => ⟨h_deep, h_encl⟩, Or.inr h_mapEnd⟩
  rw [h_mapEnd] at h_seqEnd
  exact absurd h_seqEnd (by decide)

/-- **The SEQ `locate` for the joint navigator driver** — `(i'-b-B2c-desc-joint-locate-seq)`, Phase J:
    the FIRST of the two `locate` holes `recbody_joint_navigator_driver_carrier` (R534) takes as inputs,
    now ASSEMBLED from three landed bricks.  Given the root seq separator carrier
    `SeqInteriorSeparators tokens lo0 hi0`, this produces — at every seq-closing window the driver
    visits — the first-entry boundary `m` with its depth-`0` balance and a `RecSeqEntry` for the prefix,
    exactly the shape the driver's seq branch consumes (`obtain ⟨m, …, h_entry⟩ := locate_seq …`).

    **Nothing new is proved here — it is a three-brick WIRING** ([[ref-reduction-by-import]] /
    [[ref-consumer-joint-before-producer]] resolved):

    1. **Unpack `RecBodyJointGuard tokens lo0 hi0 lo hi`** (R533): the frame bounds `lo0 ≤ lo` / `hi ≤ hi0`,
       the shared `FlowBodyWindow tokens lo hi`, and — gated by the seq close `tokens[hi]!.val =
       .flowSequenceEnd` we are handed — the deep+enclosure half `FlowBodyContentDeepSeq ∧ SeqEnclosed`.
    2. **Source the per-window non-deep `FlowBodyContent`** the dispatch needs but the guard does NOT
       carry, via the landed `seqWindow_flowBodyContent_seq_general`: the guard's `FlowBodyWindow` /
       `FlowBodyContentDeepSeq` / `SeqEnclosed` plus the threaded root carrier narrowed to `[lo, hi)` by
       the guard's own frame bounds ([[ref-narrow-from-root-breaks-rederivation-cycle]]) — the brick the
       R536 next step named as the SOLE survivor, here discharged for the seq axis with no new lemma.
    3. **Supply the dispatch's seq-only `h_ih` from the joint `oracle`** via `recbody_joint_oracle_seq_ih`
       (R535): pick `Q := SeqEnclosed tokens`, and the adapter folds the joint guard and projects the
       seq side at every narrower window — path-AGNOSTIC where a carrier-only IH would restrict to the
       all-seq path.

    `recseqentry_window_dispatch_seq` (R527) then locates the first entry; its output is the driver's
    `locate_seq` shape modulo a pure RE-PACK — the dispatch carries an extra interior-minimality conjunct
    `(∀ k, …)` the driver drops, and orders `balance`/`marker` the other way ([[ref-mirror-reads-conjunct-not-projection]]
    at the existential level: read the conjuncts, re-tuple).  The off-axis `RecMapBody` the oracle also
    carries is untouched here — it flows to `locate_map`, the symmetric brick still to assemble.

    Verified-but-unconsumed until the driver is instantiated at the root `[2, size-2)` with this `locate_seq`,
    the symmetric `locate_map`, and the per-window M2 narrowing: composes only landed lemmas, references
    no sorry site, frontier sorry count unchanged at 4.  Inherits the dispatch's
    `[propext, Classical.choice, Quot.sound]` (the seq dispatch threads the choice-tainted classify; the
    oracle adapter is clean — [[ref-mirror-inherits-dependency-axioms]]). -/
theorem recbody_locate_seq_carrier (tokens : Array (Positioned YamlToken)) (lo0 hi0 : Nat)
    (h_seq_carrier : SeqInteriorSeparators tokens lo0 hi0) :
    ∀ lo hi, RecBodyJointGuard tokens lo0 hi0 lo hi →
      tokens[hi]!.val = .flowSequenceEnd →
      (∀ lo' hi', hi' - lo' < hi - lo → RecBodyJointGuard tokens lo0 hi0 lo' hi' →
        (tokens[hi']!.val = .flowSequenceEnd → RecSeqBody ((tokens.toList.take hi').drop lo')) ∧
        (tokens[hi']!.val = .flowMappingEnd → RecMapBody ((tokens.toList.take hi').drop lo'))) →
      ∃ m, lo < m ∧ m ≤ hi ∧
        (m = hi ∨ tokens[m]!.val = .flowEntry) ∧
        flowBracketBalance tokens lo m = 0 ∧
        RecSeqEntry ((tokens.toList.take m).drop lo) := by
  intro lo hi h_g h_seqEnd oracle
  obtain ⟨h_lo0_lo, h_hi_hi0, h_win, h_seqHalf, _h_mapHalf, _h_close⟩ := h_g
  obtain ⟨h_deep, h_enc⟩ := h_seqHalf h_seqEnd
  have h_lo_sz : lo < tokens.size := by
    have := h_win.lo_lt_hi; have := h_win.hi_lt; omega
  -- Brick (2): per-window non-deep `FlowBodyContent` from the carrier narrowed by the guard's frame bounds.
  have h_content : FlowBodyContent tokens lo hi :=
    seqWindow_flowBodyContent_seq_general tokens lo0 hi0 lo hi h_win h_deep h_enc
      h_seq_carrier h_lo0_lo h_hi_hi0
  -- Dispatch the first entry; the seq-only `h_ih` is the joint oracle projected to the seq side (R535).
  obtain ⟨m, h_lo_m, h_m_hi, h_bal_m, h_marker, _h_min, h_entry⟩ :=
    recseqentry_window_dispatch_seq tokens lo hi h_win h_deep h_content
      (SeqEnclosed tokens)
      (fun h_open => seqEnclosed_descend tokens lo h_enc h_lo_sz h_open)
      (recbody_joint_oracle_seq_ih tokens lo0 hi0 lo hi h_lo0_lo h_hi_hi0 oracle)
  -- Re-pack into the driver's `locate_seq` shape (drop minimality, swap balance/marker order).
  exact ⟨m, h_lo_m, h_m_hi, h_marker, h_bal_m, h_entry⟩

/-- **The root-span instance of `seqWindowRecSeqBody_seq_general`** — `lo0 := 2`, `hi0 := size-2`,
    bounds read off `FlowBodyWindow.lo_ge`/`hi_le`.  Signature-preserving so `seqWindowRecSeqBody_seq`'s
    consumers are untouched (ROUTE A, R445 — the parametric carrier rides the recursion via the
    containment exposed through `recseqentry_window_dispatch_seq`'s `h_ih`). -/
theorem seqWindowRecSeqBody_seq (tokens : Array (Positioned YamlToken))
    (h_root_carrier : SeqInteriorSeparators tokens 2 (tokens.size - 2))
    (lo hi : Nat)
    (h_win0 : FlowBodyWindow tokens lo hi) (h_deep0 : FlowBodyContentDeepSeq tokens lo hi)
    (h_enc0 : SeqEnclosed tokens lo) (h_close0 : tokens[hi]!.val = .flowSequenceEnd) :
    RecSeqBody ((tokens.toList.take hi).drop lo) :=
  seqWindowRecSeqBody_seq_general tokens 2 (tokens.size - 2) h_root_carrier lo hi
    h_win0 h_deep0 h_enc0 h_close0 h_win0.lo_ge h_win0.hi_le

/-- **The domain-restricted nested `RecSeqBody` provider** — `(i'-b-B2c-nested-project)`, the navigator
    R335–R337 set up, now LANDED.  At every body window `[lo, hi)` on the **all-seq PATH** domain
    (`SeqPathAllSeq tokens lo` — every enclosing frame from the root to `lo` a flow sequence `[`, R336's
    routing discriminator) that is a `FlowBodyWindow ∧ FlowBodyContentDeep` whose `hi` is the enclosing
    sequence's matching close, it produces the recursive interior `RecSeqBody`.

    **It is `seqWindowRecSeqBody` (R323) with `SeqEnclosed` supplied from the carried `SeqPathAllSeq`**
    — a one-line composition, settling the open (a)/(b) question of the 185th-revision map decisively in
    favour of **(a)**.  The deciding fact ([[ref-severed-edge-bounds-navigator-domain]] read in the
    PRODUCER direction): `seqWindowRecSeqBody` does NOT *navigate* the root `RecSeqBody` tree — it
    *produces* `RecSeqBody` fresh from the window guards, routing a `{`-headed first entry through
    `recseqentry_window_dispatch`'s NEAR-LEAF map oracle (`recseqentry_mapbracket_oracle`, interior
    `WellBracketed`, NO IH) to a `RecSeqEntry.map` LEAF.  So the severed edge that defeats *navigation*
    (R335 — a seq window buried in a `RecSeqEntry.map`'s `WellBracketed` is unreachable from the root
    tree) is never crossed by *production*: the producer stops AT the map opener, it never needs to
    re-enter it.  Because `RecSeqBody` is a `Prop` (proof-irrelevant), the freshly produced witness is
    as good as a navigated one — so the FOUR position-keyed arms (R331–R334) are an ALTERNATIVE driver,
    not a necessity; the existing `windowWidth_strongRecOn` driver already serves the whole domain.

    The `SeqPathAllSeq` hypothesis is therefore STRONGER than this provider's own need (it consumes only
    the `SeqEnclosed` TOP-projection, via `seqEnclosed_of_seqPathAllSeq`, R337's DOMINANCE lemma).  It is
    carried because it is the CONSUMER's routing discriminator (R336): `SeqEnclosed` alone (top-only)
    cannot tell an all-seq-path window from one whose path dips through a `{` — only the whole-stack
    `SeqPathAllSeq` can — and the consumer needs that distinction to route map-path windows to the
    separate flat provider.  This provider sits on the all-seq-path side of that partition; threading the
    domain through descent is `seqPathAllSeq_descend` (R337 PRESERVATION), the map edge's exclusion is
    `seqPathAllSeq_map_push_breaks` (R337 NEGATION).

    Verified-but-unconsumed until the consumer routes the partition (R225): composes only landed lemmas
    (`seqWindowRecSeqBody` + `seqEnclosed_of_seqPathAllSeq`), references no sorry site, frontier sorry
    count unchanged at 4; axiom-clean. -/
theorem rec_seq_body_nested_project (tokens : Array (Positioned YamlToken))
    (h_root_carrier : SeqInteriorSeparators tokens 2 (tokens.size - 2))
    (lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi) (h_deep : FlowBodyContentDeep tokens lo hi)
    (h_path : SeqPathAllSeq tokens lo) (h_close : tokens[hi]!.val = .flowSequenceEnd) :
    RecSeqBody ((tokens.toList.take hi).drop lo) :=
  seqWindowRecSeqBody tokens h_root_carrier lo hi h_win h_deep
    (seqEnclosed_of_seqPathAllSeq tokens lo h_path) h_close

/-- **`h_seq_rec` reduces to the ROOT CARRIER + a flat per-window facts provider** — R389, the
    de-risk's redirect rendered as code.  This is the EXACT `h_seq_rec` universal shape that
    `flowSubrangesOk_of_window_producers` / `seqLocator_of_window_recseqbody` consume (bracket guards
    only: `2 ≤ lo`, `lo < hi`, `hi ≤ size-2`, `hi < size`, `tokens[hi]! = .flowSequenceEnd`,
    `balance lo hi = 0`, `tokens[lo-1]! = .flowSequenceStart`), produced here directly from
    `seqWindowRecSeqBody` (R323) — NO forward locator, NO `SeqPathAllSeq`.

    **Why the whole-domain width driver, not the forward locator** ([[ref-locate-consumer-by-gate-strength]]
    sharpened to its limit).  `h_seq_rec` quantifies over EVERY nested seq window with the bracket
    guards, INCLUDING windows whose enclosing path dips through a `{` (a seq nested under a map,
    `[{a: [..]}]`).  The forward emission locator (R386–R388) is keyed on the all-seq-PATH gate
    `SeqPathAllSeq tokens (lo-1)`, which a map-path window FAILS — the de-risk's minimal pair confirms
    it on real scanned output (`[["1"], {"a": ["2"]}]`: the inner seq `[2]`'s opener stack is
    `[false, true]`, not all-`true`, yet it satisfies every `h_seq_rec` guard).  So the locator can
    NEVER be the sole `h_seq_rec` producer; the gate-strengthening bridge the blueprint queued
    (`h_seq_rec` guards ⟹ `SeqPathAllSeq`) is FALSE.  `seqWindowRecSeqBody` instead needs only the
    TOP-only `SeqEnclosed tokens lo` (the immediate frame is a seq `[`), which holds for ANY nested
    seq window via `enclosingMark_true_of_opener` — so it serves the WHOLE domain (R323's doc:
    "the existing `windowWidth_strongRecOn` driver already serves the whole domain"), and the forward
    locator is REDUNDANT for `h_seq_rec` (verified-but-unconsumed, off the critical path).

    **The reduction** ([[ref-reduction-by-import]] / [[ref-fold-consumer-chain-to-producer-contract]]):
    this retypes the seq half of the `FlowSubrangesOk` residual (`NonemptyStructure.lean:7502`) from
    "produce `RecSeqBody` at every window" to its two genuine sub-residuals — the ROOT CARRIER
    `SeqInteriorSeparators tokens 2 (size-2)` (= `seqRoot_seqInteriorSeparators` fed `desc`, whose
    residual is the width fixpoint `h_enc` via the backward `seqEnclosingOpener_of_gate` scan) and a
    FLAT per-window facts provider (`FlowBodyWindow ∧ FlowBodyContentDeep ∧ SeqEnclosed`, all
    restrictions of global emission facts — `dyck`/`wellTyped` via `WellTyped_subrange`, the
    content-start fields via the all-depth emission characterization, `SeqEnclosed` via
    `enclosingMark_true_of_opener`).  `windowFacts` is bundled to read the producer's contract off the
    `h_seq_rec` signature in one line.  Verified-but-unconsumed until the carrier and the provider land:
    composes only `seqWindowRecSeqBody`, references no sorry site, frontier sorry count unchanged at 4. -/
theorem seqRec_of_carrier_and_windowFacts (tokens : Array (Positioned YamlToken))
    (h_root_carrier : SeqInteriorSeparators tokens 2 (tokens.size - 2))
    (windowFacts : ∀ lo hi, 2 ≤ lo → lo < hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowSequenceEnd → flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowSequenceStart →
      FlowBodyWindow tokens lo hi ∧ FlowBodyContentDeep tokens lo hi ∧ SeqEnclosed tokens lo) :
    ∀ lo hi, 2 ≤ lo → lo < hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowSequenceEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowSequenceStart →
      RecSeqBody ((tokens.toList.take hi).drop lo) := by
  intro lo hi h2 hlt hhi hsz hclose hbal hopen
  obtain ⟨h_win, h_deep, h_enc⟩ := windowFacts lo hi h2 hlt hhi hsz hclose hbal hopen
  exact seqWindowRecSeqBody tokens h_root_carrier lo hi h_win h_deep h_enc hclose

/-- **Per-window assembler of the bracket + enclosure halves of the window-facts provider**
    (Phase J — R390, the (a) WINDOW-FACTS sub-residual carved off `seqRec_of_carrier_and_windowFacts`).
    R389 reduced `h_seq_rec` to the root carrier + a per-window provider
    `∀ lo hi, <seq guards> → FlowBodyWindow ∧ FlowBodyContentDeep ∧ SeqEnclosed`.  This brick discharges
    TWO of that provider's three conjuncts — `FlowBodyWindow` and `SeqEnclosed` — at EVERY seq window
    from facts that are pure RESTRICTIONS of the global emission invariants, isolating
    `FlowBodyContentDeep` as the sole genuine residual.

    The DE-RISK that motivated the split ([[ref-minimal-pair-extracts-the-gate]] /
    [[ref-probe-deferred-universal-before-producing]]): is the global content-start fact at the sorry
    site (`scanFiltered_emitSeq_nonempty_structure`, `NonemptyStructure.lean:7502`) stated ALL-DEPTH or
    DEPTH-0 only?  Reading the in-scope facts settled it — `h_content0` is the depth-`0` HEAD
    (`tokens[2]`) and `h_fe_pattern` is gated on `flowBracketBalance tokens 2 k = 0` (TOP-level
    separators only).  But `FlowBodyContentDeep`'s `openerContentStart`/`feContentStart` quantify over
    ALL `k ∈ [lo, hi)` with NO balance gate — they are all-depth.  So the content conjunct genuinely owes
    a deep characterization (every opener / separator at any nesting is followed by a content-start head),
    which the in-scope depth-`0` facts cannot supply.  This is the [[ref-incomplete-projection-still-factors]]
    verdict: the carrier covers the bracket + enclosure part, NAMES the residual (the deep content), and
    the names are the real owed primitives.

    The two covered conjuncts are restrictions, both genuinely derivable (not pass-throughs):
    * `FlowBodyWindow` — the frame bounds are arithmetic, `balanced` is the guard, `dyck` is the window
      floor `h_win_dyck` (the matched-pair-interior floor, a `flowBracketBalance_matching_close`-style
      fact, here a hypothesis), and `wellTyped` is `WellTyped_subrange` carrying the outer
      `[2, size-2)` `WellTyped` down to `[lo, hi)` given the same window balance + floor.
    * `SeqEnclosed` — `enclosingMark_true_of_opener` pushes `true` onto the (defined) pre-opener fold at
      `lo - 1`; the fold's DEFINEDNESS (`h_fold_pre`) is the only input and follows globally from
      `btFold_some_prefix` on the whole-stream fold ([[ref-prefix-gate-reconstructed-from-boundary]]).

    The two named hypotheses — `h_win_dyck` (window floor) and `h_fold_pre` (prefix fold defined) — are
    exactly the global-restriction primitives the eventual provider supplies once (whole-stream
    well-bracketedness gives both at every window); they are NOT the deep content, which stays the lone
    standalone residual.  Verified-but-unconsumed until the window-facts provider assembles all three:
    references no sorry site, frontier sorry count unchanged at 4. -/
theorem flowBodyWindow_and_seqEnclosed_of_facts
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo : 2 ≤ lo) (h_lo_hi : lo < hi) (h_hi : hi ≤ tokens.size - 2) (h_hi_sz : hi < tokens.size)
    (h_bal : flowBracketBalance tokens lo hi = 0)
    (h_open : tokens[lo - 1]!.val = .flowSequenceStart)
    (h_wt_outer : WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2))
    (h_win_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_fold_pre : ∃ s, btFold (some []) (tokens.toList.take (lo - 1)) = some s) :
    FlowBodyWindow tokens lo hi ∧ SeqEnclosed tokens lo := by
  refine ⟨⟨h_lo, h_lo_hi, h_hi, h_hi_sz, h_bal, h_win_dyck, ?_⟩, ?_⟩
  · -- wellTyped via the balanced-subrange transporter (window ⊆ outer [2, size-2)).
    exact WellTyped_subrange tokens 2 lo hi (tokens.size - 2) h_lo (Nat.le_of_lt h_lo_hi) h_hi
      (by omega) h_wt_outer h_bal h_win_dyck
  · -- SeqEnclosed: push `true` onto the (defined) pre-opener fold via the opener at `lo-1`.
    obtain ⟨s, h_pre⟩ := h_fold_pre
    have h_q : lo - 1 < tokens.size := by omega
    have h_enc := enclosingMark_true_of_opener tokens (lo - 1) h_q s h_pre h_open
    have h_eq : lo - 1 + 1 = lo := by omega
    rw [h_eq] at h_enc
    exact h_enc

/-- **The deep-content conjunct of the window-facts provider restricts from a SINGLE ROOT seed** —
    `(i'-b-B2c window-facts provider — the (a) deep content-start sub-residual, R391)`.  R390 carved the
    per-window provider `∀ lo hi, <gate> → FlowBodyWindow ∧ FlowBodyContentDeep ∧ SeqEnclosed` into two
    restriction conjuncts (`flowBodyWindow_and_seqEnclosed_of_facts`) and the lone genuine residual
    `FlowBodyContentDeep`.  Reading the consuming recursion settles what that residual costs:
    `seqWindowRecSeqBody` (R323) descends INTERNALLY (re-establishing the deep guard at each child via
    `flowBodyContentDeep_advance`/`_descend`), but `seqRec_of_carrier_and_windowFacts` calls `windowFacts`
    at EVERY gated window, so the provider owes `FlowBodyContentDeep tokens lo hi` at each.

    Crucially that is NOT a per-window deep induction — it is a pure RESTRICTION of a SINGLE ROOT instance
    `FlowBodyContentDeep tokens 2 (tokens.size - 2)` ([[ref-non-restriction-residual-root-seed]]: the
    all-depth, balance-FREE fields are a subset-restriction across the window, so seed the root once and
    restrict everywhere; only the position-`lo`-keyed head needs a one-line recovery):
    * `openerContentStart` / `feContentStart` over `[lo, hi) ⊆ [2, size-2)` — direct sub-universals of the
      root's (drop the window bounds via `omega`, the fields carry NO balance gate so nesting is irrelevant).
    * `headContentStart : isFlowContentStart tokens[lo]` — recovered from the root's `openerContentStart`
      at the opener `k = lo - 1` (the gate gives `tokens[lo-1]! = .flowSequenceStart`, `flowBracketDelta = 1`,
      and `(lo-1)+1 = lo < hi ≤ size-2`), with the degenerate `lo = 2` falling back to the root head itself.

    So the window-facts provider's LAST residual collapses from "an all-depth content fact at every window"
    to the SINGLE root seed `FlowBodyContentDeep tokens 2 (size-2)` (the genuine deep emission
    characterization, still owed — its `headContentStart` is the in-scope depth-`0` `h_content0`, but its
    all-depth opener/separator fields need an emitter induction).  Composes only the projection of
    `FlowBodyContentDeep` + `flowBracketDelta_flowSequenceStart`; references no sorry site, frontier sorry
    count unchanged at 4; axiom-clean. -/
theorem flowBodyContentDeep_window_of_root
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo : 2 ≤ lo) (h_lo_hi : lo < hi) (h_hi : hi ≤ tokens.size - 2)
    (h_open : tokens[lo - 1]!.val = .flowSequenceStart)
    (h_root : FlowBodyContentDeep tokens 2 (tokens.size - 2)) :
    FlowBodyContentDeep tokens lo hi := by
  obtain ⟨h_root_head, h_root_op, h_root_fe⟩ := h_root
  refine ⟨?_, ?_, ?_⟩
  · -- headContentStart: tokens[lo] is content-start.
    rcases Nat.eq_or_lt_of_le h_lo with h_eq | h_gt
    · -- lo = 2: the root head directly
      rw [← h_eq]; exact h_root_head
    · -- lo > 2 (lo ≥ 3): the root opener fact at k = lo - 1 (a flowSequenceStart, delta 1)
      have h_delta : flowBracketDelta tokens[lo - 1]!.val = 1 := by
        rw [h_open]; exact flowBracketDelta_flowSequenceStart
      have h := h_root_op (lo - 1) (by omega) (by omega) h_delta
      rwa [Nat.sub_add_cancel (by omega)] at h
  · -- openerContentStart: a restriction of the root's (all-depth, balance-free)
    intro k hk1 hk2 hdelta
    exact h_root_op k (by omega) (by omega) hdelta
  · -- feContentStart: a restriction of the root's
    intro k hk1 hk2 hfe
    exact h_root_fe k (by omega) (by omega) hfe

/-- **The deep-content ROOT SEED is FALSE on real emitter output** — R392, the de-risk
    `flowBodyContentDeep_window_of_root` (R391) queued, machine-checked.  R391 reduced the per-window
    `FlowBodyContentDeep` provider to the single root instance `FlowBodyContentDeep tokens 2 (size-2)`
    (`flowBodyContentDeep_window_of_root` restricts it to every gated window).  The queued next step was to
    PRODUCE that root seed by emitter induction.  Probing it FIRST ([[ref-probe-deferred-universal-before-producing]])
    shows it is **unprovable — the predicate is false on actual scanned output**, so the production path is
    a dead end and the recursion's deep guard must be re-scoped (see below).

    This theorem exhibits the witness within the host lemma's exact domain
    (`scanFiltered ("[" ++ emit.emitList items ++ "]")`, `items ≠ []`): for `items = [[]]` (a single
    EMPTY nested flow sequence — `emit.emitList [.sequence .flow #[]] = "[]"`, input `"[[]]"`), the scan is
    `streamStart, [, [, ], ], streamEnd` (size 6, body window `[2, 4)`).  The opener `[` at `k = 2`
    (`flowBracketDelta = 1`) has `tokens[3] = .flowSequenceEnd` at `k + 1 = 3 < 4 = hi`, so
    `openerContentStart` would force `isFlowContentStart .flowSequenceEnd` — false.

    **Three violation classes the #eval probe found** (this lemma machine-checks the first; the structure
    is the same):
    * EMPTY bracket — `[]` / `{}` puts the matching CLOSE right after the opener (`tokens[k+1]` is the
      closer, not content-start).  Refuted here on `[[]]`.
    * MAP opener — every `{` opener's successor is a `.key` token (`["a", {"x": "y"}]`: `{` at `k=4`,
      `.key` at `k=5`), so `openerContentStart` (which fires for `flowBracketDelta = 1`, i.e. `{` too)
      is false at EVERY non-empty map opener, independent of emptiness.
    * MAP separator — `feContentStart` is false inside nested maps: a map pair-separator `,` is followed
      by `.key` (`[{"a": "b", "c": "d"}]`: `,` at `k=7`, `.key` at `k=8`).

    **Why it stayed hidden — and the fix direction.**  `FlowBodyContentDeep`'s all-depth balance-FREE
    fields (R290's strengthening, which made `flowBodyContentDeep_descend`/`_advance` pure restrictions —
    the [[ref-converse-forward-invariant-asymmetry]] dividend) assume the WHOLE window obeys
    flow-SEQUENCE conventions (opener→content, separator→content).  But flow-MAP interiors break both
    (`{`→`.key`, `,`→`.key`, `[]`→`]`).  The fields are CONSUMED only at seq-context positions —
    non-empty `[` openers (`flowBodyContentDeep_descend`, which always has `k+1 < j`) and depth-`0` seq
    separators (`flowBodyContentDeep_advance`) — never inside the map LEAVES (`recseqentry_window_dispatch`
    routes `{`-entries to the near-leaf map oracle, NO descent).  The descend/advance/`window_of_root`
    lemmas only ever RESTRICT the fields, so the falsity (a `∀`-over-all-depths the producer must
    establish from scratch) never surfaced until this root probe — the "target you only project hides its
    own falsity" trap.  Sharper still: `recseqentry_window_dispatch` (doc lines 5872-5878) RELIES on the
    false `openerContentStart` to EXCLUDE the empty-bracket leaf, a case that is REAL — so the field is
    not merely unprovable, the consumer's empty-exclusion is unsound for real inputs.  The redesign:
    re-scope the deep guard to seq-context positions (the `SeqPathAllSeq` discriminator, R336, already
    separates seq-path from map-dipping positions), and make the dispatch HANDLE empty `[ ]`/`{ }` entries
    (route to `RecSeqEntry.seqEmpty` / empty-`map`) rather than exclude them.

    Machine-checked: `native_decide` on the concrete 6-token scan of `"[[]]"` (the input shown literally
    as the emitter form), then `openerContentStart` at `k = 2` contradicts `tokens[3] = .flowSequenceEnd`.
    A guard rail: it permanently refutes the "prove the root seed" path so it is not re-attempted.  Off
    the critical path (a refutation, consumed by nothing — `native_decide`'s `Lean.ofReduceBool` does not
    reach `universal_roundtrip`); frontier sorry count unchanged at 4. -/
theorem flowBodyContentDeep_root_seed_false
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered
        ("[" ++ emit.emitList [YamlValue.sequence .flow #[]] ++ "]") = .ok tokens) :
    ¬ FlowBodyContentDeep tokens 2 (tokens.size - 2) := by
  -- Concrete token facts, transported from the scan equation via native_decide on the Option image.
  have key : ∀ {α : Type} (g : Array (Positioned YamlToken) → α) (a : α),
      (Scanner.scanFiltered
          ("[" ++ emit.emitList [YamlValue.sequence .flow #[]] ++ "]")).toOption.map g = some a →
        g tokens = a := by
    intro α g a e; rw [h] at e; exact Option.some.inj e
  have h2 : tokens[2]!.val = .flowSequenceStart :=
    key (fun t => t[2]!.val) .flowSequenceStart (by native_decide)
  have h3 : tokens[3]!.val = .flowSequenceEnd :=
    key (fun t => t[3]!.val) .flowSequenceEnd (by native_decide)
  have hsz : tokens.size = 6 :=
    key (fun t => t.size) 6 (by native_decide)
  -- The opener at k = 2 has delta 1; openerContentStart would force content-start at 3 = `]`.
  intro hd
  have h_delta : flowBracketDelta tokens[2]!.val = 1 := by
    rw [h2]; exact flowBracketDelta_flowSequenceStart
  have h_cs : isFlowContentStart tokens[3]!.val :=
    hd.openerContentStart 2 (Nat.le_refl 2) (by omega) h_delta
  rw [h3] at h_cs
  simp [isFlowContentStart] at h_cs

/-- **The re-scoped opener field reaches into the MAP axis — it is NOT projectable from `RecSeqBody`** —
    R394, the de-risk of (i'-b-B2c-root-seed) before authoring the general root seed of the R393 guard
    `FlowBodyContentDeepSeq`.  R393 re-scoped `FlowBodyContentDeep` to the root-TRUE `FlowBodyContentDeepSeq`
    (opener keyed on `.flowSequenceStart` + `≠ ]`), keeping the field **all-depth/balance-free** so its
    descend/advance edges stay pure restrictions ([[ref-window-absolute-gate-subset-restriction]]).  The
    queued next step was to PRODUCE the root seed `FlowBodyContentDeepSeq tokens 2 (size-2)` by induction on
    the seq-side recursive deliverable `RecSeqBody` (`seqRoot_recseqbody` already produces it).  Probing
    that path FIRST ([[ref-probe-deferred-universal-before-producing]]) shows it is a **dead end for the
    opener field**: the all-depth opener quantifier reaches `.flowSequenceStart` openers that live strictly
    INSIDE flow-MAP interiors, and the ENTIRE seq-side family (`RecSeqBody`/`RecSeqEntry`/
    `EmitScansInFlowRecEntry`) bottoms out at `WellBracketed` for a map entry's interior
    (`RecSeqEntry.map`, `NonemptyStructure.lean:466-469`, stores only `WellBracketed interior` — no recursive
    content structure), so those openers' content-start successors are UNWITNESSED by `RecSeqBody`.

    This theorem exhibits the witness within the host lemma's exact domain
    (`scanFiltered ("[" ++ emit.emitList items ++ "]")`): for `items = [{a: [b]}]` (a single flow-MAP entry
    whose value is a nested flow seq), the scan is
    `streamStart, [, {, key, "a", value, [, "b", ], }, ], streamEnd` (size 12, body window `[2, 10)`).  The
    body's only entry is the MAP (`tokens[2] = .flowMappingStart`).  Its value `[b]` contributes a
    `.flowSequenceStart` at `k = 6` — strictly inside the map (`flowBracketBalance tokens 2 6 = 1`, NOT the
    depth-`0` the seq separator machinery sees) — with content successor `tokens[7] = .scalar "b"`.  So
    `openerContentStart` FIRES at `k = 6` (the conclusion `isFlowContentStart tokens[7]` is TRUE — the field
    is sound here), but `k = 6` sits in the `WellBracketed`-only interior of the lone `RecSeqEntry.map`, so
    no `RecSeqBody` value over `[2, 10)` records it.

    **The sharpening of R392.**  `flowBodyContentDeep_root_seed_false` noted the deep fields are *consumed*
    only at seq-context positions (the dispatch routes `{`-entries to the near-leaf map oracle with NO
    descent), and the re-scoped field is now TRUE everywhere (R393).  But PRODUCTION of the root seed must
    still establish the all-depth opener at EVERY opener in `[2, 10)`, including the map-interior one at
    `k = 6` — and the seq axis cannot supply it.  Meanwhile the only consumer of `openerContentStart`
    (`flowBodyContent_descend`: `h_deep.openerContentStart p (Nat.le_refl p) …`) reads it ONLY at the window
    HEAD `k = lo`, never at a map-interior opener — so the field's map-interior obligations are pure
    over-reach: true, unconsumed, and unproducible from the owning (seq) axis.  This is
    [[ref-conjunctive-consumer-gates-on-orthogonal-axis]] surfacing at the PRODUCER: a single-axis recursive
    deliverable cannot establish an all-depth fact that quantifies over the ORTHOGONAL axis's interiors,
    even when that fact is consumed only on its own axis.

    **The fix direction.**  Do NOT produce the opener field by `RecSeqBody` induction, and do NOT re-scope
    its DOMAIN to seq-context (that reintroduces depth/re-basing, [[ref-non-restriction-residual-root-seed]]).
    Source it as a GLOBAL emitter-output token-adjacency fact — "every `.flowSequenceStart` in `emit _` is
    followed by `]` or a content-start token" — provable by induction on the emitter (`emit`/`emitList`/
    `emitPairList`) UNIFORMLY across both axes, indifferent to seq-vs-map.  The field then stays all-depth
    (trivial restriction edges, R393) AND true everywhere AND producible, the two-axis tension dissolved by
    not routing production through either axis's recursive deliverable.

    Machine-checked: `native_decide` on the concrete 12-token scan of `[{a: [b]}]`; the asserted bundle
    (`tokens[6] = .flowSequenceStart` at `flowBracketBalance 2 6 = 1`, `tokens[7]` content-start) is the
    positive witness that the opener field reaches a non-seq-structural, non-depth-`0` opener.  A guard rail:
    it fences the "produce `openerContentStart` from `RecSeqBody`" path so it is not re-attempted.  Off the
    critical path (a witness consumed by nothing — `native_decide`'s `Lean.ofReduceBool` does not reach
    `universal_roundtrip`); frontier sorry count unchanged at 4. -/
theorem flowBodyContentDeepSeq_opener_reaches_map_interior
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered
        ("[" ++ emit.emitList
          [YamlValue.mapping .flow
            #[(YamlValue.scalar { content := "a", style := .plain },
               YamlValue.sequence .flow #[YamlValue.scalar { content := "b", style := .plain }])]]
        ++ "]") = .ok tokens) :
    tokens.size = 12 ∧
    tokens[2]!.val = .flowMappingStart ∧
    tokens[6]!.val = .flowSequenceStart ∧
    flowBracketBalance tokens 2 6 = 1 ∧
    tokens[7]!.val ≠ .flowSequenceEnd ∧
    isFlowContentStart tokens[7]!.val := by
  have key : ∀ {α : Type} (g : Array (Positioned YamlToken) → α) (a : α),
      (Scanner.scanFiltered
          ("[" ++ emit.emitList
            [YamlValue.mapping .flow
              #[(YamlValue.scalar { content := "a", style := .plain },
                 YamlValue.sequence .flow #[YamlValue.scalar { content := "b", style := .plain }])]]
          ++ "]")).toOption.map g = some a →
        g tokens = a := by
    intro α g a e; rw [h] at e; exact Option.some.inj e
  have hsz : tokens.size = 12 := key (fun t => t.size) 12 (by native_decide)
  have h2 : tokens[2]!.val = .flowMappingStart :=
    key (fun t => t[2]!.val) .flowMappingStart (by native_decide)
  have h6 : tokens[6]!.val = .flowSequenceStart :=
    key (fun t => t[6]!.val) .flowSequenceStart (by native_decide)
  have hbal : flowBracketBalance tokens 2 6 = 1 :=
    key (fun t => flowBracketBalance t 2 6) 1 (by native_decide)
  have h7 : tokens[7]!.val = .scalar "b" .doubleQuoted :=
    key (fun t => t[7]!.val) (.scalar "b" .doubleQuoted) (by native_decide)
  refine ⟨hsz, h2, h6, hbal, ?_, ?_⟩
  · rw [h7]; exact (by decide)
  · rw [h7]; exact Or.inl ⟨"b", .doubleQuoted, rfl⟩

/-- **The global opener-adjacency target predicate** — `(i'-b-B2c-global-opener-adjacency)`, R395.
    The exact fact the *redirected* root-seed producer must establish.  R394 found the seq-axis
    `RecSeqBody` route cannot: the all-depth `FlowBodyContentDeepSeq.openerContentStart` field reaches
    `.flowSequenceStart` openers strictly INSIDE flow-MAP interiors, where the whole seq-side family
    (`RecSeqBody`/`RecSeqEntry`/`EmitScansInFlowRecEntry`) bottoms out at `WellBracketed` (`RecSeqEntry.map`
    stores only `WellBracketed interior`; and even `RecMapBody`/`RecMapPair` bottom out there for a nested
    *mapping* interior).  So source the fact GLOBALLY instead: stated over the WHOLE filtered token stream
    (no window bound) and indifferent to which axis an opener sits in — every `.flowSequenceStart` with a
    non-close successor is followed by a content-start.  This is what a value-induction on
    `emit`/`emitList`/`emitPairList` naturally concludes (every `[` in `emit _` is emitted by some
    `emit (.sequence _ items)` and followed in the STRING by `emitList items` — `""` ⇒ `]`, or a content
    head — uniform across seq and map; cf. `Output/Emitter.lean:131-146`).  The all-depth window field
    `FlowBodyContentDeepSeq.openerContentStart` over `[2, size-2)` is a trivial subset restriction of this
    (`flowSeqOpenerAdj_window_of_global`). -/
def GlobalFlowSeqOpenerAdj (tokens : Array (Positioned YamlToken)) : Prop :=
  ∀ k, k + 1 < tokens.size →
    tokens[k]!.val = .flowSequenceStart →
    tokens[k+1]!.val ≠ .flowSequenceEnd →
    isFlowContentStart tokens[k+1]!.val

/-- **The window field is a trivial restriction of the global predicate** —
    `(i'-b-B2c-global-opener-adjacency-restrict)`, R395, the CONSUME-side half (LANDED).  Once the global
    producer delivers `GlobalFlowSeqOpenerAdj tokens`, the window-relative all-depth opener field (the
    shape of `FlowBodyContentDeepSeq.openerContentStart` over any `[lo, hi)` with `hi ≤ size`) follows by
    ONE `omega` bound step — the payoff of keeping the field all-depth: the restriction edge is pure
    subset narrowing ([[ref-window-absolute-gate-subset-restriction]]), no re-basing
    ([[ref-non-restriction-residual-root-seed]]).  Landing this isolates the residual to EXACTLY the
    global producer: the value-induction that establishes `GlobalFlowSeqOpenerAdj`.  References no sorry
    site; frontier sorry count unchanged at 4. -/
theorem flowSeqOpenerAdj_window_of_global
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h : GlobalFlowSeqOpenerAdj tokens) (h_hi : hi ≤ tokens.size) :
    ∀ k, lo ≤ k → k + 1 < hi →
      tokens[k]!.val = .flowSequenceStart →
      tokens[k+1]!.val ≠ .flowSequenceEnd →
      isFlowContentStart tokens[k+1]!.val := by
  intro k _ hkhi ho hne
  exact h k (by omega) ho hne

/-- **The global opener-adjacency predicate is SATISFIABLE and UNIFORM across both axes** —
    `(i'-b-B2c-global-opener-adjacency-probe)`, R395, the [[ref-probe-provider-satisfiable-before-assembler]]
    discipline applied to the redirected GLOBAL provider.  Before authoring the heavy value-induction
    producer of `GlobalFlowSeqOpenerAdj`, machine-check that the body fires NON-VACUOUSLY at the two
    `.flowSequenceStart` openers of the cross-axis witness `[{a: [b]}]` — at BOTH the seq-spine opener
    `k = 1` (successor `tokens[2] = .flowMappingStart`, a content-start via the map disjunct) AND the
    map-interior opener `k = 6` (`flowBracketBalance 2 6 = 1`, the `[` of `[b]` strictly inside the map;
    successor `tokens[7] = .scalar "b"`, content-start via the scalar disjunct).  ONE predicate body, both
    axes: exactly the uniformity the seq-only `RecSeqBody` route lacks
    (`flowBodyContentDeepSeq_opener_reaches_map_interior` shows the same `k = 6` opener is unwitnessed by
    the seq deliverable).  Confirms the provider is not vacuously true and the
    `flowSeqOpenerAdj_window_of_global` projection has a real inhabitant to consume.  Off the critical
    path; frontier sorry count unchanged at 4. -/
theorem globalFlowSeqOpenerAdj_fires_cross_axis
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered
        ("[" ++ emit.emitList
          [YamlValue.mapping .flow
            #[(YamlValue.scalar { content := "a", style := .plain },
               YamlValue.sequence .flow #[YamlValue.scalar { content := "b", style := .plain }])]]
        ++ "]") = .ok tokens) :
    (tokens[1]!.val = .flowSequenceStart ∧ tokens[2]!.val ≠ .flowSequenceEnd ∧
      isFlowContentStart tokens[2]!.val) ∧
    (tokens[6]!.val = .flowSequenceStart ∧ tokens[7]!.val ≠ .flowSequenceEnd ∧
      isFlowContentStart tokens[7]!.val) := by
  have key : ∀ {α : Type} (g : Array (Positioned YamlToken) → α) (a : α),
      (Scanner.scanFiltered
          ("[" ++ emit.emitList
            [YamlValue.mapping .flow
              #[(YamlValue.scalar { content := "a", style := .plain },
                 YamlValue.sequence .flow #[YamlValue.scalar { content := "b", style := .plain }])]]
          ++ "]")).toOption.map g = some a →
        g tokens = a := by
    intro α g a e; rw [h] at e; exact Option.some.inj e
  have h1 : tokens[1]!.val = .flowSequenceStart :=
    key (fun t => t[1]!.val) .flowSequenceStart (by native_decide)
  have h2 : tokens[2]!.val = .flowMappingStart :=
    key (fun t => t[2]!.val) .flowMappingStart (by native_decide)
  have h6 : tokens[6]!.val = .flowSequenceStart :=
    key (fun t => t[6]!.val) .flowSequenceStart (by native_decide)
  have h7 : tokens[7]!.val = .scalar "b" .doubleQuoted :=
    key (fun t => t[7]!.val) (.scalar "b" .doubleQuoted) (by native_decide)
  refine ⟨⟨h1, ?_, ?_⟩, ⟨h6, ?_, ?_⟩⟩
  · rw [h2]; exact (by decide)
  · rw [h2]; exact Or.inr (Or.inr rfl)
  · rw [h7]; exact (by decide)
  · rw [h7]; exact Or.inl ⟨"b", .doubleQuoted, rfl⟩

/-- **The PRODUCE-side joint — the global opener contract reduces to the BODY-window field plus the
    structure's boundary facts** — `(i'-b-B2c-global-opener-adjacency-assemble)`, R396, the consumer joint
    of the redirected GLOBAL producer ([[ref-consumer-joint-before-producer]]).  R395 named the contract
    `GlobalFlowSeqOpenerAdj` and landed the CONSUME-side half (`flowSeqOpenerAdj_window_of_global`,
    global → any window).  This is the dual PRODUCE-side reduction: it shows the global obligation factors
    into (i) the four boundary facts the structure lemma `scanFiltered_emitSeq_nonempty_structure`
    ALREADY delivers — `size ≥ 5`, `tokens[0] = .streamStart`, `tokens[size-2] = .flowSequenceEnd`, and the
    body HEAD content-start `isFlowContentStart tokens[2]` — and (ii) one flat all-depth opener field over
    the BODY window `[2, size-2)` (precisely the shape of `flowSeqOpenerAdj_window_of_global tokens 2
    (size-2)`).  Landing this ISOLATES the producer's true residual to exactly the body field: every outer
    boundary (the `k=0` `.streamStart`, the `k=1` outer opener whose successor is the head, the
    `k=size-2` outer close) is discharged HERE by the structure facts, so the value-induction producer
    need only establish the opener adjacency of the scanned `emitList items` body — the recursive emitter
    object that `emitList_body_filtered_characterization` / the `SafeBody` block already scans (the
    de-risk's verdict: the NON-indexed body producer is the home, NOT the indexed `EmitScansInFlowIx`,
    whose `IxToken`/`ScannerStateIx` substrate would need a bridge back).

    The five-way case split on `k` (over `getElem!`, so no proof-carrying indices): `k=0` contradicts
    `.streamStart ≠ .flowSequenceStart`; `k=1` is the head fact (`1+1` reduces to `2`); `2 ≤ k` with
    `k+1 < size-2` is the body field; `k+1 = size-2` contradicts the `≠ .flowSequenceEnd` premise via the
    close; `k=size-2` contradicts `.flowSequenceEnd ≠ .flowSequenceStart`.  References no sorry site;
    frontier sorry count unchanged at 4. -/
theorem globalFlowSeqOpenerAdj_of_structure
    (tokens : Array (Positioned YamlToken))
    (h_sz : 5 ≤ tokens.size)
    (h_t0 : tokens[0]!.val = .streamStart)
    (h_close : tokens[tokens.size - 2]!.val = .flowSequenceEnd)
    (h_head : isFlowContentStart tokens[2]!.val)
    (h_body : ∀ k, 2 ≤ k → k + 1 < tokens.size - 2 →
        tokens[k]!.val = .flowSequenceStart →
        tokens[k+1]!.val ≠ .flowSequenceEnd →
        isFlowContentStart tokens[k+1]!.val) :
    GlobalFlowSeqOpenerAdj tokens := by
  intro k hk1 hopen hne
  by_cases h0 : k = 0
  · subst h0; rw [h_t0] at hopen; exact absurd hopen (by decide)
  by_cases h1 : k = 1
  · subst h1; exact h_head
  have hk2 : 2 ≤ k := by omega
  by_cases hb : k + 1 < tokens.size - 2
  · exact h_body k hk2 hb hopen hne
  by_cases hb2 : k + 1 = tokens.size - 2
  · rw [hb2] at hne; exact absurd h_close hne
  have hk_eq : k = tokens.size - 2 := by omega
  rw [hk_eq] at hopen
  rw [h_close] at hopen
  exact absurd hopen (by decide)

/-- **The SEQ (c)-PRODUCE-GLOBAL half — `GlobalFlowSeqOpenerAdj tokens` from the seq structure lemma** —
    `(i'-b-B2c-(c)-produce-global-seq)`, R409.  R408 (step (c) EXPOSE) made
    `scanFiltered_emitSeq_nonempty_structure` OUTPUT the all-depth `.flowSequenceStart`-opener field over
    the body window `[2, size-2)` as its twelfth conclusion conjunct.  This is the downstream CONSUME half
    the import edge forced into a separate module ([[ref-carry-up-splits-at-import-edge]]): the structure
    lemma lives in `NonemptyStructure` but the global producer `globalFlowSeqOpenerAdj_of_structure`
    (R396) lives HERE in `SeqInteriorSeparators` (which imports it), so `GlobalFlowSeqOpenerAdj` could not
    be produced inside the consumer; it is produced one level down, feeding the producer exactly the four
    boundary facts the structure lemma already exposes (`size ≥ 5`, `tokens[0] = .streamStart`,
    `tokens[size-2] = .flowSequenceEnd`, the body-HEAD content-start `isFlowContentStart tokens[2]`) plus
    the newly-exposed body opener field.  A near one-liner — destructure the twelve-conjunct conclusion,
    apply the landed producer.  The MAP axis is NOT a free mirror (`globalFlowSeqOpenerAdj_of_structure`
    end-keys its `k+1 = size-2` boundary on the seq close `.flowSequenceEnd`, but the map close is
    `.flowMappingEnd` — that boundary's `hopen` premise is instead vacuously false, sourced from the map
    body structure), so it gets a sibling next.  Verified-but-unconsumed until the (d)–(e)
    `FlowSubrangesOk` rewire feeds it through `flowSeqOpenerAdj_window_of_global`; references no sorry
    site, frontier sorry count unchanged at 4. -/
theorem seqGlobalFlowSeqOpenerAdj_of_emit
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w) :
    GlobalFlowSeqOpenerAdj tokens := by
  obtain ⟨h_sz5, h_t0, _h_tend, _h_t1, h_close, h_head, _h_fe_pattern,
          _h_outer_bal, _h_dyck, _h_wt_interior, h_body_opener, _h_body_separator⟩ :=
    scanFiltered_emitSeq_nonempty_structure items tokens h_scan h_ne h_all_block
  exact globalFlowSeqOpenerAdj_of_structure tokens (by omega) h_t0 h_close h_head h_body_opener

/-- **The MAP-axis global opener producer — the predicted NON-mirror sibling of
    `globalFlowSeqOpenerAdj_of_structure`** — `(i'-b-B2c-(c)-produce-global-map-structure)`, R410.  The
    seq producer (R396) discharged its `k+1 = size-2` boundary the cheap way: there the close token is
    the seq close `.flowSequenceEnd`, so the `≠ .flowSequenceEnd` premise `hne` is itself
    contradictory and the case closes with one `absurd h_close hne`, with NO appeal to the body
    structure.  On the MAP axis the close is `.flowMappingEnd`, so `hne` is genuinely SATISFIED at that
    boundary and the cheap discharge is unavailable; the case instead reasons that the pre-close body
    token at `k = size-3` (the one whose successor IS the close) is never a `.flowSequenceStart` opener.
    That is sourced from the map body's BRACKET STRUCTURE — the balance-0 conjunct `h_outer_bal` and the
    Dyck conjunct `h_dyck` the structure lemma already carries — exactly as
    [[ref-boundary-residual-end-dual]] anticipates: the boundary fact discharges VACUOUSLY by refuting
    its `hopen` premise, but the refutation is END-keyed on the enclosing close, so it needs the floor
    invariant the interior body field does not carry.  The one-step balance recurrence
    `balance 2 (k+1) = balance 2 k + flowBracketDelta tokens[k]!.val` (the inline analogue of
    `flowBracketBalance_matching_close`'s `step`): if `tokens[k] = .flowSequenceStart` its delta is `+1`,
    and since `k+1 = size-2` pins `balance 2 (k+1) = 0` (`h_outer_bal`), the prefix balance would be
    `-1`, contradicting `h_dyck`'s `≥ 0`.  The `k=1` case is the MIRROR simplification — the seq's
    `tokens[1] = .flowSequenceStart` made `k=1` the REAL head case (producing the head content-start),
    but the map's `tokens[1] = .flowMappingStart` makes `hopen` contradictory there, so `k=1` is
    VACUOUS for the map ([[ref-near-leaf-mirror-sheds-machinery]]: the storage asymmetry flips sign
    across the boundary — the map sheds the head-content hypothesis the seq needed but pays the
    balance/Dyck pair the seq did not).  References no sorry site; frontier sorry count unchanged at 4. -/
theorem globalFlowSeqOpenerAdj_of_map_structure
    (tokens : Array (Positioned YamlToken))
    (h_sz : 5 ≤ tokens.size)
    (h_t0 : tokens[0]!.val = .streamStart)
    (h_t1 : tokens[1]!.val = .flowMappingStart)
    (h_close : tokens[tokens.size - 2]!.val = .flowMappingEnd)
    (h_outer_bal : flowBracketBalance tokens 2 (tokens.size - 2) = 0)
    (h_dyck : ∀ k, 2 ≤ k → k ≤ tokens.size - 2 → flowBracketBalance tokens 2 k ≥ 0)
    (h_body : ∀ k, 2 ≤ k → k + 1 < tokens.size - 2 →
        tokens[k]!.val = .flowSequenceStart →
        tokens[k+1]!.val ≠ .flowSequenceEnd →
        isFlowContentStart tokens[k+1]!.val) :
    GlobalFlowSeqOpenerAdj tokens := by
  intro k hk1 hopen hne
  by_cases h0 : k = 0
  · subst h0; rw [h_t0] at hopen; exact absurd hopen (by decide)
  by_cases h1 : k = 1
  · subst h1; rw [h_t1] at hopen; exact absurd hopen (by decide)
  have hk2 : 2 ≤ k := by omega
  by_cases hb : k + 1 < tokens.size - 2
  · exact h_body k hk2 hb hopen hne
  by_cases hb2 : k + 1 = tokens.size - 2
  · -- The genuine map difference: the pre-close body token at `k = size-3` cannot be an opener,
    -- else the prefix balance would be `-1`, contradicting the Dyck floor.
    exfalso
    have h_k_sz : k < tokens.size := by omega
    have hstep : flowBracketBalance tokens 2 (k+1) =
        flowBracketBalance tokens 2 k + flowBracketDelta tokens[k]!.val := by
      rw [flowBracketBalance_compose tokens 2 k (k+1) (by omega) (by omega)]
      have hlen : k < tokens.toList.length := by rw [Array.length_toList]; exact h_k_sz
      rw [flowBracketBalance_single tokens k hlen]
      have h1' : tokens.toList[k]'hlen = tokens[k] := Array.getElem_toList h_k_sz
      have h2' : tokens[k] = tokens[k]! := (getElem!_pos tokens k h_k_sz).symm
      rw [h1', h2']
    have h_delta : flowBracketDelta tokens[k]!.val = 1 := by
      rw [hopen]; exact flowBracketDelta_flowSequenceStart
    rw [hb2, h_outer_bal, h_delta] at hstep
    have hge := h_dyck k hk2 (by omega)
    omega
  · -- k = size-2: `tokens[size-2] = .flowMappingEnd ≠ .flowSequenceStart`, `hopen` is absurd.
    have hk_eq : k = tokens.size - 2 := by omega
    rw [hk_eq] at hopen
    rw [h_close] at hopen
    exact absurd hopen (by decide)

/-- **The MAP (c)-PRODUCE-GLOBAL half — `GlobalFlowSeqOpenerAdj tokens` from the map structure lemma** —
    `(i'-b-B2c-(c)-produce-global-map)`, R410.  Mirrors `seqGlobalFlowSeqOpenerAdj_of_emit` (R409): the
    downstream CONSUME of `scanFiltered_emitMap_nonempty_structure`'s twelve-conjunct conclusion, feeding
    the map-axis producer the facts the structure lemma already carries — `tokens[0] = .streamStart`,
    `tokens[1] = .flowMappingStart`, the map close `tokens[size-2] = .flowMappingEnd`, the balance-0 +
    Dyck pair, and the newly-exposed (R408) body opener field over `[2, size-2)`.  Unlike the SEQ
    consume this is NOT a one-liner only because the producer is the non-mirror sibling
    (`globalFlowSeqOpenerAdj_of_map_structure`, not the seq producer) — `mkG`'s contract is genuinely
    axis-specific ([[ref-carry-up-splits-at-import-edge]] consume-half tell), so the structure lemma's
    conclusion is a subset of the MAP producer's contract (balance-0/Dyck), not the seq producer's.
    Verified-but-unconsumed until the (d)–(e) `FlowSubrangesOk` rewire; frontier sorry count unchanged
    at 4. -/
theorem mapGlobalFlowSeqOpenerAdj_of_emit
    (pairs : Array (YamlValue × YamlValue)) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}") = .ok tokens)
    (h_ne : pairs.toList ≠ [])
    (h_all_k_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowSavedKeyBlock p.1)
    (h_all_v_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowBlock p.2) :
    GlobalFlowSeqOpenerAdj tokens := by
  obtain ⟨h_sz7, h_t0, _h_tend, h_t1, h_close, _h_key, _h_fe_pattern,
          h_outer_bal, h_dyck, _h_wt_interior, _h_pnok, h_body_opener, _h_body_separator⟩ :=
    scanFiltered_emitMap_nonempty_structure pairs tokens h_scan h_ne h_all_k_block h_all_v_block
  exact globalFlowSeqOpenerAdj_of_map_structure tokens (by omega) h_t0 h_t1 h_close
    h_outer_bal h_dyck h_body_opener

/-- **The per-window opener-adjacency provider, SEQ emit source** —
    `(i'-b-B2c-(d)-window-opener-adjacency-seq)`, R411, the SMALLEST-FIRST step of the (d)–(e)
    `FlowSubrangesOk` rewire: confirm the global → window feed typechecks END-TO-END from emission before
    assembling `flowSubrangesOk_of_window_producers`.  It chains the two landed halves of the import-edge
    carry-up — `seqGlobalFlowSeqOpenerAdj_of_emit` (R409, the downstream CONSUME that produces
    `GlobalFlowSeqOpenerAdj tokens` from a scanned top-level seq) and `flowSeqOpenerAdj_window_of_global`
    (R395, the trivial restriction of the global predicate to any window `[lo, hi)` with `hi ≤ size`) —
    into a single per-window provider keyed exactly on a `FlowSubrangesOk.seq` sub-window's shape: at any
    `[lo, hi)` with `hi ≤ tokens.size`, the all-depth `.flowSequenceStart`-opener field holds (every flow
    sequence opener at depth-blind `k ∈ [lo, hi)` is followed by a content-start unless by `]`).  The
    `hi ≤ size` premise is weaker than the `FlowSubrangesOk.seq` guard's `hi < size`, so it discharges by
    `Nat.le_of_lt` at the call site.  Verified-but-unconsumed until the gate-strengthening bridge feeds
    this into the per-window `Rec…Body` producers; references no sorry site, frontier sorry count
    unchanged at 4. -/
theorem seqWindowOpenerAdj_of_emit
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w)
    (h_hi : hi ≤ tokens.size) :
    ∀ k, lo ≤ k → k + 1 < hi →
      tokens[k]!.val = .flowSequenceStart →
      tokens[k+1]!.val ≠ .flowSequenceEnd →
      isFlowContentStart tokens[k+1]!.val :=
  flowSeqOpenerAdj_window_of_global tokens lo hi
    (seqGlobalFlowSeqOpenerAdj_of_emit items tokens h_scan h_ne h_all_block) h_hi

/-- **The per-window opener-adjacency provider, MAP emit source** —
    `(i'-b-B2c-(d)-window-opener-adjacency-map)`, R411, the orthogonal-axis mirror of
    `seqWindowOpenerAdj_of_emit` ([[ref-conjunctive-consumer-gates-on-orthogonal-axis]]: the two axes are
    INDEPENDENT obligations — a top-level map nests seqs and vice versa, so (d) must feed the opener
    adjacency on BOTH).  The SAME window field, but sourced from a scanned top-level MAP via
    `mapGlobalFlowSeqOpenerAdj_of_emit` (R410, the non-mirror sibling producer).  This is the
    [[ref-coerce-to-weaker-reuse-wrapper]] payoff of keeping the global predicate AXIS-UNIFORM: ONE
    `GlobalFlowSeqOpenerAdj` shape, ONE restriction lemma `flowSeqOpenerAdj_window_of_global`, fed from
    EITHER emit source — the conjunctive consumer's two orthogonal conjuncts consume the same per-window
    deliverable, differing only in which emit wrapper produced the global fact.  Verified-but-unconsumed;
    references no sorry site, frontier sorry count unchanged at 4. -/
theorem mapWindowOpenerAdj_of_emit
    (pairs : Array (YamlValue × YamlValue)) (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_scan : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}") = .ok tokens)
    (h_ne : pairs.toList ≠ [])
    (h_all_k_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowSavedKeyBlock p.1)
    (h_all_v_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowBlock p.2)
    (h_hi : hi ≤ tokens.size) :
    ∀ k, lo ≤ k → k + 1 < hi →
      tokens[k]!.val = .flowSequenceStart →
      tokens[k+1]!.val ≠ .flowSequenceEnd →
      isFlowContentStart tokens[k+1]!.val :=
  flowSeqOpenerAdj_window_of_global tokens lo hi
    (mapGlobalFlowSeqOpenerAdj_of_emit pairs tokens h_scan h_ne h_all_k_block h_all_v_block) h_hi

/-- **The GLOBAL separator-adjacency predicate — the `.flowEntry` mirror of `GlobalFlowSeqOpenerAdj`** —
    `(i'-b-B2c-(d)-seq-rec-producer (R3) global-separator-adjacency)`, R417, the structure-level fact that
    will source `FlowBodyContentDeepSeq.feContentStart` per window — the missing THIRD per-window field the
    R416 (R2) consumer re-thread left owed ([[ref-conjunctive-consumer-gates-on-orthogonal-axis]]: of the
    re-scoped guard's three fields, `openerContentStart` is sourced by R411's `seqWindowOpenerAdj_of_emit`,
    `headContentStart` reduces from the global opener at `k = lo-1`, and THIS — the separator field — needs
    a parallel new global fact).  Where `GlobalFlowSeqOpenerAdj` says every `.flowSequenceStart` opener with
    a non-close successor is followed by a content-start, this says every `.flowEntry` SEPARATOR whose
    successor is `≠ .key` is followed by a content-start.  The `≠ .key` gate is the separator analogue of the
    opener's `≠ .flowSequenceEnd`: it excludes the MAP-internal `,`, whose successor IS a `.key` (a flow-map
    entry `c: d` after a comma emits the key token, not seq content), leaving exactly the SEQ-context
    separators — every `,` between flow-sequence elements is followed by the next element's content head
    (scalar / `[` / `{`).  Axis-blind and window-free like its opener sibling
    ([[ref-window-absolute-gate-subset-restriction]]): the gate is keyed only on `tokens[k]`/`tokens[k+1]`,
    never the origin, so the all-depth window field `FlowBodyContentDeepSeq.feContentStart` over any
    `[lo, hi)` is a trivial subset restriction (`flowSeqSepAdj_window_of_global`). -/
def GlobalFlowSeqSepAdj (tokens : Array (Positioned YamlToken)) : Prop :=
  ∀ k, k + 1 < tokens.size →
    tokens[k]!.val = .flowEntry →
    tokens[k+1]!.val ≠ .key →
    isFlowContentStart tokens[k+1]!.val

/-- **The window field is a trivial restriction of the global separator predicate** —
    `(i'-b-B2c-(d)-seq-separator-adjacency-restrict)`, R417, the CONSUME-side half (the "structure-expose"
    that lets a consumer read the field off the global at any window), mirror of
    `flowSeqOpenerAdj_window_of_global` (R395).  Once the global producer delivers `GlobalFlowSeqSepAdj
    tokens`, the window-relative all-depth separator field (the shape of
    `FlowBodyContentDeepSeq.feContentStart` over any `[lo, hi)` with `hi ≤ size`) follows by ONE `omega`
    bound step — the payoff of the all-depth, balance-FREE formulation: the restriction edge is pure subset
    narrowing, no re-basing ([[ref-window-absolute-gate-subset-restriction]]).  Landing this isolates the
    residual to EXACTLY the global producer (the value-induction that establishes `GlobalFlowSeqSepAdj`).
    References no sorry site; frontier sorry count unchanged at 4. -/
theorem flowSeqSepAdj_window_of_global
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h : GlobalFlowSeqSepAdj tokens) (h_hi : hi ≤ tokens.size) :
    ∀ k, lo ≤ k → k + 1 < hi →
      tokens[k]!.val = .flowEntry →
      tokens[k+1]!.val ≠ .key →
      isFlowContentStart tokens[k+1]!.val := by
  intro k _ hkhi hfe hne
  exact h k (by omega) hfe hne

/-- **The global separator-adjacency predicate is SATISFIABLE — the body fires NON-VACUOUSLY at a real
    seq separator** — `(i'-b-B2c-(d)-seq-separator-adjacency-probe)`, R417, the
    [[ref-probe-provider-satisfiable-before-assembler]] discipline applied to the new GLOBAL separator
    provider before authoring its (heavier) value-induction producer.  On the two-element flow sequence
    `["a", "b"]` the body fires at the `.flowEntry` separator `k = 3`: its successor `tokens[4] = .scalar
    "b"` is `≠ .key` and a content-start (the scalar disjunct).  Confirms `GlobalFlowSeqSepAdj` is not
    vacuously true and the `flowSeqSepAdj_window_of_global` projection has a real inhabitant to consume — the
    positive mirror of the gate's purpose (the `≠ .key` premise that excludes the map-internal `,` is
    SATISFIED here, where the separator genuinely precedes seq content).  Off the critical path; frontier
    sorry count unchanged at 4. -/
theorem globalFlowSeqSepAdj_fires
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered
        ("[" ++ emit.emitList
          [YamlValue.scalar { content := "a", style := .plain },
           YamlValue.scalar { content := "b", style := .plain }]
        ++ "]") = .ok tokens) :
    tokens[3]!.val = .flowEntry ∧ tokens[4]!.val ≠ .key ∧
      isFlowContentStart tokens[4]!.val := by
  have key : ∀ {α : Type} (g : Array (Positioned YamlToken) → α) (a : α),
      (Scanner.scanFiltered
          ("[" ++ emit.emitList
            [YamlValue.scalar { content := "a", style := .plain },
             YamlValue.scalar { content := "b", style := .plain }]
          ++ "]")).toOption.map g = some a →
        g tokens = a := by
    intro α g a e; rw [h] at e; exact Option.some.inj e
  have h3 : tokens[3]!.val = .flowEntry :=
    key (fun t => t[3]!.val) .flowEntry (by native_decide)
  have h4 : tokens[4]!.val = .scalar "b" .doubleQuoted :=
    key (fun t => t[4]!.val) (.scalar "b" .doubleQuoted) (by native_decide)
  refine ⟨h3, ?_, ?_⟩
  · rw [h4]; exact (by decide)
  · rw [h4]; exact Or.inl ⟨"b", .doubleQuoted, rfl⟩

/-- **The PRODUCE-side joint — the global separator contract reduces to the BODY-window separator field
    plus the structure's boundary facts AND a no-trailing-separator boundary input** —
    `(i'-b-B2c-(d)-seq-separator-adjacency-assemble)`, R418, the produce-side joint of the new GLOBAL
    separator producer, mirror of `globalFlowSeqOpenerAdj_of_structure` (R396) for the `.flowEntry`
    trigger / `≠ .key` gate.  It factors `GlobalFlowSeqSepAdj tokens` into the boundary facts the
    structure lemma `scanFiltered_emitSeq_nonempty_structure` already delivers — `size ≥ 5`,
    `tokens[0] = .streamStart`, `tokens[1] = .flowSequenceStart`, the close
    `tokens[size-2] = .flowSequenceEnd` — plus (i) one flat all-depth SEPARATOR field over the body window
    `[2, size-2)` (the shape of `flowSeqSepAdj_window_of_global tokens 2 (size-2)`, the R417 restriction's
    interior) and (ii) ONE new boundary input the opener producer did NOT need: the pre-close token is a
    non-separator (`tokens[size-3] ≠ .flowEntry`).

    **Why the boundary case is NOT a free mirror (the genuine R418 difference).** The five-way `k`-split
    over `getElem!` reuses the opener producer's skeleton, but the `k+1 = size-2` (pre-close) cell
    discharges by a THIRD strategy neither opener sibling used, because the boundary discharge is selected
    by TWO axes the trigger token does NOT determine ([[ref-boundary-discharge-gate-trigger-typed]]):

    * **Does the gate exclude the close?** The seq OPENER producer (R396) gate is `≠ .flowSequenceEnd`,
      and the close IS `.flowSequenceEnd`, so its boundary `hne` premise is self-contradictory and the
      cell closes with a single `absurd h_close hne` — no structural fact at all.  The separator gate
      `≠ .key` does NOT exclude the close (`.flowSequenceEnd ≠ .key`), so that cheap discharge is gone:
      `hne` is genuinely SATISFIED at the pre-close.
    * **Is the trigger a balance-changer?** The MAP opener producer (R410), facing a close its gate also
      admits (`.flowMappingEnd ≠ .flowSequenceEnd`), refuted its pre-close opener by the Dyck FLOOR — an
      opener has bracket-delta `+1`, so a pre-close opener forces prefix balance `-1`, contradicting
      `h_dyck`.  A `.flowEntry` separator has bracket-delta `0` ([[ref-boundary-residual-end-dual]]): it
      moves no balance, so the Dyck-floor refutation is UNAVAILABLE too.

    Both opener discharges fail, so the separator's pre-close cell needs a genuinely new input — that the
    emitter writes NO trailing separator before the close, i.e. `tokens[size-3]` is a non-`.flowEntry`.
    Here that is taken as a HYPOTHESIS / named residual ([[ref-incomplete-projection-still-factors]]: name
    the data the boundary cannot otherwise see), keeping the joint a clean reduction; its sourcing is a
    SEPARATE later brick — the `SeqInteriorSeparators` carrier's `noTrailingSepFact tokens 2 (size-2)`
    (R416) refutes a pre-close `.flowEntry` via its false content-start conclusion at the close, given
    `flowBracketBalance tokens 2 (size-3) = 0`, or a freshly-exposed structure field supplies it directly.

    The five cells: `k=0` contradicts `.streamStart ≠ .flowEntry`; `k=1` contradicts the seq opener
    `.flowSequenceStart ≠ .flowEntry` (VACUOUS — unlike the opener producer where `k=1` was the real head
    case, the seq head is the OPENER, never a separator); `2 ≤ k` with `k+1 < size-2` is the body field;
    `k+1 = size-2` is the new no-trailing-separator boundary; `k=size-2` contradicts
    `.flowSequenceEnd ≠ .flowEntry`.  References no sorry site; frontier sorry count unchanged at 4. -/
theorem globalFlowSeqSepAdj_of_structure
    (tokens : Array (Positioned YamlToken))
    (h_sz : 5 ≤ tokens.size)
    (h_t0 : tokens[0]!.val = .streamStart)
    (h_t1 : tokens[1]!.val = .flowSequenceStart)
    (h_close : tokens[tokens.size - 2]!.val = .flowSequenceEnd)
    (h_no_trailing_sep : tokens[tokens.size - 3]!.val ≠ .flowEntry)
    (h_body : ∀ k, 2 ≤ k → k + 1 < tokens.size - 2 →
        tokens[k]!.val = .flowEntry →
        tokens[k+1]!.val ≠ .key →
        isFlowContentStart tokens[k+1]!.val) :
    GlobalFlowSeqSepAdj tokens := by
  intro k hk1 hfe hne
  by_cases h0 : k = 0
  · subst h0; rw [h_t0] at hfe; exact absurd hfe (by decide)
  by_cases h1 : k = 1
  · subst h1; rw [h_t1] at hfe; exact absurd hfe (by decide)
  have hk2 : 2 ≤ k := by omega
  by_cases hb : k + 1 < tokens.size - 2
  · exact h_body k hk2 hb hfe hne
  by_cases hb2 : k + 1 = tokens.size - 2
  · -- The genuine separator difference: the gate `≠ .key` does NOT exclude the close, and `.flowEntry`
    -- is balance-neutral, so neither opener discharge applies; refute the pre-close `.flowEntry` directly.
    have hk_eq : k = tokens.size - 3 := by omega
    rw [hk_eq] at hfe
    exact absurd hfe h_no_trailing_sep
  have hk_eq : k = tokens.size - 2 := by omega
  rw [hk_eq] at hfe
  rw [h_close] at hfe
  exact absurd hfe (by decide)

/-- **Sourcing the produce-side joint's owed no-trailing boundary input from the R416 carrier** —
    `(i'-b-B2c-(d)-seq-separator-noTrailing-boundary)`, R419, BRICK (b) of the R418 CAUTION's two owed
    inputs (SMALLEST-FIRST: this is the genuinely-new residual the cell-3 boundary discharge flagged,
    [[ref-boundary-discharge-gate-trigger-typed]]).  `globalFlowSeqSepAdj_of_structure` (R418) took the
    pre-close non-separator `tokens[size-3] ≠ .flowEntry` as a NAMED hypothesis because neither opener
    sibling's discharge applies (the `≠ .key` gate ADMITS the seq close, and `.flowEntry` is
    balance-neutral, so both the `absurd h_close hne` and the Dyck-floor routes are gone).  This brick
    DISCHARGES that hypothesis — and the discharge reveals the cell-3 residual is NOT a fresh
    emitter-level field after all: it is the END-DUAL of the R416 `noTrailingSepFact tokens 2 (size-2)`
    carrier, the SAME body fact `seqSeparatorFacts_of_windowed_safebodyunit` already delivers at the root
    window for the root seed's per-window discharge — a DIFFERENT consumer
    ([[ref-deferred-structural-already-proven-by-sibling]]).  The R418 hedge ("source from the carrier OR
    a fresh structure field") resolves to the carrier; no new induction is owed.

    **The discharge** ([[ref-boundary-residual-end-dual]]).  Suppose `tokens[size-3] = .flowEntry` for
    contradiction.  Instantiate the carrier at `k = size-3`: `2 ≤ size-3` (from `size ≥ 5`),
    `(size-3)+1 = size-2`, the assumed separator, and the boundary balance
    `flowBracketBalance tokens 2 (size-3) = 0` (taken as a hypothesis — the depth-`0` reach of the close,
    sourced separately).  The carrier concludes `isFlowContentStart tokens[size-2]`; but
    `tokens[size-2] = .flowSequenceEnd` (the close, `h_close`), and `isFlowContentStart .flowSequenceEnd`
    is FALSE (the close is neither a scalar nor an opener).  The trailing-separator premise is refuted
    because its content-start conclusion lands on a token the window cannot follow.

    Verified-but-unconsumed: it is the (b)-brick of the R418 produce-side joint, which consumes it once the
    carrier + boundary-balance are wired in alongside the (a) body-separator structure-EXPOSE.  References
    no sorry site; frontier sorry count unchanged at 4. -/
theorem noTrailingSep_preClose_of_carrier
    (tokens : Array (Positioned YamlToken))
    (h_sz : 5 ≤ tokens.size)
    (h_close : tokens[tokens.size - 2]!.val = .flowSequenceEnd)
    (h_bal : flowBracketBalance tokens 2 (tokens.size - 3) = 0)
    (h_carrier : noTrailingSepFact tokens 2 (tokens.size - 2)) :
    tokens[tokens.size - 3]!.val ≠ .flowEntry := by
  intro h_fe
  have hk : (tokens.size - 3) + 1 = tokens.size - 2 := by omega
  have h2 : 2 ≤ tokens.size - 3 := by omega
  have h_cs := h_carrier (tokens.size - 3) h2 hk h_fe h_bal
  rw [hk, h_close] at h_cs
  simp [isFlowContentStart] at h_cs

/-- **The pre-close prefix balance is `0` IN THE BRANCH where the pre-close token is a separator** —
    `(i'-b-B2c-(d)-seq-separator-preClose-balance)`, R428, the shared kernel of BOTH axes' emit-wrapper
    pre-close discharge.  The R419 carrier route demanded `flowBracketBalance tokens 2 (size-3) = 0` as
    an UNCONDITIONAL hypothesis — but that fact is FALSE in general: when the seq's last element is a
    nested collection the pre-close token `tokens[size-3]` is a closing `]`/`}` (delta `-1`), so the
    pre-close prefix balance is `+1`, not `0`.  The fix ([[ref-contradiction-branch-supplies-boundary]]):
    the boundary balance is not a free-standing fact, it is a CONSEQUENCE of the very separator
    assumption the wrapper is refuting.  GIVEN `tokens[size-3] = .flowEntry` (the branch where a trailing
    separator is hypothesised), the `.flowEntry` has bracket-delta `0` (`flowBracketDelta_flowEntry`), so
    the one-step balance recurrence `balance 2 (size-2) = balance 2 (size-3) + delta tokens[size-3]`
    collapses to `balance 2 (size-3) = balance 2 (size-2) = 0` (the structure's outer balance conjunct).
    The recurrence is the inline analogue of `globalFlowSeqOpenerAdj_of_map_structure`'s `hstep`
    (`flowBracketBalance_compose` + `flowBracketBalance_single`).  Self-contained from the structure
    conclusion (no carrier, no `EmitScansInFlowRecEntry`); axis-blind (keyed only on the outer balance,
    not the close token).  References no sorry site; frontier sorry count unchanged at 4. -/
theorem preClose_balance_zero_of_flowEntry
    (tokens : Array (Positioned YamlToken))
    (h_sz : 5 ≤ tokens.size)
    (h_outer_bal : flowBracketBalance tokens 2 (tokens.size - 2) = 0)
    (h_fe : tokens[tokens.size - 3]!.val = .flowEntry) :
    flowBracketBalance tokens 2 (tokens.size - 3) = 0 := by
  have hm1 : (tokens.size - 3) + 1 = tokens.size - 2 := by omega
  have hm_sz : tokens.size - 3 < tokens.size := by omega
  have hstep : flowBracketBalance tokens 2 ((tokens.size - 3) + 1) =
      flowBracketBalance tokens 2 (tokens.size - 3)
        + flowBracketDelta tokens[tokens.size - 3]!.val := by
    rw [flowBracketBalance_compose tokens 2 (tokens.size - 3) ((tokens.size - 3) + 1)
      (by omega) (by omega)]
    have hlen : tokens.size - 3 < tokens.toList.length := by rw [Array.length_toList]; exact hm_sz
    rw [flowBracketBalance_single tokens (tokens.size - 3) hlen]
    have h1' : tokens.toList[tokens.size - 3]'hlen = tokens[tokens.size - 3] :=
      Array.getElem_toList hm_sz
    have h2' : tokens[tokens.size - 3] = tokens[tokens.size - 3]! :=
      (getElem!_pos tokens (tokens.size - 3) hm_sz).symm
    rw [h1', h2']
  have h_delta : flowBracketDelta tokens[tokens.size - 3]!.val = 0 := by
    rw [h_fe]; exact flowBracketDelta_flowEntry
  rw [hm1, h_outer_bal, h_delta] at hstep
  omega

/-- **The MAP-axis global separator producer — the predicted NON-mirror sibling of
    `globalFlowSeqSepAdj_of_structure`** — `(i'-b-B2c-(d)-produce-global-map-separator)`, R428.  The
    `.flowEntry`/`≠ .key` mirror of `globalFlowSeqOpenerAdj_of_map_structure` (R410), bearing the SAME
    relationship to the seq producer (R418) that the map opener producer bears to the seq opener: the
    five-way `k`-split is verbatim, only the two boundary tokens swap — `k=1` end-keys on the map head
    `.flowMappingStart` (instead of the seq `.flowSequenceStart`) and `k=size-2` on the map close
    `.flowMappingEnd` (instead of `.flowSequenceEnd`), both still `≠ .flowEntry` (`by decide`), so both
    boundary cells stay VACUOUS.  The pre-close cell (`k+1 = size-2`) is the SAME genuinely-new input
    `globalFlowSeqSepAdj_of_structure` needed — `tokens[size-3] ≠ .flowEntry`, the no-trailing-separator
    boundary ([[ref-boundary-residual-end-dual]]) — taken here as the named hypothesis the emit-wrapper
    discharges from the map's key-pattern conjunct + `preClose_balance_zero_of_flowEntry`.  References no
    sorry site; frontier sorry count unchanged at 4. -/
theorem globalFlowSeqSepAdj_of_map_structure
    (tokens : Array (Positioned YamlToken))
    (h_sz : 5 ≤ tokens.size)
    (h_t0 : tokens[0]!.val = .streamStart)
    (h_t1 : tokens[1]!.val = .flowMappingStart)
    (h_close : tokens[tokens.size - 2]!.val = .flowMappingEnd)
    (h_no_trailing_sep : tokens[tokens.size - 3]!.val ≠ .flowEntry)
    (h_body : ∀ k, 2 ≤ k → k + 1 < tokens.size - 2 →
        tokens[k]!.val = .flowEntry →
        tokens[k+1]!.val ≠ .key →
        isFlowContentStart tokens[k+1]!.val) :
    GlobalFlowSeqSepAdj tokens := by
  intro k hk1 hfe hne
  by_cases h0 : k = 0
  · subst h0; rw [h_t0] at hfe; exact absurd hfe (by decide)
  by_cases h1 : k = 1
  · subst h1; rw [h_t1] at hfe; exact absurd hfe (by decide)
  have hk2 : 2 ≤ k := by omega
  by_cases hb : k + 1 < tokens.size - 2
  · exact h_body k hk2 hb hfe hne
  by_cases hb2 : k + 1 = tokens.size - 2
  · have hk_eq : k = tokens.size - 3 := by omega
    rw [hk_eq] at hfe
    exact absurd hfe h_no_trailing_sep
  have hk_eq : k = tokens.size - 2 := by omega
  rw [hk_eq] at hfe
  rw [h_close] at hfe
  exact absurd hfe (by decide)

/-- **The SEQ (3)-PRODUCE-GLOBAL half — `GlobalFlowSeqSepAdj tokens` from the seq structure lemma** —
    `(i'-b-B2c-(d)-produce-global-seq-separator)`, R428, the `.flowEntry` mirror of
    `seqGlobalFlowSeqOpenerAdj_of_emit` (R409).  R427 (step 3 EXPOSE) made
    `scanFiltered_emitSeq_nonempty_structure` OUTPUT the all-depth `.flowEntry`-separator field over the
    body window `[2, size-2)` as its thirteenth conclusion conjunct; this is the downstream CONSUME half:
    destructure the conclusion and apply the landed producer `globalFlowSeqSepAdj_of_structure` (R418).
    Unlike the opener wrapper this is NOT a pure one-liner — the separator producer needs ONE extra input
    the opener did not, the pre-close no-trailing boundary `tokens[size-3] ≠ .flowEntry`.  It is
    discharged INLINE from the structure conclusion (NOT the R419 carrier route, whose unconditional
    boundary-balance hypothesis is unsatisfiable here): assume the pre-close is a `.flowEntry`, derive the
    branch-local balance `0` via `preClose_balance_zero_of_flowEntry`, feed both to the structure's
    body-successor conjunct at `k = size-3` — which concludes `tokens[size-2]` is flow-content-start, but
    `tokens[size-2] = .flowSequenceEnd` (the close) is NOT, contradiction.  Verified-but-unconsumed until
    the (d)–(e) `FlowSubrangesOk` rewire feeds it through `flowSeqSepAdj_window_of_global`; references no
    sorry site, frontier sorry count unchanged at 4. -/
theorem seqGlobalFlowSeqSepAdj_of_emit
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w) :
    GlobalFlowSeqSepAdj tokens := by
  obtain ⟨h_sz5, h_t0, _h_tend, h_t1, h_close, _h_head, h_bodysucc,
          h_outer_bal, _h_dyck, _h_wt_interior, _h_body_opener, h_body_separator⟩ :=
    scanFiltered_emitSeq_nonempty_structure items tokens h_scan h_ne h_all_block
  have h_nts : tokens[tokens.size - 3]!.val ≠ .flowEntry := by
    intro h_fe
    have h_bal := preClose_balance_zero_of_flowEntry tokens (by omega) h_outer_bal h_fe
    obtain ⟨_, h_cs⟩ := h_bodysucc (tokens.size - 3) (by omega) (by omega) h_fe h_bal
    rw [show (tokens.size - 3) + 1 = tokens.size - 2 by omega, h_close] at h_cs
    simp at h_cs
  exact globalFlowSeqSepAdj_of_structure tokens (by omega) h_t0 h_t1 h_close h_nts h_body_separator

/-- **The MAP (3)-PRODUCE-GLOBAL half — `GlobalFlowSeqSepAdj tokens` from the map structure lemma** —
    `(i'-b-B2c-(d)-produce-global-map-separator)`, R428.  Mirrors `seqGlobalFlowSeqSepAdj_of_emit` but
    feeds the non-mirror map producer `globalFlowSeqSepAdj_of_map_structure`, and its pre-close discharge
    refutes by a DIFFERENT conjunct: the map's body-pattern says a depth-`0` `.flowEntry` is followed by
    a `.key` (a flow-map entry's key marker), not a content-start, so the pre-close refutation feeds the
    branch-local balance into that key-pattern conjunct at `k = size-3`, concluding `tokens[size-2] =
    .key` — contradicting the map close `tokens[size-2] = .flowMappingEnd`.  The shared kernel is the
    same `preClose_balance_zero_of_flowEntry` (axis-blind); only the final token-clash differs (close vs
    content-start on the seq, close vs `.key` on the map).  Verified-but-unconsumed; references no sorry
    site, frontier sorry count unchanged at 4. -/
theorem mapGlobalFlowSeqSepAdj_of_emit
    (pairs : Array (YamlValue × YamlValue)) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}") = .ok tokens)
    (h_ne : pairs.toList ≠ [])
    (h_all_k_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowSavedKeyBlock p.1)
    (h_all_v_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowBlock p.2) :
    GlobalFlowSeqSepAdj tokens := by
  obtain ⟨h_sz7, h_t0, _h_tend, h_t1, h_close, _h_key, h_keypattern,
          h_outer_bal, _h_dyck, _h_wt_interior, _h_pnok, _h_body_opener, h_body_separator⟩ :=
    scanFiltered_emitMap_nonempty_structure pairs tokens h_scan h_ne h_all_k_block h_all_v_block
  have h_nts : tokens[tokens.size - 3]!.val ≠ .flowEntry := by
    intro h_fe
    have h_bal := preClose_balance_zero_of_flowEntry tokens (by omega) h_outer_bal h_fe
    obtain ⟨_, h_key⟩ := h_keypattern (tokens.size - 3) (by omega) (by omega) h_fe h_bal
    rw [show (tokens.size - 3) + 1 = tokens.size - 2 by omega, h_close] at h_key
    exact absurd h_key (by decide)
  exact globalFlowSeqSepAdj_of_map_structure tokens (by omega) h_t0 h_t1 h_close h_nts h_body_separator

/-- **The per-window separator-adjacency provider, SEQ emit source** —
    `(i'-b-B2c-(d)-window-separator-adjacency-seq)`, R429, the `.flowEntry` mirror of R411's
    `seqWindowOpenerAdj_of_emit` and the THIRD per-window field the R416 (R2) consumer re-thread left owed
    (`FlowBodyContentDeepSeq.feContentStart`).  It chains the two now-landed halves of the separator
    carry-up — `seqGlobalFlowSeqSepAdj_of_emit` (R428, the CONSUME that produces `GlobalFlowSeqSepAdj
    tokens` from a scanned top-level seq, with the pre-close no-trailing boundary discharged inline by
    contradiction, [[ref-contradiction-branch-supplies-boundary]]) and `flowSeqSepAdj_window_of_global`
    (R417, the trivial subset restriction of the global predicate to any window `[lo, hi)` with
    `hi ≤ size`) — into a single per-window provider keyed exactly on a `FlowSubrangesOk.seq` sub-window's
    shape: at any `[lo, hi)` with `hi ≤ tokens.size`, the all-depth `.flowEntry`-separator field holds
    (every flow-sequence separator at depth-blind `k ∈ [lo, hi)` whose successor is `≠ .key` is followed by
    a content-start).  The `hi ≤ size` premise is weaker than the `FlowSubrangesOk.seq` guard's `hi < size`,
    so it discharges by `Nat.le_of_lt` at the call site.  Structurally IDENTICAL plumbing to the opener
    wrapper ([[ref-window-absolute-gate-subset-restriction]]: one global shape, one restriction lemma, fed
    from either emit source) — the only deltas are the gate token (`.flowEntry` vs `.flowSequenceStart`) and
    the successor-exclusion (`≠ .key` vs `≠ .flowSequenceEnd`).  Verified-but-unconsumed until the
    gate-strengthening bridge feeds this into the per-window `Rec…Body` producers; references no sorry
    site, frontier sorry count unchanged at 4. -/
theorem seqWindowSepAdj_of_emit
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w)
    (h_hi : hi ≤ tokens.size) :
    ∀ k, lo ≤ k → k + 1 < hi →
      tokens[k]!.val = .flowEntry →
      tokens[k+1]!.val ≠ .key →
      isFlowContentStart tokens[k+1]!.val :=
  flowSeqSepAdj_window_of_global tokens lo hi
    (seqGlobalFlowSeqSepAdj_of_emit items tokens h_scan h_ne h_all_block) h_hi

/-- **The per-window separator-adjacency provider, MAP emit source** —
    `(i'-b-B2c-(d)-window-separator-adjacency-map)`, R429, the orthogonal-axis mirror of
    `seqWindowSepAdj_of_emit` ([[ref-conjunctive-consumer-gates-on-orthogonal-axis]]: a top-level map nests
    seqs, so (d) must feed the SAME separator field on BOTH axes).  The SAME window field, sourced from a
    scanned top-level MAP via `mapGlobalFlowSeqSepAdj_of_emit` (R428, the non-mirror sibling producer whose
    pre-close discharge refutes through the map's `.key` body-pattern conjunct rather than the seq's
    content-successor one).  The [[ref-coerce-to-weaker-reuse-wrapper]] payoff of keeping `GlobalFlowSeqSepAdj`
    AXIS-UNIFORM: ONE global shape, ONE restriction lemma `flowSeqSepAdj_window_of_global`, fed from either
    emit source — the conjunctive consumer's two orthogonal conjuncts consume the same per-window
    deliverable, differing only in which emit wrapper produced the global fact.  Completes the separator
    half of the per-window opener/separator pair; with `seq/mapWindowOpenerAdj_of_emit` (R411) the assembler
    `flowBodyContentDeepSeq_of_window_producers` now has all THREE `FlowBodyContentDeepSeq` fields available
    from emission.  Verified-but-unconsumed; references no sorry site, frontier sorry count unchanged at 4. -/
theorem mapWindowSepAdj_of_emit
    (pairs : Array (YamlValue × YamlValue)) (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_scan : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}") = .ok tokens)
    (h_ne : pairs.toList ≠ [])
    (h_all_k_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowSavedKeyBlock p.1)
    (h_all_v_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowBlock p.2)
    (h_hi : hi ≤ tokens.size) :
    ∀ k, lo ≤ k → k + 1 < hi →
      tokens[k]!.val = .flowEntry →
      tokens[k+1]!.val ≠ .key →
      isFlowContentStart tokens[k+1]!.val :=
  flowSeqSepAdj_window_of_global tokens lo hi
    (mapGlobalFlowSeqSepAdj_of_emit pairs tokens h_scan h_ne h_all_k_block h_all_v_block) h_hi

/-- **The per-window deep-content guard ASSEMBLER, SEQ emit source** —
    `(i'-b-B2c-(d)-flowBodyContentDeepSeq-of-window-producers-seq)`, R430, the brick that wires the three
    now-landed per-window providers into the re-scoped carrier `FlowBodyContentDeepSeq tokens lo hi`.  Its
    two universal fields are EXACT matches of the window providers — `openerContentStart` is R411's
    `seqWindowOpenerAdj_of_emit`, `feContentStart` is R429's `seqWindowSepAdj_of_emit`, both consumed
    verbatim (the [[ref-orthogonal-field-mirror-costs-discriminator]] payoff: the carrier's two interior
    fields ARE the two window providers, nothing to re-derive).  The third field `headContentStart`
    (`isFlowContentStart tokens[lo]`) is the lone position-`lo`-keyed read, recovered from the GLOBAL
    opener `seqGlobalFlowSeqOpenerAdj_of_emit` (R409) at `k = lo - 1`: the window's head is the token after
    the `.flowSequenceStart` that opens it (`h_open : tokens[lo-1] = .flowSequenceStart`), and the
    non-degeneracy gate `tokens[lo] ≠ .flowSequenceEnd` (`h_head_ne`) fires the opener body.  KEY: this is
    sourced from the UNBOUNDED global predicate, NOT the window-restricted opener field — the restriction's
    lower bound `lo` excludes exactly the `lo-1` index the head needs, so reading the edge off the global
    erases the degenerate `lo = 2` boundary special-case that R391's window-bounded
    `flowBodyContentDeep_window_of_root` required ([[ref-edge-adjacent-read-from-global-not-restricted]]).
    Verified-but-unconsumed until the (R1) root carrier + window dispatch supplies `h_open`/`h_head_ne`;
    references no sorry site, frontier sorry count unchanged at 4. -/
theorem flowBodyContentDeepSeq_of_window_producers
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo < hi) (h_hi : hi ≤ tokens.size)
    (h_open : tokens[lo - 1]!.val = .flowSequenceStart)
    (h_head_ne : tokens[lo]!.val ≠ .flowSequenceEnd) :
    FlowBodyContentDeepSeq tokens lo hi := by
  have hlo1 : lo - 1 + 1 = lo := Nat.sub_add_cancel h_lo
  refine ⟨?_, ?_, ?_⟩
  · -- headContentStart: the GLOBAL opener at k = lo - 1 (unbounded ⇒ no `lo = 2` special-case)
    have hg := seqGlobalFlowSeqOpenerAdj_of_emit items tokens h_scan h_ne h_all_block
    have h := hg (lo - 1) (by omega) h_open (by rwa [hlo1])
    rwa [hlo1] at h
  · -- openerContentStart: R411 window provider, verbatim
    exact seqWindowOpenerAdj_of_emit items tokens lo hi h_scan h_ne h_all_block h_hi
  · -- feContentStart: R429 window provider, verbatim
    exact seqWindowSepAdj_of_emit items tokens lo hi h_scan h_ne h_all_block h_hi

/-- **The per-window deep-content guard ASSEMBLER, MAP emit source** —
    `(i'-b-B2c-(d)-flowBodyContentDeepSeq-of-window-producers-map)`, R430, the orthogonal-axis mirror of
    `flowBodyContentDeepSeq_of_window_producers` ([[ref-conjunctive-consumer-gates-on-orthogonal-axis]]: a
    top-level MAP nests flow SEQUENCES, whose interior windows carry the SAME `FlowBodyContentDeepSeq`
    guard).  Structurally identical — the head recovered from `mapGlobalFlowSeqOpenerAdj_of_emit` (R410),
    the interior fields from `mapWindowOpenerAdj_of_emit` (R411) / `mapWindowSepAdj_of_emit` (R429) — with
    only the emit facts swapped to the map family.  The [[ref-coerce-to-weaker-reuse-wrapper]] payoff of
    keeping `GlobalFlowSeqOpenerAdj`/`GlobalFlowSeqSepAdj` axis-uniform: ONE carrier, ONE assembler shape,
    fed from either emit source.  Verified-but-unconsumed; references no sorry site, frontier sorry count
    unchanged at 4. -/
theorem flowBodyContentDeepSeq_of_window_producers_map
    (pairs : Array (YamlValue × YamlValue)) (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_scan : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}") = .ok tokens)
    (h_ne : pairs.toList ≠ [])
    (h_all_k_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowSavedKeyBlock p.1)
    (h_all_v_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowBlock p.2)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo < hi) (h_hi : hi ≤ tokens.size)
    (h_open : tokens[lo - 1]!.val = .flowSequenceStart)
    (h_head_ne : tokens[lo]!.val ≠ .flowSequenceEnd) :
    FlowBodyContentDeepSeq tokens lo hi := by
  have hlo1 : lo - 1 + 1 = lo := Nat.sub_add_cancel h_lo
  refine ⟨?_, ?_, ?_⟩
  · -- headContentStart: the GLOBAL opener (map source) at k = lo - 1
    have hg := mapGlobalFlowSeqOpenerAdj_of_emit pairs tokens h_scan h_ne h_all_k_block h_all_v_block
    have h := hg (lo - 1) (by omega) h_open (by rwa [hlo1])
    rwa [hlo1] at h
  · -- openerContentStart: R411 map window provider, verbatim
    exact mapWindowOpenerAdj_of_emit pairs tokens lo hi h_scan h_ne h_all_k_block h_all_v_block h_hi
  · -- feContentStart: R429 map window provider, verbatim
    exact mapWindowSepAdj_of_emit pairs tokens lo hi h_scan h_ne h_all_k_block h_all_v_block h_hi

/-- **A flow-body window's head is never the close** — `(i'-b-B2c-(d)-window-head-ne-close)`, R431.  The
    head token `tokens[lo]` of a `FlowBodyWindow tokens lo hi` is NOT a `.flowSequenceEnd`.  This is NOT a
    separate emission fact — it is a FREE consequence of the window's own Dyck floor: the floor gives
    `flowBracketBalance tokens lo (lo+1) ≥ 0`, the one-step balance is `flowBracketDelta tokens[lo]!.val`,
    and a `.flowSequenceEnd` has bracket-delta `-1 < 0`, contradiction.  In other words the non-emptiness
    of a body window (`tokens[lo] ≠ ]`) is ENCODED in its floor, not a fact to be threaded separately:
    an empty `[]` window would have a close-head, but its floor would dip to `-1` at the very first step,
    so it is not a `FlowBodyWindow` at all.  Axis-agnostic (the map mirror's `.flowMappingEnd` is the same
    delta `-1`, but this lemma is stated for the seq close the `FlowBodyContentDeepSeq` head gate needs). -/
theorem flowBodyWindow_head_ne_close (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi) :
    tokens[lo]!.val ≠ .flowSequenceEnd := by
  intro h_close
  have h_lo_sz : lo < tokens.size := by
    have := h_win.lo_lt_hi; have := h_win.hi_lt; omega
  have hlen : lo < tokens.toList.length := by rw [Array.length_toList]; exact h_lo_sz
  have hfloor := h_win.dyck (lo + 1) (by omega) (by have := h_win.lo_lt_hi; omega)
  rw [flowBracketBalance_single tokens lo hlen] at hfloor
  have h1 : tokens.toList[lo]'hlen = tokens[lo] := Array.getElem_toList h_lo_sz
  have h2 : tokens[lo] = tokens[lo]! := (getElem!_pos tokens lo h_lo_sz).symm
  rw [h1, h2, h_close, flowBracketDelta_flowSequenceEnd] at hfloor
  omega

/-- **The per-window `FlowBodyContentDeepSeq` provider from emission, SEQ source** —
    `(i'-b-B2c-(d)-flowBodyContentDeepSeq-of-emit-and-window-seq)`, R431, the brick that hands the R430
    assembler the SAME `FlowBodyWindow` the recursion already threads — discharging R430's awkward
    `h_head_ne` hypothesis FOR FREE via `flowBodyWindow_head_ne_close` (the Dyck-floor consequence), and
    `h_lo`/`h_hi` from the window's own `lo_ge`/`hi_lt` fields.  So the per-window deep-content supply
    needs, beyond the window facts + emission, ONLY the enclosing-opener guard `tokens[lo-1] =
    .flowSequenceStart` (the one fact a bracket-shape window cannot self-supply — it names which bracket
    TYPE encloses it).  This is exactly the shape the `windowFacts` provider of
    `seqRec_of_carrier_and_windowFacts` consumes for its `FlowBodyContentDeepSeq` field.
    Verified-but-unconsumed until `windowFacts` is assembled; references no sorry site, frontier sorry
    count unchanged at 4. -/
theorem flowBodyContentDeepSeq_of_emit_and_window
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_open : tokens[lo - 1]!.val = .flowSequenceStart) :
    FlowBodyContentDeepSeq tokens lo hi :=
  flowBodyContentDeepSeq_of_window_producers items tokens lo hi h_scan h_ne h_all_block
    (by have := h_win.lo_ge; omega) h_win.lo_lt_hi (Nat.le_of_lt h_win.hi_lt) h_open
    (flowBodyWindow_head_ne_close tokens lo hi h_win)

/-- **The per-window `FlowBodyContentDeepSeq` provider from emission, MAP source** —
    `(i'-b-B2c-(d)-flowBodyContentDeepSeq-of-emit-and-window-map)`, R431, the orthogonal-axis mirror
    (a top-level MAP nests flow SEQUENCES whose interior windows carry `FlowBodyContentDeepSeq`).  Same
    `FlowBodyWindow`-fed shape, `h_head_ne` again free from the Dyck floor, sourced from the map emit
    family.  Verified-but-unconsumed; references no sorry site, frontier sorry count unchanged at 4. -/
theorem flowBodyContentDeepSeq_of_emit_and_window_map
    (pairs : Array (YamlValue × YamlValue)) (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_scan : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}") = .ok tokens)
    (h_ne : pairs.toList ≠ [])
    (h_all_k_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowSavedKeyBlock p.1)
    (h_all_v_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowBlock p.2)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_open : tokens[lo - 1]!.val = .flowSequenceStart) :
    FlowBodyContentDeepSeq tokens lo hi :=
  flowBodyContentDeepSeq_of_window_producers_map pairs tokens lo hi h_scan h_ne h_all_k_block
    h_all_v_block (by have := h_win.lo_ge; omega) h_win.lo_lt_hi (Nat.le_of_lt h_win.hi_lt) h_open
    (flowBodyWindow_head_ne_close tokens lo hi h_win)

/-- **The FULL `windowFacts` triple from emission, SEQ source** —
    `(i'-b-B2c-(d)-seqWindowFacts-of-emit-seq)`, R432, the brick that completes the CONTENT of the flat
    per-window provider `seqRec_of_carrier_and_windowFacts_seq` consumes: at every seq window it produces
    all THREE fields `FlowBodyWindow ∧ FlowBodyContentDeepSeq ∧ SeqEnclosed`.  It composes the two landed
    halves — R390's `flowBodyWindow_and_seqEnclosed_of_facts` (the bracket + enclosure fields) and R431's
    `flowBodyContentDeepSeq_of_emit_and_window` (the deep-content field) — and the KEY structural move is
    that the deep field is sourced from the `FlowBodyWindow` the FIRST half just PRODUCED (R431's provider
    consumes `h_win`), not from a fresh hypothesis: a later provider field is discharged from an EARLIER
    field's OUTPUT ([[ref-provider-field-from-sibling-output]]).  So the combined residual is NOT the union
    of each field's primitives but only R390's three global-restriction primitives `h_wt_outer` /
    `h_win_dyck` / `h_fold_pre` — the Dyck floor `h_win_dyck` does DOUBLE DUTY (it is `FlowBodyWindow.dyck`
    AND, through R431, the source of `FlowBodyContentDeepSeq`'s head non-emptiness).  The three primitives
    are the whole-stream-well-bracketedness restrictions a separate brick supplies once.
    Verified-but-unconsumed until those primitives are sourced; references no sorry site, frontier sorry
    count unchanged at 4. -/
theorem seqWindowFacts_of_emit_and_primitives
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w)
    (h_wt_outer : WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2))
    (lo hi : Nat)
    (h_lo : 2 ≤ lo) (h_lo_hi : lo < hi) (h_hi : hi ≤ tokens.size - 2) (h_hi_sz : hi < tokens.size)
    (h_bal : flowBracketBalance tokens lo hi = 0)
    (h_open : tokens[lo - 1]!.val = .flowSequenceStart)
    (h_win_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_fold_pre : ∃ s, btFold (some []) (tokens.toList.take (lo - 1)) = some s) :
    FlowBodyWindow tokens lo hi ∧ FlowBodyContentDeepSeq tokens lo hi ∧ SeqEnclosed tokens lo := by
  obtain ⟨h_win, h_enc⟩ := flowBodyWindow_and_seqEnclosed_of_facts tokens lo hi h_lo h_lo_hi h_hi
    h_hi_sz h_bal h_open h_wt_outer h_win_dyck h_fold_pre
  exact ⟨h_win,
    flowBodyContentDeepSeq_of_emit_and_window items tokens lo hi h_scan h_ne h_all_block h_win h_open,
    h_enc⟩

/-- **The FULL `windowFacts` triple from emission, MAP source** —
    `(i'-b-B2c-(d)-seqWindowFacts-of-emit-map)`, R432, the orthogonal-axis mirror (the seq recursion also
    runs over windows nested in a top-level MAP).  Same composition — R390 for the bracket + enclosure
    fields (axis-agnostic), R431's `flowBodyContentDeepSeq_of_emit_and_window_map` for the deep field, fed
    the produced `FlowBodyWindow` — with only the emit facts swapped to the map family.
    Verified-but-unconsumed; references no sorry site, frontier sorry count unchanged at 4. -/
theorem seqWindowFacts_of_emit_and_primitives_map
    (pairs : Array (YamlValue × YamlValue)) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}") = .ok tokens)
    (h_ne : pairs.toList ≠ [])
    (h_all_k_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowSavedKeyBlock p.1)
    (h_all_v_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowBlock p.2)
    (h_wt_outer : WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2))
    (lo hi : Nat)
    (h_lo : 2 ≤ lo) (h_lo_hi : lo < hi) (h_hi : hi ≤ tokens.size - 2) (h_hi_sz : hi < tokens.size)
    (h_bal : flowBracketBalance tokens lo hi = 0)
    (h_open : tokens[lo - 1]!.val = .flowSequenceStart)
    (h_win_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_fold_pre : ∃ s, btFold (some []) (tokens.toList.take (lo - 1)) = some s) :
    FlowBodyWindow tokens lo hi ∧ FlowBodyContentDeepSeq tokens lo hi ∧ SeqEnclosed tokens lo := by
  obtain ⟨h_win, h_enc⟩ := flowBodyWindow_and_seqEnclosed_of_facts tokens lo hi h_lo h_lo_hi h_hi
    h_hi_sz h_bal h_open h_wt_outer h_win_dyck h_fold_pre
  exact ⟨h_win,
    flowBodyContentDeepSeq_of_emit_and_window_map pairs tokens lo hi h_scan h_ne h_all_k_block
      h_all_v_block h_win h_open,
    h_enc⟩

/-- **The RE-SCOPED, FLOOR-GUARDED `h_seq_rec` reduction to root carrier + windowFacts** —
    `(i'-b-B2c-(d)-seqRec-of-carrier-and-windowFacts-seq)`, R432 + R433-floor.  The `_seq` twin of R389's
    `seqRec_of_carrier_and_windowFacts` migrated to the re-scoped guard ([[ref-additive-parallel-type-over-shared-edit]]:
    content field `FlowBodyContentDeepSeq` not the false-rooted `FlowBodyContentDeep`; consumed recursion
    `seqWindowRecSeqBody_seq`).

    **R433 fix** ([[ref-bracket-guards-admit-cross-matched-window]]): the R432 unfloored shape carried the
    SEVEN bracket-shape guards only — and `seqWindowFacts_false_window` machine-checked that those admit a
    CROSS-MATCHED false window (`[3,7)` of `[[],[a]]`: all seven hold but the Dyck floor underflows, so
    `FlowBodyWindow` is false ⇒ the `windowFacts` hypothesis was UNSATISFIABLE).  This version adds the
    interior Dyck floor `∀ i ∈ [lo, hi], balance lo i ≥ 0` as an 8th guard to BOTH the `windowFacts`
    hypothesis and the produced `h_seq_rec` conclusion — it EXCLUDES every cross-matched window, restoring
    satisfiability, and threads through trivially (the producer just RECEIVES it on the conclusion side and
    PASSES it to `windowFacts` — contravariant, free on the producer side; the matching consumer-side floor
    of `flowSubrangesOk_of_window_producers`'s `h_seq_rec`, via `seqLocator_of_window_recseqbody`, is the
    next brick).  The floored `windowFacts` matches `seqWindowFacts_of_emit_and_primitives`, whose
    `h_win_dyck` IS this floor.  Verified-but-unconsumed until the consumer floor + root carrier (R1) land;
    references no sorry site, frontier sorry count unchanged at 4. -/
theorem seqRec_of_carrier_and_windowFacts_seq (tokens : Array (Positioned YamlToken))
    (h_root_carrier : SeqInteriorSeparators tokens 2 (tokens.size - 2))
    (windowFacts : ∀ lo hi, 2 ≤ lo → lo < hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowSequenceEnd → flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowSequenceStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      FlowBodyWindow tokens lo hi ∧ FlowBodyContentDeepSeq tokens lo hi ∧ SeqEnclosed tokens lo) :
    ∀ lo hi, 2 ≤ lo → lo < hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowSequenceEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowSequenceStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      RecSeqBody ((tokens.toList.take hi).drop lo) := by
  intro lo hi h2 hlt hhi hsz hclose hbal hopen hfloor
  obtain ⟨h_win, h_deep, h_enc⟩ := windowFacts lo hi h2 hlt hhi hsz hclose hbal hopen hfloor
  exact seqWindowRecSeqBody_seq tokens h_root_carrier lo hi h_win h_deep h_enc hclose

/-- **The floored `windowFacts` provider's per-window fold-totality primitive is SATISFIABLE on real
    output** — `(i'-b-B2c-(d)-seqFoldTotal-satisfiable)`, R441, the SMALLEST-FIRST de-risk that
    `seqHRec_of_root_and_context` (below) does not thread a VACUOUS hypothesis.  Docking
    `seqRec_of_carrier_and_windowFacts_seq` retires the producer's CONCLUSION de-risk by importing the
    already-proven assembler `seqWindowFacts_of_emit_and_primitives` (the floored 8-guard → 3-fact
    triple is a theorem, so the floored provider is satisfiable BY CONSTRUCTION — no fresh witness for
    `FlowBodyWindow`/`FlowBodyContentDeepSeq`/`SeqEnclosed`, which are DERIVED from the guards, not owed).
    But the dock RELOCATES the unsatisfiability risk from the conclusion onto the residual HYPOTHESES it
    threads — exactly the R433 trap one layer up ([[ref-bracket-guards-admit-cross-matched-window]]): a
    `lemma H → C` with unsatisfiable `H` type-checks yet is vacuous.  The window guards and `h_wt_outer`
    are bracket facts available at the consume site; the one threaded primitive whose truth is NOT
    self-evident is the per-window fold-totality `∀ m, ∃ s, btFold (some []) (tokens.toList.take m) =
    some s` (`seqWindowFacts_of_emit_and_primitives`'s `h_fold_pre`, instantiated at `m := lo - 1`).

    This lemma PROVES it TRUE on the genuine witness `[[],[a]]` — and proves the strong GENERAL `∀ m`
    form, not a single prefix: the whole scanned stream is `WellTyped` (`btFold (some []) tokens.toList
    = some []`, machine-checked — `btStep` is the identity on the non-bracket `streamStart`/`streamEnd`
    and every interior prefix is balanced), and `WellTyped_prefix_some` turns whole-stream
    well-typedness into fold-totality at EVERY prefix.  So the probe also NAMES the future discharge
    route for `h_fold_total`: a whole-stream `WellTyped tokens.toList` fact (none exists yet — `h_wt_outer`
    covers only the interior `(take (size-2)).drop 2`) fed through `WellTyped_prefix_some`.  Contains the
    `ofReduceBool` axiom (`native_decide`), off the `universal_roundtrip` path. -/
theorem seqFoldTotal_satisfiable_on_real_output
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered
        ("[" ++ emit.emitList
          [YamlValue.sequence .flow #[],
           YamlValue.sequence .flow #[YamlValue.scalar { content := "a", style := .plain }]]
        ++ "]") = .ok tokens) :
    WellTyped tokens.toList ∧
    ∀ m, ∃ s, btFold (some []) (tokens.toList.take m) = some s := by
  have key : ∀ {α : Type} (g : Array (Positioned YamlToken) → α) (a : α),
      (Scanner.scanFiltered
          ("[" ++ emit.emitList
            [YamlValue.sequence .flow #[],
             YamlValue.sequence .flow #[YamlValue.scalar { content := "a", style := .plain }]]
          ++ "]")).toOption.map g = some a →
        g tokens = a := by
    intro α g a e; rw [h] at e; exact Option.some.inj e
  have hwt : btFold (some []) tokens.toList = some [] :=
    key (fun t => btFold (some []) t.toList) (some []) (by native_decide)
  refine ⟨hwt, fun m => ?_⟩
  apply WellTyped_prefix_some (tokens.toList.take m) (tokens.toList.drop m)
  rw [List.take_append_drop]
  exact hwt

/-- **The floored `windowFacts` provider, assembled from emission context** —
    `(i'-b-B2c-(d)-seqWindowFacts-provider-of-context)`, R441.  Curries the proven R432 brick
    `seqWindowFacts_of_emit_and_primitives` into EXACTLY the `windowFacts` hypothesis shape that
    `seqRec_of_carrier_and_windowFacts_seq` consumes (its 8-guard → `FlowBodyWindow ∧
    FlowBodyContentDeepSeq ∧ SeqEnclosed` universal).  The producer's window shape additionally binds the
    close guard `tokens[hi]!.val = .flowSequenceEnd` — the assembler RECEIVES and DROPS it (`_hclose`);
    the three facts come entirely from the bracket/balance/floor guards + the emit context.  The floor
    (`hfloor`) IS `seqWindowFacts_of_emit_and_primitives`'s `h_win_dyck` — so after R440's conduit
    flooring the two shapes are textually identical and this is pure currying.  The per-window
    `h_fold_pre` is supplied from the threaded whole-stream fold-totality `h_fold_total` at `m := lo - 1`
    (its satisfiability is `seqFoldTotal_satisfiable_on_real_output` above).
    Verified-but-unconsumed until `h_fold_total` is sourced; references no sorry site, frontier sorry
    count unchanged at 4. -/
theorem seqWindowFacts_provider_of_context
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w)
    (h_wt_outer : WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2))
    (h_fold_total : ∀ m, ∃ s, btFold (some []) (tokens.toList.take m) = some s) :
    ∀ lo hi, 2 ≤ lo → lo < hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowSequenceEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowSequenceStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      FlowBodyWindow tokens lo hi ∧ FlowBodyContentDeepSeq tokens lo hi ∧ SeqEnclosed tokens lo :=
  fun lo hi h2 hlt hhi hsz _hclose hbal hopen hfloor =>
    seqWindowFacts_of_emit_and_primitives items tokens h_scan h_ne h_all_block h_wt_outer
      lo hi h2 hlt hhi hsz hbal hopen hfloor (h_fold_total (lo - 1))

/-- **The floored seq `h_seq_rec` producer, DOCKED to its root carrier + emission context** —
    `(i'-b-B2c-(d)-seqHRec-of-root-and-context)`, R441, the PAYOFF of R440's conduit flooring.  Composes
    the floored producer `seqRec_of_carrier_and_windowFacts_seq` (whose conclusion R440 made textually
    identical to `flowSubrangesOk_of_window_producers`'s `h_seq_rec` slot) with the windowFacts provider
    `seqWindowFacts_provider_of_context` just assembled.  Its conclusion IS that `h_seq_rec` slot
    verbatim — so wiring it into `flowSubrangesOk_of_window_producers` is a direct substitution, no
    adapter.

    This reduces the entire seq-side `h_seq_rec` obligation to FOUR named residuals: **(1)** the ROOT
    CARRIER `SeqInteriorSeparators tokens 2 (tokens.size - 2)` — itself reducing (via
    `seqRoot_seqInteriorSeparators`) to the `desc` descent provider, the hard B2 brick; **(2)** the
    whole-stream fold-totality `h_fold_total` (TRUE — `seqFoldTotal_satisfiable_on_real_output`; future
    route: a `WellTyped tokens.toList` fact via `WellTyped_prefix_some`); **(3)** `h_wt_outer` (available
    at the consume site as the interior `WellTyped`); **(4)** the emit context (`h_scan`/`h_ne`/
    `h_all_block`).  Verified-but-unconsumed until the root carrier + fold-totality land; references no
    sorry site, frontier sorry count unchanged at 4. -/
theorem seqHRec_of_root_and_context
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w)
    (h_wt_outer : WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2))
    (h_fold_total : ∀ m, ∃ s, btFold (some []) (tokens.toList.take m) = some s)
    (h_root_carrier : SeqInteriorSeparators tokens 2 (tokens.size - 2)) :
    ∀ lo hi, 2 ≤ lo → lo < hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowSequenceEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowSequenceStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      RecSeqBody ((tokens.toList.take hi).drop lo) :=
  seqRec_of_carrier_and_windowFacts_seq tokens h_root_carrier
    (seqWindowFacts_provider_of_context items tokens h_scan h_ne h_all_block h_wt_outer h_fold_total)

/-- **Whole-stream well-typedness from the emit context** —
    `(i'-b-B2c-(d)-seqWholeStreamWellTyped)`, the GENERAL, axiom-clean producer of `WellTyped
    tokens.toList` that the satisfiability probe `seqFoldTotal_satisfiable_on_real_output` (R441)
    proved only on a CONCRETE witness by `native_decide`.  That probe's own docstring NAMED this
    discharge route — "a whole-stream `WellTyped tokens.toList` fact (none exists yet — `h_wt_outer`
    covers only the interior `(take (size-2)).drop 2`) fed through `WellTyped_prefix_some`" — and its
    proof factored as `general_reduction (concrete_fact)`: the `∀ m` fold-totality form fell out of
    `WellTyped_prefix_some` GENERICALLY, with ONLY the whole-stream `WellTyped tokens.toList` leaf
    example-specific.  So promoting the probe is replacing that one `native_decide` leaf with a
    STRUCTURAL derivation of the single fact it localized, reusing the generic tail verbatim
    (`seqFoldTotal_of_context` below).

    The structural derivation reads the emitted+filtered stream off `scanFiltered_emitSeq_nonempty_structure`
    as `streamStart :: .flowSequenceStart :: interior ++ [.flowSequenceEnd, streamEnd]` (the four boundary
    tokens + `size ≥ 5` + the interior `WellTyped`), and folds piecewise the SAME way `seqRoot_seqPathAllSeq`
    (R386) computes the depth-2 prefix: `btStep` is the identity on `streamStart`/`streamEnd` (non-bracket),
    pushes `true` on `[`, and the interior returns the stack to `[true]` by `WellTyped_frame` of `h_wt_interior`,
    then `]` pops back to `[]`.  No `native_decide`; axiom-clean.  References no sorry site, frontier sorry
    count unchanged at 4. -/
theorem seqWholeStreamWellTyped
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w) :
    WellTyped tokens.toList := by
  obtain ⟨h_sz5, h_t0, h_tlast, h_t1, h_tpe, _h_content0, _h_fe_pattern,
          _h_outer_bal, _h_dyck, h_wt_interior, _h_body_opener, _h_body_separator⟩ :=
    scanFiltered_emitSeq_nonempty_structure items tokens h_scan h_ne h_all_block
  have h_len : tokens.toList.length = tokens.size := Array.length_toList
  -- the four boundary indices are in range
  have hb0 : 0 < tokens.toList.length := by rw [h_len]; omega
  have hb1 : 1 < tokens.toList.length := by rw [h_len]; omega
  have hbe : tokens.size - 2 < tokens.toList.length := by rw [h_len]; omega
  have hbl : tokens.size - 1 < tokens.toList.length := by rw [h_len]; omega
  -- their token VALUES (bridged from the `tokens[_]!` boundary facts)
  have e0 : (tokens.toList[0]'hb0).val = .streamStart := by
    have hb : tokens.toList[0]'hb0 = tokens[0]! := by
      rw [Array.getElem_toList, getElem!_pos tokens 0 (by omega)]
    rw [hb]; exact h_t0
  have e1 : (tokens.toList[1]'hb1).val = .flowSequenceStart := by
    have hb : tokens.toList[1]'hb1 = tokens[1]! := by
      rw [Array.getElem_toList, getElem!_pos tokens 1 (by omega)]
    rw [hb]; exact h_t1
  have ee : (tokens.toList[tokens.size - 2]'hbe).val = .flowSequenceEnd := by
    have hb : tokens.toList[tokens.size - 2]'hbe = tokens[tokens.size - 2]! := by
      rw [Array.getElem_toList, getElem!_pos tokens (tokens.size - 2) (by omega)]
    rw [hb]; exact h_tpe
  have el : (tokens.toList[tokens.size - 1]'hbl).val = .streamEnd := by
    have hb : tokens.toList[tokens.size - 1]'hbl = tokens[tokens.size - 1]! := by
      rw [Array.getElem_toList, getElem!_pos tokens (tokens.size - 1) (by omega)]
    rw [hb]; exact h_tlast
  -- prefix `take 2` = [streamStart, `[`]
  have h_take2 : tokens.toList.take 2 = [tokens.toList[0]'hb0, tokens.toList[1]'hb1] := by
    have step1 : tokens.toList.take 2 = tokens.toList.take 1 ++ [tokens.toList[1]'hb1] :=
      List.take_succ_eq_append_getElem hb1
    have step0 : tokens.toList.take 1 = tokens.toList.take 0 ++ [tokens.toList[0]'hb0] :=
      List.take_succ_eq_append_getElem hb0
    rw [step1, step0]; rfl
  -- suffix `drop (size-2)` = [`]`, streamEnd]
  have h_suf : tokens.toList.drop (tokens.size - 2)
      = [tokens.toList[tokens.size - 2]'hbe, tokens.toList[tokens.size - 1]'hbl] := by
    have d1 : tokens.toList.drop (tokens.size - 2)
        = tokens.toList[tokens.size - 2]'hbe :: tokens.toList.drop (tokens.size - 2 + 1) :=
      List.drop_eq_getElem_cons hbe
    have hidx : tokens.size - 2 + 1 = tokens.size - 1 := by omega
    rw [hidx] at d1
    have d2 : tokens.toList.drop (tokens.size - 1)
        = tokens.toList[tokens.size - 1]'hbl :: tokens.toList.drop (tokens.size - 1 + 1) :=
      List.drop_eq_getElem_cons hbl
    have hidx2 : tokens.size - 1 + 1 = tokens.size := by omega
    rw [hidx2] at d2
    have d3 : tokens.toList.drop tokens.size = [] := by rw [← h_len, List.drop_length]
    rw [d1, d2, d3]
  -- the body window `take (size-2)` splits as `take 2 ++ interior`
  have h_take2_eq : (tokens.toList.take (tokens.size - 2)).take 2 = tokens.toList.take 2 := by
    rw [List.take_take]; congr 1; omega
  have h_interior_decomp : tokens.toList.take (tokens.size - 2)
      = tokens.toList.take 2 ++ (tokens.toList.take (tokens.size - 2)).drop 2 := by
    rw [← h_take2_eq, List.take_append_drop]
  -- the whole list = (take 2 ++ interior) ++ suffix
  have h_whole : tokens.toList
      = (tokens.toList.take 2 ++ (tokens.toList.take (tokens.size - 2)).drop 2)
        ++ tokens.toList.drop (tokens.size - 2) := by
    rw [← h_interior_decomp, List.take_append_drop]
  -- fold piecewise: `[` pushes `true`, interior frames back to `[true]`, `]` pops to `[]`
  show btFold (some []) tokens.toList = some []
  rw [h_whole, btFold_append, btFold_append]
  have hf2 : btFold (some []) (tokens.toList.take 2) = some [true] := by
    rw [h_take2]
    have hs0 : btStep (tokens.toList[0]'hb0) [] = some [] := by simp only [btStep, e0]
    have hs1 : btStep (tokens.toList[1]'hb1) [] = some [true] := by simp only [btStep, e1]
    rw [btFold_cons_some, hs0, btFold_cons_some, hs1]; rfl
  rw [hf2, WellTyped_frame _ [true] h_wt_interior, h_suf]
  have hse : btStep (tokens.toList[tokens.size - 2]'hbe) [true] = some [] := by simp only [btStep, ee]
  have hss : btStep (tokens.toList[tokens.size - 1]'hbl) [] = some [] := by simp only [btStep, el]
  rw [btFold_cons_some, hse, btFold_cons_some, hss]; rfl

/-- **The whole-stream fold-totality `h_fold_total`, discharged GENERALLY from the emit context** —
    `(i'-b-B2c-(d)-seqFoldTotal-of-context)`, retiring residual **(2)** of `seqHRec_of_root_and_context`
    (R441) — the `h_fold_total : ∀ m, ∃ s, btFold (some []) (tokens.toList.take m) = some s` slot.  This
    is the generic tail the satisfiability probe `seqFoldTotal_satisfiable_on_real_output` already had:
    `WellTyped_prefix_some` turns whole-stream `WellTyped tokens.toList` (now produced GENERALLY by
    `seqWholeStreamWellTyped`, axiom-clean) into fold-totality at EVERY prefix, since every prefix of a
    `WellTyped` list folds to `some` (never underflows).  Axiom-clean (no `native_decide`); references no
    sorry site, frontier sorry count unchanged at 4. -/
theorem seqFoldTotal_of_context
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w) :
    ∀ m, ∃ s, btFold (some []) (tokens.toList.take m) = some s := by
  have h_wt := seqWholeStreamWellTyped items tokens h_scan h_ne h_all_block
  intro m
  exact WellTyped_prefix_some (tokens.toList.take m) (tokens.toList.drop m)
    (by rw [List.take_append_drop]; exact h_wt)

/-- **The floored seq `h_seq_rec` producer over the EMIT context — residual (2) now discharged** —
    `(i'-b-B2c-(d)-seqHRec-of-root-and-emit)`.  `seqHRec_of_root_and_context` (R441) reduced the
    seq-side `h_seq_rec` to FOUR named residuals; this wires `seqFoldTotal_of_context` into its
    `h_fold_total` slot ([[ref-reduction-by-import]] — the import RETYPES the residual from owed to
    discharged), so the seq producer now needs only THREE: **(1)** the hard root carrier
    `SeqInteriorSeparators tokens 2 (size-2)` (the `desc` descent provider), **(3)** `h_wt_outer`
    (available at the consume site as the interior `WellTyped`), **(4)** the emit context
    (`h_scan`/`h_ne`/`h_all_block`).  Verified-but-unconsumed until the root carrier lands; references
    no sorry site, frontier sorry count unchanged at 4. -/
theorem seqHRec_of_root_and_emit
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w)
    (h_wt_outer : WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2))
    (h_root_carrier : SeqInteriorSeparators tokens 2 (tokens.size - 2)) :
    ∀ lo hi, 2 ≤ lo → lo < hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowSequenceEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowSequenceStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      RecSeqBody ((tokens.toList.take hi).drop lo) :=
  seqHRec_of_root_and_context items tokens h_scan h_ne h_all_block h_wt_outer
    (seqFoldTotal_of_context items tokens h_scan h_ne h_all_block) h_root_carrier

/-- **The SEQ half of `FlowSubrangesOk` collapses to the SINGLE root carrier** —
    `(i'-b-B2c-(d)-flowSubrangesOk-of-seqRoot-and-map)`, R512, the critical-path RECONCILIATION that
    fixes the position of the genuine remaining work.  It folds the entire discharged seq chain into the
    actual `FlowSubrangesOk` consumer ([[ref-fold-consumer-chain-to-producer-contract]] at the
    contract level): it composes `flowSubrangesOk_of_window_producers` (the locator-pair assembler) with
    `seqHRec_of_root_and_emit` in its `h_seq_rec` slot — a DIRECT substitution, since R440 made the two
    universals textually identical.  So the whole seq side of the `FlowSubrangesOk tokens` residual
    (`NonemptyStructure.lean:11208`) is now discharged from **the single hypothesis `h_root_carrier`**
    (`SeqInteriorSeparators tokens 2 (size-2)`) plus the emit context + boundary facts already in scope
    at the sorry site.  The map side is left as its seven raw per-window producers (`h_map_rec` + the six
    grammar facts) — it is NOT yet reduced to a root carrier, so this brick records the seq/map ASYMMETRY:
    the seq axis is one carrier away from done; the map axis still owes its whole producer family.

    **The finding it pins** (the reason this is the right brick now, not the R510/R511 driver line).
    Tracing the actual critical path shows the carrier-based recursion `seqWindowRecSeqBody_seq_general`
    (R415) + the R432–R441 emit/fold-totality chain ALREADY close the seq navigator end-to-end — given
    the root carrier.  The width-recursion DRIVER `recseqbody_navigator_driver` (R510) and its extracted
    `recseqbody_seq_descend_tail` (R511) are a *parallel* modular re-derivation of R415's inlined `step`;
    correct, but OFF this critical path — building `locate` and re-typing the driver would re-prove what
    R415 already delivers.  So the sole genuine open seq residual is the root carrier
    `SeqInteriorSeparators tokens 2 (size-2)` = `seqRoot_seqInteriorSeparators` fed its `desc` descent
    provider (the hard B2 brick: `seqEnclosingOpener_of_gate` LOCATE + `seqDescent_provider_of_gate`
    ASSEMBLE, the carrier riding the recursion via ROUTE A).  This brick makes that precise by exhibiting
    the one statement in which `h_root_carrier` is the ONLY seq-side hypothesis left.

    Verified-but-unconsumed until the root carrier + the map producers land: pure composition of landed
    lemmas (`flowSubrangesOk_of_window_producers` ∘ `seqHRec_of_root_and_emit`), references no sorry site,
    frontier sorry count unchanged at 4; axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. -/
theorem flowSubrangesOk_of_seqRoot_and_map_producers
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w)
    (h_t0 : tokens[0]!.val = .streamStart)
    (h_tlast : tokens[tokens.size - 1]!.val = .streamEnd)
    (h_wt_outer : WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2))
    (h_root_carrier : SeqInteriorSeparators tokens 2 (tokens.size - 2))
    (h_map_rec : ∀ lo hi, 2 ≤ lo → lo < hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      RecMapBody ((tokens.toList.take hi).drop lo))
    (h_key_content : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .key →
        k + 1 < hi ∧ isFlowContentStart tokens[k + 1]!.val)
    (h_key_scalar_value : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .key →
        (∃ c s, tokens[k + 1]!.val = .scalar c s) →
        k + 2 < hi ∧ tokens[k + 2]!.val = .value)
    (h_value_content : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .value →
        k + 1 < hi ∧ isFlowContentStart tokens[k + 1]!.val)
    (h_value_scalar_succ : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .value →
        (∃ c s, tokens[k + 1]!.val = .scalar c s) →
        k + 2 ≤ hi ∧
        (tokens[k + 2]!.val = .flowEntry ∨
         (tokens[k + 2]!.val = .flowMappingEnd ∧ k + 2 = hi)))
    (h_key_bracket_succ : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      ∀ k j, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .key →
        k + 1 < j → j < hi →
        flowBracketDelta tokens[j]!.val = -1 →
        flowBracketBalance tokens lo (j + 1) = 0 →
        j + 1 < hi ∧ tokens[j + 1]!.val = .value)
    (h_value_bracket_succ : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
      ∀ k j, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .value →
        k + 1 < j → j < hi →
        flowBracketDelta tokens[j]!.val = -1 →
        flowBracketBalance tokens lo (j + 1) = 0 →
        j + 1 ≤ hi ∧
        (tokens[j + 1]!.val = .flowEntry ∨
         (tokens[j + 1]!.val = .flowMappingEnd ∧ j + 1 = hi))) :
    FlowSubrangesOk tokens :=
  flowSubrangesOk_of_window_producers tokens h_t0 h_tlast h_wt_outer
    (seqHRec_of_root_and_emit items tokens h_scan h_ne h_all_block h_wt_outer h_root_carrier)
    h_map_rec h_key_content h_key_scalar_value h_value_content h_value_scalar_succ
    h_key_bracket_succ h_value_bracket_succ

/-! ### The MAP fold cluster — toward `mapHRec_of_root_and_emit` (brick (2))

The seq half of `FlowSubrangesOk` now rides on the single carrier
`SeqInteriorSeparators tokens 2 (size-2)` via `seqHRec_of_root_and_emit` (`:6771`), whose context
inputs are discharged by `seqWholeStreamWellTyped` (`:6665`) + `seqFoldTotal_of_context` (`:6751`).
The MAP half still rides into the consumer as its seven raw per-window producers (the recorded
asymmetry).  Brick (2) builds the map fold `mapHRec_of_root_and_emit` that will collapse the
`h_map_rec` (`RecMapBody`) slot onto the map root carrier, mirroring the seq fold cluster.

This first sub-brick lands the fold cluster's CONTEXT residual — the `h_fold_total` slot every
windowFacts provider needs — as the `some false`/`{`/`}` dual of the seq context pair.  Both proofs
are collection-agnostic below the boundary: `mapFoldTotal_of_context` reuses `WellTyped_prefix_some`
verbatim (fold-totality at every prefix follows from whole-stream `WellTyped`), and
`mapWholeStreamWellTyped` is the seq whole-stream fold with `btStep`'s `[`-push-`true` swapped for the
`{`-push-`false` convention (`WellBracketed.lean:1540-1541`): the four boundary tokens are
`streamStart :: .flowMappingStart :: interior ++ [.flowMappingEnd, streamEnd]`, the interior frames
back to `[false]` by `WellTyped_frame`, and `.flowMappingEnd` pops the matching `false`.

AXIOM NOTE — the seq/map asymmetry reaches the axiom layer.  Unlike `seqWholeStreamWellTyped`
(`[propext, Classical.choice, Quot.sound]`, clean), both map lemmas carry `sorryAx` —
`[propext, sorryAx, Classical.choice, Quot.sound]` — inherited via
`scanFiltered_emitMap_nonempty_structure`, whose `ParseEntryFlowMapOk` conjunct still discharges the
frontier residual `FlowSubrangesOk tokens := sorry` (`NonemptyStructure.lean:11208`, sorry #4) INLINE.
The seq structure lemma sheds this only because R442 RELOCATED its twin sorry out to
`parseStream_emitSequence`; the map structure lemma never got that relocation, so the WHOLE map
context-provider family (`mapWindowOpenerAdj_of_emit`, …, and now these) carries `sorryAx`.  This adds
NO NEW sorry — it routes through the existing #4 — and the `sorryAx` vanishes the moment the root
carriers close #4.  Frontier sorry count unchanged at 4. -/

/-- **Whole-stream well-typedness from the MAP emit context** — the `some false`/`{`/`}` dual of
    `seqWholeStreamWellTyped` (`:6665`).  Reads the emitted+filtered stream off
    `scanFiltered_emitMap_nonempty_structure` as `streamStart :: .flowMappingStart :: interior ++
    [.flowMappingEnd, streamEnd]` (four boundary tokens + `size ≥ 7` + the interior `WellTyped`), and
    folds piecewise: `btStep` is the identity on `streamStart`/`streamEnd`, pushes `false` on `{`, the
    interior returns the stack to `[false]` by `WellTyped_frame` of `h_wt_interior`, then `}` pops the
    matching `false` back to `[]`.  No `native_decide`.  Carries `sorryAx` (`[propext, sorryAx,
    Classical.choice, Quot.sound]`) inherited from `scanFiltered_emitMap_nonempty_structure`'s inline
    sorry #4 — see the cluster AXIOM NOTE above; adds no NEW sorry.  Verified-but-unconsumed until the
    map fold lands; frontier sorry count unchanged at 4. -/
theorem mapWholeStreamWellTyped
    (pairs : Array (YamlValue × YamlValue)) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}") = .ok tokens)
    (h_ne : pairs.toList ≠ [])
    (h_all_k_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowSavedKeyBlock p.1)
    (h_all_v_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowBlock p.2) :
    WellTyped tokens.toList := by
  obtain ⟨h_sz7, h_t0, h_tlast, h_t1, h_close, _h_key, _h_fe_pattern,
          _h_outer_bal, _h_dyck, h_wt_interior, _h_pnok, _h_body_opener, _h_body_separator⟩ :=
    scanFiltered_emitMap_nonempty_structure pairs tokens h_scan h_ne h_all_k_block h_all_v_block
  have h_len : tokens.toList.length = tokens.size := Array.length_toList
  -- the four boundary indices are in range
  have hb0 : 0 < tokens.toList.length := by rw [h_len]; omega
  have hb1 : 1 < tokens.toList.length := by rw [h_len]; omega
  have hbe : tokens.size - 2 < tokens.toList.length := by rw [h_len]; omega
  have hbl : tokens.size - 1 < tokens.toList.length := by rw [h_len]; omega
  -- their token VALUES (bridged from the `tokens[_]!` boundary facts)
  have e0 : (tokens.toList[0]'hb0).val = .streamStart := by
    have hb : tokens.toList[0]'hb0 = tokens[0]! := by
      rw [Array.getElem_toList, getElem!_pos tokens 0 (by omega)]
    rw [hb]; exact h_t0
  have e1 : (tokens.toList[1]'hb1).val = .flowMappingStart := by
    have hb : tokens.toList[1]'hb1 = tokens[1]! := by
      rw [Array.getElem_toList, getElem!_pos tokens 1 (by omega)]
    rw [hb]; exact h_t1
  have ee : (tokens.toList[tokens.size - 2]'hbe).val = .flowMappingEnd := by
    have hb : tokens.toList[tokens.size - 2]'hbe = tokens[tokens.size - 2]! := by
      rw [Array.getElem_toList, getElem!_pos tokens (tokens.size - 2) (by omega)]
    rw [hb]; exact h_close
  have el : (tokens.toList[tokens.size - 1]'hbl).val = .streamEnd := by
    have hb : tokens.toList[tokens.size - 1]'hbl = tokens[tokens.size - 1]! := by
      rw [Array.getElem_toList, getElem!_pos tokens (tokens.size - 1) (by omega)]
    rw [hb]; exact h_tlast
  -- prefix `take 2` = [streamStart, `{`]
  have h_take2 : tokens.toList.take 2 = [tokens.toList[0]'hb0, tokens.toList[1]'hb1] := by
    have step1 : tokens.toList.take 2 = tokens.toList.take 1 ++ [tokens.toList[1]'hb1] :=
      List.take_succ_eq_append_getElem hb1
    have step0 : tokens.toList.take 1 = tokens.toList.take 0 ++ [tokens.toList[0]'hb0] :=
      List.take_succ_eq_append_getElem hb0
    rw [step1, step0]; rfl
  -- suffix `drop (size-2)` = [`}`, streamEnd]
  have h_suf : tokens.toList.drop (tokens.size - 2)
      = [tokens.toList[tokens.size - 2]'hbe, tokens.toList[tokens.size - 1]'hbl] := by
    have d1 : tokens.toList.drop (tokens.size - 2)
        = tokens.toList[tokens.size - 2]'hbe :: tokens.toList.drop (tokens.size - 2 + 1) :=
      List.drop_eq_getElem_cons hbe
    have hidx : tokens.size - 2 + 1 = tokens.size - 1 := by omega
    rw [hidx] at d1
    have d2 : tokens.toList.drop (tokens.size - 1)
        = tokens.toList[tokens.size - 1]'hbl :: tokens.toList.drop (tokens.size - 1 + 1) :=
      List.drop_eq_getElem_cons hbl
    have hidx2 : tokens.size - 1 + 1 = tokens.size := by omega
    rw [hidx2] at d2
    have d3 : tokens.toList.drop tokens.size = [] := by rw [← h_len, List.drop_length]
    rw [d1, d2, d3]
  -- the body window `take (size-2)` splits as `take 2 ++ interior`
  have h_take2_eq : (tokens.toList.take (tokens.size - 2)).take 2 = tokens.toList.take 2 := by
    rw [List.take_take]; congr 1; omega
  have h_interior_decomp : tokens.toList.take (tokens.size - 2)
      = tokens.toList.take 2 ++ (tokens.toList.take (tokens.size - 2)).drop 2 := by
    rw [← h_take2_eq, List.take_append_drop]
  -- the whole list = (take 2 ++ interior) ++ suffix
  have h_whole : tokens.toList
      = (tokens.toList.take 2 ++ (tokens.toList.take (tokens.size - 2)).drop 2)
        ++ tokens.toList.drop (tokens.size - 2) := by
    rw [← h_interior_decomp, List.take_append_drop]
  -- fold piecewise: `{` pushes `false`, interior frames back to `[false]`, `}` pops to `[]`
  show btFold (some []) tokens.toList = some []
  rw [h_whole, btFold_append, btFold_append]
  have hf2 : btFold (some []) (tokens.toList.take 2) = some [false] := by
    rw [h_take2]
    have hs0 : btStep (tokens.toList[0]'hb0) [] = some [] := by simp only [btStep, e0]
    have hs1 : btStep (tokens.toList[1]'hb1) [] = some [false] := by simp only [btStep, e1]
    rw [btFold_cons_some, hs0, btFold_cons_some, hs1]; rfl
  rw [hf2, WellTyped_frame _ [false] h_wt_interior, h_suf]
  have hse : btStep (tokens.toList[tokens.size - 2]'hbe) [false] = some [] := by simp only [btStep, ee]
  have hss : btStep (tokens.toList[tokens.size - 1]'hbl) [] = some [] := by simp only [btStep, el]
  rw [btFold_cons_some, hse, btFold_cons_some, hss]; rfl

/-- **The whole-stream fold-totality `h_fold_total`, discharged from the MAP emit context** — the dual
    of `seqFoldTotal_of_context` (`:6751`).  Fold-totality is collection-AGNOSTIC: `WellTyped_prefix_some`
    turns whole-stream `WellTyped tokens.toList` (now produced by `mapWholeStreamWellTyped`) into
    fold-totality at EVERY prefix, since every prefix of a `WellTyped` list folds to `some` (never
    underflows).  The proof body is byte-identical to the seq twin — only the whole-stream producer it
    calls differs.  Carries `sorryAx` via `mapWholeStreamWellTyped` (the map structure lemma's inline
    sorry #4 — see the cluster AXIOM NOTE above); adds no NEW sorry, frontier count unchanged at 4. -/
theorem mapFoldTotal_of_context
    (pairs : Array (YamlValue × YamlValue)) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}") = .ok tokens)
    (h_ne : pairs.toList ≠ [])
    (h_all_k_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowSavedKeyBlock p.1)
    (h_all_v_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowBlock p.2) :
    ∀ m, ∃ s, btFold (some []) (tokens.toList.take m) = some s := by
  have h_wt := mapWholeStreamWellTyped pairs tokens h_scan h_ne h_all_k_block h_all_v_block
  intro m
  exact WellTyped_prefix_some (tokens.toList.take m) (tokens.toList.drop m)
    (by rw [List.take_append_drop]; exact h_wt)

/-- **The 7-guard `windowFacts`/`h_seq_rec` universal is UNSATISFIABLE — a cross-matched false window** —
    `(i'-b-B2c-(d)-windowFacts-false-window)`, R433, the machine-checked refutation that REDIRECTS the
    "discharge the three `windowFacts` primitives" plan ([[ref-probe-deferred-universal-before-producing]] /
    [[ref-minimal-pair-extracts-the-gate]], the R392-style discipline).  The `windowFacts` provider and
    `flowSubrangesOk_of_window_producers`'s `h_seq_rec` both quantify over EVERY window `[lo, hi)` gated only
    by the SEVEN bracket-shape facts (`2 ≤ lo`, `lo < hi`, `hi ≤ size-2`, `hi < size`, `tokens[hi] =
    .flowSequenceEnd`, `flowBracketBalance lo hi = 0`, `tokens[lo-1] = .flowSequenceStart`).  Those guards
    do NOT pin a MATCHED bracket pair: `tokens[lo-1]` and `tokens[hi]` may close DIFFERENT brackets with
    `balance lo hi = 0` holding only by COINCIDENCE across a separator.

    Witness (`native_decide` on real scanned output): `[[],[a]]` scans to `streamStart, [, [, ], `,`, [, a,
    ], ], streamEnd` (size 10).  The window `[3, 7)` satisfies ALL SEVEN guards — `tokens[2] =
    .flowSequenceStart`, `tokens[7] = .flowSequenceEnd`, `flowBracketBalance tokens 3 7 = 0` — yet
    `flowBracketBalance tokens 3 4 = -1` (its head `tokens[3]` is the FIRST element's CLOSE `]`, delta `-1`),
    so the Dyck floor UNDERFLOWS and `FlowBodyWindow tokens 3 7` is FALSE.  `[3, 7)` is a CROSS-MATCHED
    window: `tokens[2] = [` is matched by `tokens[8]`, `tokens[7] = ]` matches `tokens[5]` — the guards
    paired the wrong opener/closer.

    **The fix direction** (the genuine remaining work, redirecting R389/R390/R432's "supply `h_win_dyck`
    from whole-stream well-bracketedness" framing): `h_win_dyck` is NOT a global-restriction primitive — it
    is the GUARD that DEFINES a genuine window.  Add the Dyck floor `∀ i ∈ [lo, hi], balance lo i ≥ 0` as an
    8th guard to `h_seq_rec`/`windowFacts` (it EXCLUDES every cross-matched false window and makes
    `FlowBodyWindow.dyck` a trivial pass-through).  This is the [[ref-end-free-gate-underdetermines-close]] /
    [[ref-probe-provider-head-blind-gate]] family: an endpoint + total-balance gate underdetermines the
    matched pair; the interior floor is the discriminator.  This lemma contains the `ofReduceBool` axiom
    (`native_decide`), off the `universal_roundtrip` path. -/
theorem seqWindowFacts_false_window
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered
        ("[" ++ emit.emitList
          [YamlValue.sequence .flow #[],
           YamlValue.sequence .flow #[YamlValue.scalar { content := "a", style := .plain }]]
        ++ "]") = .ok tokens) :
    (2 ≤ 3 ∧ (3 : Nat) < 7 ∧ 7 ≤ tokens.size - 2 ∧ 7 < tokens.size ∧
      tokens[7]!.val = .flowSequenceEnd ∧ flowBracketBalance tokens 3 7 = 0 ∧
      tokens[3 - 1]!.val = .flowSequenceStart) ∧
    ¬ FlowBodyWindow tokens 3 7 := by
  have key : ∀ {α : Type} (g : Array (Positioned YamlToken) → α) (a : α),
      (Scanner.scanFiltered
          ("[" ++ emit.emitList
            [YamlValue.sequence .flow #[],
             YamlValue.sequence .flow #[YamlValue.scalar { content := "a", style := .plain }]]
          ++ "]")).toOption.map g = some a →
        g tokens = a := by
    intro α g a e; rw [h] at e; exact Option.some.inj e
  have hsz : tokens.size = 10 := key (fun t => t.size) 10 (by native_decide)
  have h7 : tokens[7]!.val = .flowSequenceEnd :=
    key (fun t => t[7]!.val) .flowSequenceEnd (by native_decide)
  have h2 : tokens[3 - 1]!.val = .flowSequenceStart :=
    key (fun t => t[3 - 1]!.val) .flowSequenceStart (by native_decide)
  have hbal : flowBracketBalance tokens 3 7 = 0 :=
    key (fun t => flowBracketBalance t 3 7) 0 (by native_decide)
  have hfloor : flowBracketBalance tokens 3 4 = -1 :=
    key (fun t => flowBracketBalance t 3 4) (-1) (by native_decide)
  refine ⟨⟨by omega, by omega, by omega, by omega, h7, hbal, h2⟩, ?_⟩
  intro hw
  have hd := hw.dyck 4 (by omega) (by omega)
  rw [hfloor] at hd
  omega

/-- **The floor guard on `FlowSubrangesOk.seq` is the load-bearing fix: it REJECTS the cross-matched
    window the un-floored contract wrongly admitted** — `(i'-b-B2c-(d)-flowSubrangesOk-floor-rejects)`,
    R439 (STEP C), the machine-checked confirmation that the floor lands the repair at the parser contract.
    Until R435–R439 this lemma proved the OPPOSITE conclusion `¬ FlowSubrangesOk tokens`: the un-floored
    `.seq` field quantified over EVERY window `[lo, hi)` with only FIVE bracket-shape guards (`lo ≤ hi`,
    `hi < size`, `tokens[hi] = .flowSequenceEnd`, `flowBracketBalance lo hi = 0`,
    `tokens[lo-1] = .flowSequenceStart`) and NO interior floor, so on `[[],[a]]` the cross-matched window
    `[3, 7)` ([[ref-bracket-guards-admit-cross-matched-window]]) satisfied all five, `.seq` fired, and
    `SeqBodyProps.content_start` forced `isFlowContentStart .flowSequenceEnd` — FALSE.  The un-floored
    contract was therefore itself FALSE on real emitted output, and the two sorry sites
    `have h_subranges : FlowSubrangesOk tokens := sorry` owed an unachievable goal.

    STEP C added the interior Dyck floor `∀ i ∈ [lo, hi], flowBracketBalance tokens lo i ≥ 0` as a SIXTH
    guard on `FlowSubrangesOk.seq` (and `.map`).  The cross-matched window `[3, 7)` now FAILS that guard:
    its head `tokens[3]` is the first element's CLOSE `]` (delta `-1`), so `flowBracketBalance tokens 3 4 =
    -1 < 0` — the floor UNDERFLOWS at `i = 4`.  `.seq` can no longer be invoked on `[3, 7)`, so the
    contradiction route is severed and `FlowSubrangesOk tokens` is once more SATISFIABLE (TRUE) for the
    well-formed `[[],[a]]`.  This lemma proves exactly that: the window passes all five boundary/balance
    guards yet the floor guard is FALSE on it — the floor is the discriminator that fences out the
    mis-nested pairing.  It is the `FlowSubrangesOk`-contract-level analogue of the producer-layer
    `seqWindowFacts_false_window` (which rejects the same window via `FlowBodyWindow.dyck`); the
    [[ref-end-free-gate-underdetermines-close]] / [[ref-probe-provider-head-blind-gate]] discriminator now
    lives at the parser contract's own `.seq` guard.  Contains the `ofReduceBool` axiom (`native_decide`),
    off the `universal_roundtrip` path. -/
theorem flowSubrangesOk_seq_floor_rejects_crossMatched_window
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered
        ("[" ++ emit.emitList
          [YamlValue.sequence .flow #[],
           YamlValue.sequence .flow #[YamlValue.scalar { content := "a", style := .plain }]]
        ++ "]") = .ok tokens) :
    ((3 : Nat) ≤ 7 ∧ (7 : Nat) < tokens.size ∧
      tokens[7]!.val = .flowSequenceEnd ∧ flowBracketBalance tokens 3 7 = 0 ∧
      tokens[3 - 1]!.val = .flowSequenceStart) ∧
    ¬ (∀ i, 3 ≤ i → i ≤ 7 → flowBracketBalance tokens 3 i ≥ 0) := by
  have key : ∀ {α : Type} (g : Array (Positioned YamlToken) → α) (a : α),
      (Scanner.scanFiltered
          ("[" ++ emit.emitList
            [YamlValue.sequence .flow #[],
             YamlValue.sequence .flow #[YamlValue.scalar { content := "a", style := .plain }]]
          ++ "]")).toOption.map g = some a →
        g tokens = a := by
    intro α g a e; rw [h] at e; exact Option.some.inj e
  have hsz : tokens.size = 10 := key (fun t => t.size) 10 (by native_decide)
  have h7 : tokens[7]!.val = .flowSequenceEnd :=
    key (fun t => t[7]!.val) .flowSequenceEnd (by native_decide)
  have h2 : tokens[3 - 1]!.val = .flowSequenceStart :=
    key (fun t => t[3 - 1]!.val) .flowSequenceStart (by native_decide)
  have hbal : flowBracketBalance tokens 3 7 = 0 :=
    key (fun t => flowBracketBalance t 3 7) 0 (by native_decide)
  have hfloor : flowBracketBalance tokens 3 4 = -1 :=
    key (fun t => flowBracketBalance t 3 4) (-1) (by native_decide)
  refine ⟨⟨by omega, by omega, h7, hbal, h2⟩, ?_⟩
  intro hw
  have hd := hw 4 (by omega) (by omega)
  rw [hfloor] at hd
  omega

/-- **The Dyck-FREE MAP grammar producers are FALSE at a cross-matched window — they too need the
    interior Dyck floor** — `(i'-b-B2c-(d)-map-grammar-false-window)`, the MAP twin of
    `seqWindowFacts_false_window` (`:7183`) and the probe that REDIRECTS brick (3).  The next critical-path
    brick `flowSubrangesOk_of_seqRoot_and_mapRoot` (the map twin of R512's `flowSubrangesOk_of_seqRoot_and_map_producers`)
    aims to discharge the six `flowSubrangesOk_of_window_producers` MAP grammar producers
    (`h_key_content` … `h_value_bracket_succ`, `NonemptyStructure.lean:10434+`) from the single map root
    carrier `MapInteriorSeparators tokens 2 (size-2)`.  But those six slots carry only the SEVEN
    bracket-shape guards (`2 ≤ lo`, `lo ≤ hi`, `hi ≤ size-2`, `hi < size`, `tokens[hi] = .flowMappingEnd`,
    `flowBracketBalance lo hi = 0`, `tokens[lo-1] = .flowMappingStart`) — and NOT the interior Dyck floor.
    Exactly as R433 found for `h_seq_rec` ([[ref-bracket-guards-admit-cross-matched-window]]), those seven
    do NOT pin a MATCHED `{`…`}` pair, so a CROSS-MATCHED window passes them while the carrier's
    `MapTypedInterior` gate (which needs Dyck) does not hold — the carrier cannot fire there, and the
    R515/R518 projections (`mapGrammarFacts_of_mapRoot` / `mapWindow_grammarFacts_general`) are inapplicable.

    **Machine-checked witness** (`native_decide` on real scanned output).  `{a: {b: c}, d: {e: f}}` scans
    to (filtered, size 23):

        0:SS 1:{ 2:KEY 3:a 4:VAL 5:{ 6:KEY 7:b 8:VAL 9:c 10:} 11:, 12:KEY 13:d 14:VAL 15:{ 16:KEY 17:e 18:VAL 19:f 20:} 21:} 22:SE

    The window `[6, 20)` satisfies all SEVEN guards — `tokens[5] = .flowMappingStart` (the FIRST inner map's
    opener), `tokens[20] = .flowMappingEnd` (the SECOND inner map's closer), `flowBracketBalance 6 20 = 0` —
    yet it is CROSS-MATCHED: `{` at 5 truly matches `}` at 10, `}` at 20 truly matches `{` at 15.  Its
    interior Dyck floor UNDERFLOWS at `i = 11` (`flowBracketBalance 6 11 = -1`, the head `tokens[6..10]`
    closes the inner `{b: c}`).  And the producer fact is not merely Dyck-unprovable but FALSE: at the
    depth-`0` value `tokens[8] = .value` (`flowBracketBalance 6 8 = 0`) with scalar successor `tokens[9] = c`,
    the `h_value_scalar_succ` conclusion demands `tokens[10]` be `.flowEntry` or `.flowMappingEnd` AT `hi = 20`,
    but `tokens[10] = .flowMappingEnd` with `10 ≠ 20` — it is the INNER map's close, not a separator and not
    THIS window's close.  So the Dyck-free `h_value_scalar_succ` universal is UNSATISFIABLE.

    **The redirect** (the genuine remaining work for brick (3), [[ref-minimal-pair-extracts-the-gate]]).  The
    six grammar producers must gain the interior Dyck floor `∀ i, lo ≤ i → i ≤ hi → flowBracketBalance lo i ≥ 0`
    as an EIGHTH guard — the same fix R433 applied to `h_seq_rec` and R439 to `FlowSubrangesOk.{seq,map}`.
    With it, cross-matched windows are excluded, `MapTypedInterior` becomes satisfiable, and the carrier
    projections fire.  The split is SHARP: the two CONTENT-START facts (`h_key_content`/`h_value_content`) are
    Dyck-INDEPENDENT (their `isFlowContentStart tokens[k+1]` conjunct is an emitter-global property of every
    `.key`/`.value`, and `k+1 < hi` is forced by the `.flowMappingEnd` closer) so they survive cross-matching;
    only the four BOUNDARY-referencing facts (the scalar/bracket successors, which name `hi` via `k+2 = hi` /
    `j+1 = hi` or pin an interior separator) genuinely need Dyck.  Contains the `ofReduceBool` axiom
    (`native_decide`), off the `universal_roundtrip` path; references no sorry site, frontier sorry count
    unchanged at 4. -/
theorem mapGrammarFacts_false_window
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered
        ("{" ++ emit.emitPairList
          [(YamlValue.scalar { content := "a", style := .plain },
            YamlValue.mapping .flow #[(YamlValue.scalar { content := "b", style := .plain },
                                       YamlValue.scalar { content := "c", style := .plain })]),
           (YamlValue.scalar { content := "d", style := .plain },
            YamlValue.mapping .flow #[(YamlValue.scalar { content := "e", style := .plain },
                                       YamlValue.scalar { content := "f", style := .plain })])]
        ++ "}") = .ok tokens) :
    (2 ≤ 6 ∧ (6 : Nat) ≤ 20 ∧ 20 ≤ tokens.size - 2 ∧ 20 < tokens.size ∧
      tokens[20]!.val = .flowMappingEnd ∧ flowBracketBalance tokens 6 20 = 0 ∧
      tokens[6 - 1]!.val = .flowMappingStart) ∧
    (flowBracketBalance tokens 6 8 = 0 ∧ tokens[8]!.val = .value) ∧
    ¬ ((8 : Nat) + 2 ≤ 20 ∧
        (tokens[8 + 2]!.val = .flowEntry ∨
         (tokens[8 + 2]!.val = .flowMappingEnd ∧ (8 : Nat) + 2 = 20))) ∧
    ¬ (∀ i, 6 ≤ i → i ≤ 20 → flowBracketBalance tokens 6 i ≥ 0) := by
  have key : ∀ {α : Type} (g : Array (Positioned YamlToken) → α) (a : α),
      (Scanner.scanFiltered
          ("{" ++ emit.emitPairList
            [(YamlValue.scalar { content := "a", style := .plain },
              YamlValue.mapping .flow #[(YamlValue.scalar { content := "b", style := .plain },
                                         YamlValue.scalar { content := "c", style := .plain })]),
             (YamlValue.scalar { content := "d", style := .plain },
              YamlValue.mapping .flow #[(YamlValue.scalar { content := "e", style := .plain },
                                         YamlValue.scalar { content := "f", style := .plain })])]
          ++ "}")).toOption.map g = some a →
        g tokens = a := by
    intro α g a e; rw [h] at e; exact Option.some.inj e
  have h20 : tokens[20]!.val = .flowMappingEnd :=
    key (fun t => t[20]!.val) .flowMappingEnd (by native_decide)
  have h5 : tokens[6 - 1]!.val = .flowMappingStart :=
    key (fun t => t[6 - 1]!.val) .flowMappingStart (by native_decide)
  have hsz : tokens.size = 23 := key (fun t => t.size) 23 (by native_decide)
  have hbal : flowBracketBalance tokens 6 20 = 0 :=
    key (fun t => flowBracketBalance t 6 20) 0 (by native_decide)
  have hbal8 : flowBracketBalance tokens 6 8 = 0 :=
    key (fun t => flowBracketBalance t 6 8) 0 (by native_decide)
  have h8 : tokens[8]!.val = .value :=
    key (fun t => t[8]!.val) .value (by native_decide)
  have h10 : tokens[8 + 2]!.val = .flowMappingEnd :=
    key (fun t => t[8 + 2]!.val) .flowMappingEnd (by native_decide)
  have hfloor : flowBracketBalance tokens 6 11 = -1 :=
    key (fun t => flowBracketBalance t 6 11) (-1) (by native_decide)
  refine ⟨⟨by omega, by omega, by omega, by omega, h20, hbal, h5⟩, ⟨hbal8, h8⟩, ?_, ?_⟩
  · rw [h10]
    rintro ⟨-, hc⟩
    rcases hc with hc | ⟨-, hc⟩
    · simp at hc
    · omega
  · intro hd
    have hneg := hd 11 (by omega) (by omega)
    rw [hfloor] at hneg
    omega

/-- **The SEQ-head CONS three-arm dispatch of the locator's per-window step `h_step`** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-brick-d-seq-cons)`, R378, BRICK D (carved).  This is
    the maximal-risk slice of `h_step` the blueprint flagged ("the four-way `cases h_e` × HEAD/CONS
    tangle is the risk"): the CONS branch (`body = e ++ fe :: rest`) with a SEQ head
    (`e = op :: (interior ++ [cl])`, non-empty interior).  All THREE move arms fire here — LEAF
    (`a = off + 1`), DESCEND (`off + 1 < a < off + e.length`), ADVANCE (`off + e.length < a`) — wired to
    the landed seams `…step_leaf` (R367), `…step_descend` (R369), `…step_advance` (R371), with the
    boundary `a = off + e.length` excluded by C-ii (`…cons_boundary`, R377).

    Two findings the proof embodies.  (1) **The feared "close-position bridge" is the SEPARATOR bridge
    re-bracketed** ([[ref-rebracket-reuses-prefix-bridge]]): C-ii's `h_close` needs the head entry's
    CLOSE `cl` at `off + interior.length + 1`, which looked like a new positional read.  But re-associate
    `op :: (interior ++ [cl]) = (op :: interior) ++ cl :: rest'`; then `cl` is the FIRST token past the
    `(op :: interior)` prefix, so `nestedSeq_recseqentry_locate_sep_pos` (index = prefix length) reads it
    verbatim with `e := op :: interior` — no new bridge.  (2) **The dispatch is INLINE `omega`** (the
    `move_trichotomy` shape, R350) keyed on `g.win_lo` + the C-ii `h_ne`, avoiding a `Tests/Guards`
    dependency in the library.  The risky tangle landed in ONE pass because the arm seams were each sized
    to exactly their per-arm need: LEAF/DESCEND/ADVANCE consume `g`'s fields verbatim, the only
    reconciliation being the `e.length = interior.length + 2` length identity (one `simp`+`omega`).
    Verified-but-unconsumed until the full `h_step` assembles the HEAD branch + the scalar/map shapes;
    references no sorry site, frontier sorry count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_seq_cons_step
    (tokens : Array (Positioned YamlToken)) (a b off H : Nat)
    (body rest interior : List (Positioned YamlToken))
    (op cl fe : Positioned YamlToken)
    (g : SeqLocateGuard tokens a b off H body)
    (h_eq : body = (op :: (interior ++ [cl])) ++ fe :: rest)
    (h_op : op.val = .flowSequenceStart) (h_cl : cl.val = .flowSequenceEnd)
    (h_wb : WellBracketed interior) (h_rec : RecSeqBody interior)
    (h_fe : fe.val = .flowEntry) (h_rest : RecSeqBody rest) :
    (∃ lo op' cl' interior', lo + 1 = a ∧ a ≤ b ∧
      RecSeqEntry (op' :: (interior' ++ [cl'])) ∧
      op'.val = .flowSequenceStart ∧ interior' ≠ [] ∧
      (tokens.toList.take (b + 1)).drop lo = op' :: (interior' ++ [cl']))
    ∨ (∃ off' H' body', body'.length < body.length ∧
      SeqLocateGuard tokens a b off' H' body') := by
  -- head opener position
  have h_pref_head : body = op :: ((interior ++ [cl]) ++ fe :: rest) := by rw [h_eq]; rfl
  have h_off_open : tokens[off]!.val = .flowSequenceStart := by
    rw [nestedSeq_recseqentry_locate_head_pos tokens body ((interior ++ [cl]) ++ fe :: rest) op off H
      g.slice g.bound g.Hsz h_pref_head]
    exact h_op
  -- close position (via sep_pos with e := op :: interior, re-bracketing the entry), for the boundary
  have h_pref_close : body = (op :: interior) ++ cl :: (fe :: rest) := by rw [h_eq]; simp
  have h_close_tok : tokens[off + (op :: interior).length]! = cl :=
    nestedSeq_recseqentry_locate_sep_pos tokens body (fe :: rest) (op :: interior) cl off H
      g.slice g.bound g.Hsz h_pref_close
  have h_close_val : tokens[off + (op :: interior).length]!.val = .flowSequenceEnd := by
    rw [h_close_tok]; exact h_cl
  have hbl : body.length = interior.length + rest.length + 3 := by
    rw [h_eq]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have h_m_sz : off + (op :: interior).length < tokens.size := by
    have hb := g.bound; have hH := g.Hsz
    simp only [List.length_cons]
    omega
  have h_ne : a ≠ off + interior.length + 2 := by
    have hcb := nestedSeq_recseqentry_locate_cons_boundary tokens a b off H
      (off + (op :: interior).length) body g h_m_sz h_close_val
    simp only [List.length_cons] at hcb
    omega
  -- dispatch (the move trichotomy is pure length arithmetic, inlined)
  rcases (by have := g.win_lo; omega :
      (a = off + 1) ∨ (off + 1 < a ∧ a < off + interior.length + 2)
        ∨ (off + interior.length + 2 < a)) with h_leaf | ⟨h_d1, h_d2⟩ | h_adv
  · -- LEAF
    exact Or.inl (nestedSeq_recseqentry_locate_step_leaf tokens a b off H body g h_leaf h_off_open
      (nestedSeq_recseqentry_locate_leaf_off1_b tokens a b off H body g h_leaf))
  · -- DESCEND
    exact Or.inr (nestedSeq_recseqentry_locate_step_descend tokens a b off H body (fe :: rest)
      interior op cl g h_eq h_off_open h_wb h_rec h_d1 h_d2)
  · -- ADVANCE
    refine Or.inr (nestedSeq_recseqentry_locate_step_advance tokens a b off H body rest
      (op :: (interior ++ [cl])) fe g h_eq ?_ h_fe h_rest ?_ ?_)
    · exact RecSeqEntry.seq op cl interior h_op h_cl h_wb h_rec
    · rw [nestedSeq_recseqentry_locate_sep_pos tokens body rest (op :: (interior ++ [cl])) fe off H
        g.slice g.bound g.Hsz h_eq]
      exact h_fe
    · simp only [List.length_cons, List.length_append, List.length_nil]
      omega

/-- **The seqEmpty-head CONS dispatch of `h_step`** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-brick-d-seqempty-cons)`, R378, BRICK D (carved).  The
    empty-interior sibling of `nestedSeq_recseqentry_locate_seq_cons_step`: the head is an empty seq
    `[op, cl]` (`RecSeqEntry.seqEmpty`, `e.length = 2`), so only LEAF (`a = off + 1`) and ADVANCE
    (`off + 2 < a`) fire — DESCEND is structurally absent (no interior sub-window), its arm range
    `off + 1 < a < off + 2` empty by `omega`.  The boundary `a = off + 2` is again excluded by C-ii at
    the close `cl` (re-bracketed to `[op] ++ cl :: rest`, the `interior = []` case of the seq brick's
    move).  Same seams (`…step_leaf`, `…step_advance`); verified-but-unconsumed; frontier holds at 4. -/
theorem nestedSeq_recseqentry_locate_seqEmpty_cons_step
    (tokens : Array (Positioned YamlToken)) (a b off H : Nat)
    (body rest : List (Positioned YamlToken))
    (op cl fe : Positioned YamlToken)
    (g : SeqLocateGuard tokens a b off H body)
    (h_eq : body = (op :: ([] ++ [cl])) ++ fe :: rest)
    (h_op : op.val = .flowSequenceStart) (h_cl : cl.val = .flowSequenceEnd)
    (h_fe : fe.val = .flowEntry) (h_rest : RecSeqBody rest) :
    (∃ lo op' cl' interior', lo + 1 = a ∧ a ≤ b ∧
      RecSeqEntry (op' :: (interior' ++ [cl'])) ∧
      op'.val = .flowSequenceStart ∧ interior' ≠ [] ∧
      (tokens.toList.take (b + 1)).drop lo = op' :: (interior' ++ [cl']))
    ∨ (∃ off' H' body', body'.length < body.length ∧
      SeqLocateGuard tokens a b off' H' body') := by
  have h_pref_head : body = op :: (([] ++ [cl]) ++ fe :: rest) := by rw [h_eq]; rfl
  have h_off_open : tokens[off]!.val = .flowSequenceStart := by
    rw [nestedSeq_recseqentry_locate_head_pos tokens body (([] ++ [cl]) ++ fe :: rest) op off H
      g.slice g.bound g.Hsz h_pref_head]
    exact h_op
  have h_pref_close : body = [op] ++ cl :: (fe :: rest) := by rw [h_eq]; simp
  have h_close_tok : tokens[off + ([op] : List (Positioned YamlToken)).length]! = cl :=
    nestedSeq_recseqentry_locate_sep_pos tokens body (fe :: rest) [op] cl off H
      g.slice g.bound g.Hsz h_pref_close
  have h_close_val : tokens[off + ([op] : List (Positioned YamlToken)).length]!.val
      = .flowSequenceEnd := by
    rw [h_close_tok]; exact h_cl
  have hbl : body.length = rest.length + 3 := by
    rw [h_eq]; simp only [List.nil_append, List.length_append, List.length_cons, List.length_nil]
    omega
  have h_m_sz : off + ([op] : List (Positioned YamlToken)).length < tokens.size := by
    have hb := g.bound; have hH := g.Hsz
    simp only [List.length_cons, List.length_nil]
    omega
  have h_ne : a ≠ off + 2 := by
    have hcb := nestedSeq_recseqentry_locate_cons_boundary tokens a b off H
      (off + ([op] : List (Positioned YamlToken)).length) body g h_m_sz h_close_val
    simp only [List.length_cons, List.length_nil] at hcb
    omega
  rcases (by have := g.win_lo; omega :
      (a = off + 1) ∨ (off + 1 < a ∧ a < off + 2) ∨ (off + 2 < a))
      with h_leaf | ⟨h_d1, h_d2⟩ | h_adv
  · -- LEAF
    exact Or.inl (nestedSeq_recseqentry_locate_step_leaf tokens a b off H body g h_leaf h_off_open
      (nestedSeq_recseqentry_locate_leaf_off1_b tokens a b off H body g h_leaf))
  · -- middle arm is vacuous
    omega
  · -- ADVANCE
    refine Or.inr (nestedSeq_recseqentry_locate_step_advance tokens a b off H body rest
      (op :: ([] ++ [cl])) fe g h_eq ?_ h_fe h_rest ?_ ?_)
    · exact RecSeqEntry.seqEmpty op cl h_op h_cl
    · rw [nestedSeq_recseqentry_locate_sep_pos tokens body rest (op :: ([] ++ [cl])) fe off H
        g.slice g.bound g.Hsz h_eq]
      exact h_fe
    · simp only [List.nil_append, List.length_cons, List.length_nil]
      omega

/-- **The scalar-head CONS dispatch of `h_step`** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-brick-d-scalar-cons)`, R380, BRICK D (assembly).  The
    first of the six remaining `recseqbody_head_or_cons × cases h_e` cells, unblocked by the delta-generic
    boundary (R379).  The head entry is a bare scalar `[t]` (`RecSeqEntry.scalar`, `e.length = 1`), so the
    move trichotomy DEGENERATES: the LEAF position `a = off + 1` COINCIDES with the close-boundary
    `off + e.length = off + 1` (a scalar has no interior, hence no LEAF sub-window), and DESCEND is
    structurally absent.  So the dispatch is straight-line — no `rcases`: the boundary `a ≠ off + 1` is
    excluded by `…cons_boundary_delta` at the scalar token `m = off` (`flowBracketDelta (.scalar …) = 0 ≠ 1`,
    NOT the seq-close δ=−1 — the R379 lift earns its keep here, the SECOND distinct delta), which with
    `g.win_lo : off + 1 ≤ a` forces the whole interior `off + 1 < a` = the ADVANCE region.  ONE arm call
    (`…step_advance`, `h_e := RecSeqEntry.scalar`), no LEAF/DESCEND, so the head-opener bridge `h_off_scalar`
    is needed ONLY to feed the boundary delta (not an arm).  Verified-but-unconsumed until the full `h_step`
    assembles; frontier holds at 4. -/
theorem nestedSeq_recseqentry_locate_scalar_cons_step
    (tokens : Array (Positioned YamlToken)) (a b off H : Nat)
    (body rest : List (Positioned YamlToken))
    (t fe : Positioned YamlToken) (c : String) (s : ScalarStyle)
    (g : SeqLocateGuard tokens a b off H body)
    (h_eq : body = [t] ++ fe :: rest)
    (h_t : t.val = .scalar c s)
    (h_fe : fe.val = .flowEntry) (h_rest : RecSeqBody rest) :
    (∃ lo op' cl' interior', lo + 1 = a ∧ a ≤ b ∧
      RecSeqEntry (op' :: (interior' ++ [cl'])) ∧
      op'.val = .flowSequenceStart ∧ interior' ≠ [] ∧
      (tokens.toList.take (b + 1)).drop lo = op' :: (interior' ++ [cl']))
    ∨ (∃ off' H' body', body'.length < body.length ∧
      SeqLocateGuard tokens a b off' H' body') := by
  -- head scalar position (for the boundary delta)
  have h_pref_head : body = t :: (fe :: rest) := by rw [h_eq]; rfl
  have h_off_scalar : tokens[off]!.val = .scalar c s := by
    rw [nestedSeq_recseqentry_locate_head_pos tokens body (fe :: rest) t off H
      g.slice g.bound g.Hsz h_pref_head]
    exact h_t
  have hbl : body.length = rest.length + 2 := by
    rw [h_eq]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have h_m_sz : off < tokens.size := by
    have hb := g.bound; have hH := g.Hsz; omega
  -- boundary: a ≠ off + 1 (= off + [t].length), via the scalar delta (0 ≠ 1)
  have h_ne : a ≠ off + 1 :=
    nestedSeq_recseqentry_locate_cons_boundary_delta tokens a b off H off body g h_m_sz
      (by rw [h_off_scalar, flowBracketDelta_scalar]; omega)
  -- dispatch: LEAF (a = off+1) IS the boundary (excluded by h_ne); only ADVANCE (off+1 < a) survives
  have h_adv : off + 1 < a := by have := g.win_lo; omega
  refine Or.inr (nestedSeq_recseqentry_locate_step_advance tokens a b off H body rest
    [t] fe g h_eq ?_ h_fe h_rest ?_ ?_)
  · exact RecSeqEntry.scalar t c s h_t
  · rw [nestedSeq_recseqentry_locate_sep_pos tokens body rest [t] fe off H
      g.slice g.bound g.Hsz h_eq]
    exact h_fe
  · simp only [List.length_cons, List.length_nil]
    omega

/-- **The scalar-head HEAD dispatch of `h_step`** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-brick-d-scalar-head)`, R381, BRICK D (assembly).  The
    `recseqbody_head_or_cons` HEAD branch (`body = e`, a `single` body with NO separator) where the lone
    entry is a bare scalar `[t]` (`RecSeqEntry.scalar`, `e.length = 1`).  Pure `omega` CONTRADICTION — no
    arm call, no boundary brick, no new primitive.  The slice (`g.slice` + `g.Hsz`) forces
    `body.length = H - off`, and the body being the single scalar pins `body.length = 1`, so `off + 1 = H`
    (with `g.bound`).  Then `g.win_lo : off + 1 ≤ a`, `g.win_ab : a < b`, `g.win_hi : b < H = off + 1`
    collapse to `off + 1 ≤ a < b < off + 1` — impossible: a HEAD scalar window is too SHORT to contain a
    valid interior seq target `[a,b)`.  So the HEAD branch never reaches the move trichotomy (it needs no
    `h_ne` — the boundary falls inside the arithmetic-contradiction region).  Verified-but-unconsumed until
    the full `h_step` assembles; frontier holds at 4. -/
theorem nestedSeq_recseqentry_locate_scalar_head_step
    (tokens : Array (Positioned YamlToken)) (a b off H : Nat)
    (body : List (Positioned YamlToken))
    (t : Positioned YamlToken)
    (g : SeqLocateGuard tokens a b off H body)
    (h_eq : body = [t]) :
    (∃ lo op' cl' interior', lo + 1 = a ∧ a ≤ b ∧
      RecSeqEntry (op' :: (interior' ++ [cl'])) ∧
      op'.val = .flowSequenceStart ∧ interior' ≠ [] ∧
      (tokens.toList.take (b + 1)).drop lo = op' :: (interior' ++ [cl']))
    ∨ (∃ off' H' body', body'.length < body.length ∧
      SeqLocateGuard tokens a b off' H' body') := by
  exfalso
  have h_len : body.length = H - off := by
    rw [g.slice, List.length_drop, List.length_take, Array.length_toList]
    have := g.Hsz; omega
  have hbl : body.length = 1 := by rw [h_eq]; rfl
  have hb := g.bound; have hlo := g.win_lo; have hab := g.win_ab; have hhi := g.win_hi
  omega

/-- **The seqEmpty-head HEAD dispatch of `h_step`** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-brick-d-seqEmpty-head)`, R381, BRICK D (assembly).  The
    empty-interior sibling of `…_scalar_head_step`: the `recseqbody_head_or_cons` HEAD branch where the lone
    entry is an empty seq `op :: ([] ++ [cl])` (`RecSeqEntry.seqEmpty`, `e.length = 2`).  Same pure `omega`
    CONTRADICTION — the slice pins `body.length = 2`, so `off + 2 = H`, and `g.win_lo`/`g.win_ab`/`g.win_hi`
    collapse to `off + 1 ≤ a < b < off + 2` — impossible (only `off+1` fits, leaving no room for `a < b`).
    `e.length` 1/2 are both too SHORT for a HEAD window to host an interior seq target; the seq/map HEAD
    cells (`e.length ≥ 3`) instead split LEAF/DESCEND (refuted by BRICK B) from the arith-contra region.
    Verified-but-unconsumed until the full `h_step` assembles; frontier holds at 4. -/
theorem nestedSeq_recseqentry_locate_seqEmpty_head_step
    (tokens : Array (Positioned YamlToken)) (a b off H : Nat)
    (body : List (Positioned YamlToken))
    (op cl : Positioned YamlToken)
    (g : SeqLocateGuard tokens a b off H body)
    (h_eq : body = op :: ([] ++ [cl])) :
    (∃ lo op' cl' interior', lo + 1 = a ∧ a ≤ b ∧
      RecSeqEntry (op' :: (interior' ++ [cl'])) ∧
      op'.val = .flowSequenceStart ∧ interior' ≠ [] ∧
      (tokens.toList.take (b + 1)).drop lo = op' :: (interior' ++ [cl']))
    ∨ (∃ off' H' body', body'.length < body.length ∧
      SeqLocateGuard tokens a b off' H' body') := by
  exfalso
  have h_len : body.length = H - off := by
    rw [g.slice, List.length_drop, List.length_take, Array.length_toList]
    have := g.Hsz; omega
  have hbl : body.length = 2 := by rw [h_eq]; rfl
  have hb := g.bound; have hlo := g.win_lo; have hab := g.win_ab; have hhi := g.win_hi
  omega

/-- **The seq-head HEAD dispatch of `h_step`** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-brick-d-seq-head)`, R382, BRICK D (assembly).  The
    `recseqbody_head_or_cons` HEAD branch (`body = e`, NO separator) where the lone entry is a NON-empty
    seq block `op :: (interior ++ [cl])` (`RecSeqEntry.seq`, `e.length = interior.length + 2 ≥ 3`).  Unlike
    the short scalar/seqEmpty heads (R381, pure `omega`), a long entry leaves interior ROOM, so the branch
    is genuinely cleaved.  The slice SATURATES the window (`g.slice` + `g.Hsz` ⇒ `body.length = H - off`,
    so `off + interior.length + 2 = H`), and `Nat.lt_or_ge a (off + interior.length + 2)` splits it:
    * `a ≥ off + interior.length + 2 = H` — pure ARITH-CONTRA (`a ≥ H > b > a` via `g.win_hi`/`g.win_ab`),
      FREE from saturation; subsumes the close boundary (no `…cons_boundary` needed) — exactly R381's
      mechanism, now the UPPER half only ([[ref-saturation-cleaves-terminal-branch]]).
    * `a < off + interior.length + 2` — the genuine LEAF/DESCEND interior, REUSING the seq CONS carve's arm
      calls with `rest := []`: LEAF (`a = off + 1`) → `…step_leaf` (Or.inl, the `Q` deliverable); DESCEND
      (`off + 1 < a`) → `…step_descend` with `h_prefix : body = (op :: (interior ++ [cl])) ++ []`
      (`List.append_nil`).  `step_descend` derives `interior.length ≥ 1` from the two descend bounds, so the
      empty-interior overlap with `seqEmpty` (the `seq` constructor admits `interior = []`) closes vacuously.
    No new primitive — the only `h_step` move shapes are LEAF/DESCEND/arith-contra (ADVANCE is absent in the
    separator-free HEAD).  Verified-but-unconsumed until the full `h_step` assembles; frontier holds at 4. -/
theorem nestedSeq_recseqentry_locate_seq_head_step
    (tokens : Array (Positioned YamlToken)) (a b off H : Nat)
    (body interior : List (Positioned YamlToken))
    (op cl : Positioned YamlToken)
    (g : SeqLocateGuard tokens a b off H body)
    (h_eq : body = op :: (interior ++ [cl]))
    (h_op : op.val = .flowSequenceStart) (_h_cl : cl.val = .flowSequenceEnd)
    (h_wb : WellBracketed interior) (h_rec : RecSeqBody interior) :
    (∃ lo op' cl' interior', lo + 1 = a ∧ a ≤ b ∧
      RecSeqEntry (op' :: (interior' ++ [cl'])) ∧
      op'.val = .flowSequenceStart ∧ interior' ≠ [] ∧
      (tokens.toList.take (b + 1)).drop lo = op' :: (interior' ++ [cl']))
    ∨ (∃ off' H' body', body'.length < body.length ∧
      SeqLocateGuard tokens a b off' H' body') := by
  -- saturation: a separator-free HEAD entry spans its window, off + body.length = H
  have h_len : body.length = H - off := by
    rw [g.slice, List.length_drop, List.length_take, Array.length_toList]
    have := g.Hsz; omega
  have hbl : body.length = interior.length + 2 := by
    rw [h_eq]; simp only [List.length_cons, List.length_append, List.length_nil]
  -- head opener position
  have h_off_open : tokens[off]!.val = .flowSequenceStart := by
    rw [nestedSeq_recseqentry_locate_head_pos tokens body (interior ++ [cl]) op off H
      g.slice g.bound g.Hsz h_eq]
    exact h_op
  -- cleave at the container end: LEAF/DESCEND interior vs the saturated arith-contra region
  rcases Nat.lt_or_ge a (off + interior.length + 2) with h_lt | h_ge
  · rcases (by have := g.win_lo; omega : (a = off + 1) ∨ (off + 1 < a)) with h_leaf | h_desc_lo
    · -- LEAF
      exact Or.inl (nestedSeq_recseqentry_locate_step_leaf tokens a b off H body g h_leaf h_off_open
        (nestedSeq_recseqentry_locate_leaf_off1_b tokens a b off H body g h_leaf))
    · -- DESCEND (rest := [])
      refine Or.inr (nestedSeq_recseqentry_locate_step_descend tokens a b off H body [] interior op cl
        g ?_ h_off_open h_wb h_rec h_desc_lo h_lt)
      rw [h_eq]; simp
  · -- past the container: pure arith-contra (saturation a ≥ H > b > a)
    exfalso
    have hb := g.bound; have hhi := g.win_hi; have hab := g.win_ab
    omega

/-- **The map-head HEAD dispatch of `h_step`** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-brick-d-map-head)`, R382, BRICK D (assembly).  The
    HEAD-branch sibling where the lone entry is a `.flowMappingStart` block `op :: (interior ++ [cl])`
    (`RecSeqEntry.map`, `e.length ≥ 3`).  Same saturation cleave as the seq head, but the
    `a < off + interior.length + 2` interior half is now entirely REFUTED (a map can never inhabit the
    seq-entry deliverable `Q`), via BRICK B:
    * LEAF (`a = off + 1`): the target opener is `a - 1 = off`, a `.flowMappingStart`, so
      `seqEnclosed_map_push_breaks tokens off … h_off_map : ¬ SeqEnclosed tokens (off + 1)` contradicts the
      gate's enclosure mark `g.typed.2.1 : SeqEnclosed tokens a` re-based by `h_leaf : a = off + 1`.
    * DESCEND (`off + 1 < a`): `seqPathAllSeq_map_descend_excluded` (R374, BRICK B-i) — the map's `false`
      frame persists from `off` to `a - 1`, refuting `g.path : SeqPathAllSeq tokens (a - 1)`.
    The arith-contra upper half is shared verbatim with the seq head.  `rest := []`; references no sorry
    site, frontier sorry count unchanged at 4.  With both long-entry heads landed only map CONS remains
    before `h_step` assembles ([[ref-saturation-cleaves-terminal-branch]]). -/
theorem nestedSeq_recseqentry_locate_map_head_step
    (tokens : Array (Positioned YamlToken)) (a b off H : Nat)
    (body interior : List (Positioned YamlToken))
    (op cl : Positioned YamlToken)
    (g : SeqLocateGuard tokens a b off H body)
    (h_eq : body = op :: (interior ++ [cl]))
    (h_op : op.val = .flowMappingStart) (_h_cl : cl.val = .flowMappingEnd)
    (h_wb : WellBracketed interior) :
    (∃ lo op' cl' interior', lo + 1 = a ∧ a ≤ b ∧
      RecSeqEntry (op' :: (interior' ++ [cl'])) ∧
      op'.val = .flowSequenceStart ∧ interior' ≠ [] ∧
      (tokens.toList.take (b + 1)).drop lo = op' :: (interior' ++ [cl']))
    ∨ (∃ off' H' body', body'.length < body.length ∧
      SeqLocateGuard tokens a b off' H' body') := by
  exfalso
  -- saturation
  have h_len : body.length = H - off := by
    rw [g.slice, List.length_drop, List.length_take, Array.length_toList]
    have := g.Hsz; omega
  have hbl : body.length = interior.length + 2 := by
    rw [h_eq]; simp only [List.length_cons, List.length_append, List.length_nil]
  -- head opener position (a map open at off)
  have h_off_sz : off < tokens.size := by have := g.bound; have := g.Hsz; omega
  have h_off_map : tokens[off]!.val = .flowMappingStart := by
    rw [nestedSeq_recseqentry_locate_head_pos tokens body (interior ++ [cl]) op off H
      g.slice g.bound g.Hsz h_eq]
    exact h_op
  -- cleave: the interior region (LEAF/DESCEND, both REFUTED for a map) vs the arith-contra region
  rcases Nat.lt_or_ge a (off + interior.length + 2) with h_lt | h_ge
  · rcases (by have := g.win_lo; omega : (a = off + 1) ∨ (off + 1 < a)) with h_leaf | h_desc_lo
    · -- LEAF: target opener at `off` is a map open ⇒ ¬ SeqEnclosed, contradicting g.typed's mark
      have h_enc : SeqEnclosed tokens a := g.typed.2.1
      rw [h_leaf] at h_enc
      exact seqEnclosed_map_push_breaks tokens off h_off_sz h_off_map h_enc
    · -- DESCEND: map frame persists ⇒ ¬ SeqPathAllSeq (a-1), contradicting g.path (BRICK B-i)
      exact seqPathAllSeq_map_descend_excluded tokens a off H body [] interior op cl
        g.slice g.bound g.Hsz (by rw [h_eq]; simp) h_wb h_off_map g.path h_desc_lo h_lt
  · -- arith-contra (saturation)
    have hb := g.bound; have hhi := g.win_hi; have hab := g.win_ab
    omega

/-- **The map-head CONS dispatch of `h_step`** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-brick-d-map-cons)`, R383, BRICK D (assembly).  The
    LAST of the eight `recseqbody_head_or_cons × cases h_e` cells: the CONS branch
    (`body = (op :: (interior ++ [cl])) ++ fe :: rest`, head entry has a SUCCESSOR past `fe`) with a
    `.flowMappingStart` head (`RecSeqEntry.map`, NO `h_rec` — a map interior is not a `RecSeqBody`).
    Unlike the scalar CONS (R380, where the LEAF/boundary COINCIDE and collapse the dispatch to one
    straight-line ADVANCE), a map head has `e.length = interior.length + 2 ≥ 2`, so the move trichotomy
    is NON-degenerate and all three arms are reachable — but only ADVANCE produces; LEAF and DESCEND are
    REFUTED by BRICK B (a map can never inhabit the seq-entry deliverable `Q`):
    * LEAF (`a = off + 1`): `seqEnclosed_map_push_breaks` — the map open at `off` breaks the gate's
      enclosure mark `g.typed.2.1 : SeqEnclosed tokens a` re-based by `a = off + 1`.
    * DESCEND (`off + 1 < a < off + interior.length + 2`): `seqPathAllSeq_map_descend_excluded` (R374,
      BRICK B-i) — the map's `false` frame persists from `off` to `a - 1`, refuting `g.path`.
    * ADVANCE (`off + interior.length + 2 < a`): `…step_advance` with `h_e := RecSeqEntry.map`, the sole
      producing arm (the IH-shrinking move).
    The boundary `a ≠ off + interior.length + 2` is excluded by `…cons_boundary_delta` at the map close
    `cl` (`m = off + (op :: interior).length`, `flowBracketDelta .flowMappingEnd = -1 ≠ 1` — the THIRD
    distinct delta the R379 lift serves, after the seq close `-1` and the scalar `0`).  Same `…step_advance`
    / `…sep_pos` seams as the seq CONS carve, the only swap being the BRICK-B refutations for LEAF/DESCEND
    (the seq head PRODUCED/DESCENDED there, the map head REFUTES).  With this cell the eight-cell
    `h_step` dispatch is COMPLETE — assembly (`recseqbody_head_or_cons` + `cases h_e`) + the root seed
    remain.  Verified-but-unconsumed; frontier sorry count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_map_cons_step
    (tokens : Array (Positioned YamlToken)) (a b off H : Nat)
    (body rest interior : List (Positioned YamlToken))
    (op cl fe : Positioned YamlToken)
    (g : SeqLocateGuard tokens a b off H body)
    (h_eq : body = (op :: (interior ++ [cl])) ++ fe :: rest)
    (h_op : op.val = .flowMappingStart) (h_cl : cl.val = .flowMappingEnd)
    (h_wb : WellBracketed interior)
    (h_fe : fe.val = .flowEntry) (h_rest : RecSeqBody rest) :
    (∃ lo op' cl' interior', lo + 1 = a ∧ a ≤ b ∧
      RecSeqEntry (op' :: (interior' ++ [cl'])) ∧
      op'.val = .flowSequenceStart ∧ interior' ≠ [] ∧
      (tokens.toList.take (b + 1)).drop lo = op' :: (interior' ++ [cl']))
    ∨ (∃ off' H' body', body'.length < body.length ∧
      SeqLocateGuard tokens a b off' H' body') := by
  -- head opener position (a map open at off)
  have h_pref_head : body = op :: ((interior ++ [cl]) ++ fe :: rest) := by rw [h_eq]; rfl
  have h_off_map : tokens[off]!.val = .flowMappingStart := by
    rw [nestedSeq_recseqentry_locate_head_pos tokens body ((interior ++ [cl]) ++ fe :: rest) op off H
      g.slice g.bound g.Hsz h_pref_head]
    exact h_op
  -- close position (via sep_pos with e := op :: interior, re-bracketing the entry), for the boundary
  have h_pref_close : body = (op :: interior) ++ cl :: (fe :: rest) := by rw [h_eq]; simp
  have h_close_tok : tokens[off + (op :: interior).length]! = cl :=
    nestedSeq_recseqentry_locate_sep_pos tokens body (fe :: rest) (op :: interior) cl off H
      g.slice g.bound g.Hsz h_pref_close
  have h_close_val : tokens[off + (op :: interior).length]!.val = .flowMappingEnd := by
    rw [h_close_tok]; exact h_cl
  have hbl : body.length = interior.length + rest.length + 3 := by
    rw [h_eq]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have h_off_sz : off < tokens.size := by
    have hb := g.bound; have hH := g.Hsz; omega
  have h_m_sz : off + (op :: interior).length < tokens.size := by
    have hb := g.bound; have hH := g.Hsz
    simp only [List.length_cons]
    omega
  -- boundary: a ≠ off + interior.length + 2 (one past the map close `cl`, δ = -1 ≠ 1)
  have h_ne : a ≠ off + interior.length + 2 := by
    have hcb := nestedSeq_recseqentry_locate_cons_boundary_delta tokens a b off H
      (off + (op :: interior).length) body g h_m_sz
      (by rw [h_close_val, flowBracketDelta_flowMappingEnd]; omega)
    simp only [List.length_cons] at hcb
    omega
  -- dispatch (LEAF/DESCEND refuted by BRICK B; ADVANCE the only producing arm)
  rcases (by have := g.win_lo; omega :
      (a = off + 1) ∨ (off + 1 < a ∧ a < off + interior.length + 2)
        ∨ (off + interior.length + 2 < a)) with h_leaf | ⟨h_d1, h_d2⟩ | h_adv
  · -- LEAF: a map open at off ⇒ ¬ SeqEnclosed (off+1), contradicting g.typed's enclosure mark
    exfalso
    have h_enc : SeqEnclosed tokens a := g.typed.2.1
    rw [h_leaf] at h_enc
    exact seqEnclosed_map_push_breaks tokens off h_off_sz h_off_map h_enc
  · -- DESCEND: map frame persists ⇒ ¬ SeqPathAllSeq (a-1), contradicting g.path (BRICK B-i)
    exact (seqPathAllSeq_map_descend_excluded tokens a off H body (fe :: rest) interior op cl
      g.slice g.bound g.Hsz h_eq h_wb h_off_map g.path h_d1 h_d2).elim
  · -- ADVANCE: the only producing arm (h_e := RecSeqEntry.map)
    refine Or.inr (nestedSeq_recseqentry_locate_step_advance tokens a b off H body rest
      (op :: (interior ++ [cl])) fe g h_eq ?_ h_fe h_rest ?_ ?_)
    · exact RecSeqEntry.map op cl interior h_op h_cl h_wb
    · rw [nestedSeq_recseqentry_locate_sep_pos tokens body rest (op :: (interior ++ [cl])) fe off H
        g.slice g.bound g.Hsz h_eq]
      exact h_fe
    · simp only [List.length_cons, List.length_append, List.length_nil]
      omega

/-- **The locator's per-window step `h_step`, assembled** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-brick-d-assemble)`, R384, BRICK D (assembly).  The
    fan-out that folds the eight landed cells into the single hypothesis `seqLocateRecDriver` consumes:
    at every window `SeqLocateGuard tokens a b off H body`, either the seq-entry deliverable `Q` is found
    (`Or.inl`) or the body strictly shrinks to a recursive sub-window (`Or.inr`).

    The proof is a GLUE-FREE 2×4 dispatch — `recseqbody_head_or_cons g.recBody` splits HEAD (`body = e`,
    a separator-free `single`) from CONS (`body = e ++ fe :: rest`), and `cases h_e` splits the
    `RecSeqEntry` shape (scalar / seqEmpty / seq / map).  No reconciliation glue: each cell was carved
    so that its leading hypothesis `h_eq : body = <pattern>` is EXACTLY the equation `cases`'s
    index-substitution produces ([[ref-carve-leaves-to-eliminator-output]]) — the scalar constructor
    substitutes `e := [t]`, so the reverted `h_eq : body = e` re-emerges as `body = [t]`, the seq
    constructor as `body = op :: (interior ++ [cl])`, etc., each matching its cell verbatim.  The CONS
    siblings `h_fe`/`h_rest` do NOT depend on the eliminated index `e`, so `cases h_e` leaves them
    un-reverted and they slot straight into the cell calls.  Each branch is one `exact <cell> …` over
    the post-`cases` context variables — the assembler is the INVERSE of the carve.

    With this, the per-window step is one hypothesis of the shape `seqLocateRecDriver` wants
    (`G := SeqLocateGuard tokens a b`, `Q :=` the seq-entry existential).  The ROOT SEED `h_root` (the
    descent's debt: the strict `win_ab`, the window-absolute `path`, and `opener`/`typed`/`close`/`window`
    at the top span — [[ref-root-seed-discriminator-not-from-gate]]) remains before
    `nestedSeq_recseqentry_locate := seqLocateRecDriver … hstep … h_root` lands.  Verified-but-unconsumed;
    frontier sorry count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_hstep
    (tokens : Array (Positioned YamlToken)) (a b : Nat) :
    ∀ off H body, SeqLocateGuard tokens a b off H body →
      (∃ lo op' cl' interior', lo + 1 = a ∧ a ≤ b ∧
        RecSeqEntry (op' :: (interior' ++ [cl'])) ∧
        op'.val = .flowSequenceStart ∧ interior' ≠ [] ∧
        (tokens.toList.take (b + 1)).drop lo = op' :: (interior' ++ [cl']))
      ∨ (∃ off' H' body', body'.length < body.length ∧
        SeqLocateGuard tokens a b off' H' body') := by
  intro off H body g
  rcases recseqbody_head_or_cons g.recBody with
    ⟨e, _h_ne, h_e, _h_head, h_eq⟩ | ⟨e, fe, rest, _h_ne, h_e, _h_head, h_fe, h_rest, h_eq⟩
  · -- HEAD branch (body = e, no separator): scalar/seqEmpty too short (omega), seq/map saturation-cleaved
    cases h_e with
    | scalar t c s ht =>
        exact nestedSeq_recseqentry_locate_scalar_head_step tokens a b off H body t g h_eq
    | seqEmpty op cl h_op h_cl =>
        exact nestedSeq_recseqentry_locate_seqEmpty_head_step tokens a b off H body op cl g h_eq
    | seq op cl interior h_op h_cl h_wb h_rec =>
        exact nestedSeq_recseqentry_locate_seq_head_step tokens a b off H body interior op cl
          g h_eq h_op h_cl h_wb h_rec
    | map op cl interior h_op h_cl h_wb =>
        exact nestedSeq_recseqentry_locate_map_head_step tokens a b off H body interior op cl
          g h_eq h_op h_cl h_wb
    | mapRec op cl interior h_op h_cl h_wb _ =>
        exact nestedSeq_recseqentry_locate_map_head_step tokens a b off H body interior op cl
          g h_eq h_op h_cl h_wb
  · -- CONS branch (body = e ++ fe :: rest): each head's three-arm dispatch into the carved CONS cells
    cases h_e with
    | scalar t c s ht =>
        exact nestedSeq_recseqentry_locate_scalar_cons_step tokens a b off H body rest t fe c s
          g h_eq ht h_fe h_rest
    | seqEmpty op cl h_op h_cl =>
        exact nestedSeq_recseqentry_locate_seqEmpty_cons_step tokens a b off H body rest op cl fe
          g h_eq h_op h_cl h_fe h_rest
    | seq op cl interior h_op h_cl h_wb h_rec =>
        exact nestedSeq_recseqentry_locate_seq_cons_step tokens a b off H body rest interior op cl fe
          g h_eq h_op h_cl h_wb h_rec h_fe h_rest
    | map op cl interior h_op h_cl h_wb =>
        exact nestedSeq_recseqentry_locate_map_cons_step tokens a b off H body rest interior op cl fe
          g h_eq h_op h_cl h_wb h_fe h_rest
    | mapRec op cl interior h_op h_cl h_wb _ =>
        exact nestedSeq_recseqentry_locate_map_cons_step tokens a b off H body rest interior op cl fe
          g h_eq h_op h_cl h_wb h_fe h_rest

/-- **Per-item hypothesis coercion — `EmitScansInFlowRecEntry v → EmitScansInFlowBlock v`** —
    `(i'-b-B2c-nested-fbc-emission-locator-root-structural-coerce)`, R386.  The two per-item emission
    predicates are IDENTICAL — same nine hypotheses, same `∃ n s' block` conclusion with the same
    twenty-two conjuncts — EXCEPT `EmitScansInFlowRecEntry` carries ONE extra conjunct `RecSeqEntry block`
    (the locator's recursive deliverable, conjunct #22 of 23).  Dropping it DOWN-coerces the stronger
    per-item predicate the nested locator threads to the weaker `EmitScansInFlowBlock` the existing
    whole-structure lemma `scanFiltered_emitSeq_nonempty_structure` consumes.  Mechanical
    destructure-drop-reassemble ([[ref-coerce-to-weaker-reuse-wrapper]] at the PER-ITEM-hypothesis
    granularity: one emission, two consumers picking different per-item predicates; the shared facts
    re-export after the coercion). -/
theorem emitScansInFlowBlock_of_flowRecEntry (v : YamlValue)
    (h : EmitScansInFlowRecEntry v) : EmitScansInFlowBlock v := by
  intro s rest h_corr h_inflow h_flow h_indent h_col h_ekl h_atol h_endline h_sks
  obtain ⟨n, s', block, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
          h15, h16, h17, h18, h19, h20, h21, _h22, h23, h24, h25⟩ :=
    h s rest h_corr h_inflow h_flow h_indent h_col h_ekl h_atol h_endline h_sks
  exact ⟨n, s', block, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, h17, h18, h19, h20, h21, h23, lastNonOpener_of_entryUnit block h21, h24,
    lastNonSep_of_entryUnit_contentHead block h21 h23, h25⟩

/-- **The deferred-structural root WINDOW — `FlowBodyWindow tokens 2 (size-2)`** —
    `(i'-b-B2c-nested-fbc-emission-locator-root-structural-window)`, R386.  R385's root seed named
    `window : FlowBodyWindow tokens 2 (size-2)` a DEFERRED-STRUCTURAL hypothesis (a NEW owed brick).  It
    is NOT a substantial new brick: the sibling whole-structure lemma
    `scanFiltered_emitSeq_nonempty_structure` ALREADY proves its three content fields — `balanced`
    (`flowBracketBalance tokens 2 (size-2) = 0`), `dyck` (`∀ k, 2 ≤ k → k ≤ size-2 → balance ≥ 0`,
    verbatim the `FlowBodyWindow.dyck` shape at `lo = 2`), `wellTyped` — en route to its OWN
    `FlowSubrangesOk` goal, for a DIFFERENT consumer.  This extracts them; the four frame bounds are
    `Nat.le_refl`/`omega` off `size ≥ 5`.  The only gap is the per-item-hypothesis strength
    (`EmitScansInFlowRecEntry` vs the lemma's `EmitScansInFlowBlock`), bridged by
    `emitScansInFlowBlock_of_flowRecEntry`.  [[ref-metric-bridge-is-composition]] /
    [[ref-root-seed-recursive-producer-swap]]: the feared deferred brick was already a theorem. -/
theorem seqRoot_flowBodyWindow
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v) :
    FlowBodyWindow tokens 2 (tokens.size - 2) := by
  have h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w :=
    fun w hw => emitScansInFlowBlock_of_flowRecEntry w (h_all w hw)
  obtain ⟨h_sz5, _h_t0, _h_tlast, _h_t1, _h_tpe, _h_content0, _h_fe_pattern,
          h_outer_bal, h_dyck, h_wt_interior, _h_body_opener, _h_body_separator⟩ :=
    scanFiltered_emitSeq_nonempty_structure items tokens h_scan h_ne h_all_block
  exact ⟨Nat.le_refl 2, by omega, Nat.le_refl _, by omega, h_outer_bal, h_dyck, h_wt_interior⟩

/-- **The deferred-structural root DOMAIN — `SeqPathAllSeq tokens 2`** —
    `(i'-b-B2c-nested-fbc-emission-locator-root-structural-domain)`, R386.  R385's other deferred-
    structural hypothesis, `domain : SeqPathAllSeq tokens 2` (the whole typed bracket stack after the
    prefix `[0, 2)` is nonempty and all-`true`).  After the first two emitted+filtered tokens — a
    `.streamStart` (which leaves the stack) then the outer `.flowSequenceStart` (which pushes `true`) —
    the stack is `[true]`.  A direct two-step `btFold` computation off the head-token facts
    `scanFiltered_emitSeq_nonempty_structure` already supplies (`tokens[0] = .streamStart`,
    `tokens[1] = .flowSequenceStart`, `size ≥ 5`).  Like `seqRoot_flowBodyWindow`, no substantial new
    brick — the sibling structure lemma's facts re-export after the per-item coercion. -/
theorem seqRoot_seqPathAllSeq
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v) :
    SeqPathAllSeq tokens 2 := by
  have h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w :=
    fun w hw => emitScansInFlowBlock_of_flowRecEntry w (h_all w hw)
  obtain ⟨h_sz5, h_t0, _h_tlast, h_t1, _h_tpe, _h_content0, _h_fe_pattern,
          _h_outer_bal, _h_dyck, _h_wt_interior, _h_body_opener, _h_body_separator⟩ :=
    scanFiltered_emitSeq_nonempty_structure items tokens h_scan h_ne h_all_block
  have h0 : 0 < tokens.toList.length := by rw [Array.length_toList]; omega
  have h1 : 1 < tokens.toList.length := by rw [Array.length_toList]; omega
  have e0 : (tokens.toList[0]'h0).val = .streamStart := by
    have hb : tokens.toList[0]'h0 = tokens[0]! := by
      rw [Array.getElem_toList, getElem!_pos tokens 0 (by omega)]
    rw [hb]; exact h_t0
  have e1 : (tokens.toList[1]'h1).val = .flowSequenceStart := by
    have hb : tokens.toList[1]'h1 = tokens[1]! := by
      rw [Array.getElem_toList, getElem!_pos tokens 1 (by omega)]
    rw [hb]; exact h_t1
  have step1 : tokens.toList.take 2 = tokens.toList.take 1 ++ [tokens.toList[1]'h1] :=
    List.take_succ_eq_append_getElem h1
  have step0 : tokens.toList.take 1 = tokens.toList.take 0 ++ [tokens.toList[0]'h0] :=
    List.take_succ_eq_append_getElem h0
  have h_take2 : tokens.toList.take 2 = [tokens.toList[0]'h0, tokens.toList[1]'h1] := by
    rw [step1, step0]; rfl
  refine ⟨[true], ?_, by simp, by simp⟩
  rw [h_take2]
  have hb0 : btStep (tokens.toList[0]'h0) [] = some [] := by simp only [btStep, e0]
  have hb1 : btStep (tokens.toList[1]'h1) [] = some [true] := by simp only [btStep, e1]
  rw [btFold_cons_some, hb0, btFold_cons_some, hb1]
  rfl

/-- **The locator's ROOT SEED — `SeqLocateGuard` at the outer span `[2, size-2)`** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-brick-d-root-seed)`, R385, BRICK D (root seed).  The
    base case `seqLocateRecDriver` consumes: the guard bundle at the WALKING window = the WHOLE top-level
    flow-sequence body `[2, size-2)`, with the fixed target `[a, b)` carried as before.  Per
    [[ref-root-seed-discriminator-not-from-gate]] / [[ref-universal-producer-root-seed-first]] the seed is
    PURE PACKAGING: it does no locate/descend analysis (that all lives in the inductive step `hstep`); it
    assembles the 13 fields from infra-delivered + debt facts.

    **Three field classes.** (1) **Derived-at-root from emission** — `recBody := seqRoot_recseqbody …`
    (the recursive seq body of the outer span, [[ref-root-seed-recursive-producer-swap]]: the flat-root
    `RecSeqBody` re-projection), `slice := rfl` (the window IS `(take (size-2)).drop 2` by definition),
    `Hsz := Nat.sub_le …`, and `bound` (a `List.length_drop`/`_take` computation + `omega`, the only
    field with proof content — `body₀.length = min (size-2) size - 2`, and the strict target bounds force
    `size ≥ 6`).  (2) **Root-STRUCTURAL hypotheses** — `domain : SeqPathAllSeq tokens 2` and
    `window : FlowBodyWindow tokens 2 (size-2)`: facts about the OUTER frame, not the target, so NOT debt;
    derivable from `h_scan` by token-level emission reasoning, but that derivation is a SEPARATE brick, so
    they are taken as hypotheses here (the seed's interface, [[ref-root-seed-recursive-producer-swap]]:
    the seed packages infra it does not itself build).  (3) **The descent's DEBT** — the seven
    target-RELATIVE discriminators `typed`/`close`/`opener`/`path`/`win_lo`/`win_ab`/`win_hi`: facts about
    `[a, b)`'s position the gate cannot supply (it is satisfied by the descent's own nested targets too,
    [[ref-root-seed-discriminator-not-from-gate]]), so each enters as a hypothesis = the fact the DESCENT
    re-establishes per level (`hstep`'s DESCEND/ADVANCE arms produce them from the located bracket).  The
    load-bearing pair is the strict `win_ab : a < b` (the non-empty-target precondition, R376) and the
    window-absolute `path : SeqPathAllSeq tokens (a-1)` (R375).  The root-structural `domain`/`window`
    derivations landed in R386 (`seqRoot_seqPathAllSeq` / `seqRoot_flowBodyWindow`), so
    `nestedSeq_recseqentry_locate` supplies them here from `h_scan` and is now hypothesis-free over
    emission.  References no sorry site, frontier sorry count unchanged at 4. -/
theorem nestedSeq_recseqentry_locate_root_seed
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v)
    (h_domain : SeqPathAllSeq tokens 2)
    (h_window : FlowBodyWindow tokens 2 (tokens.size - 2))
    (h_typed : SeqTypedInterior tokens a b)
    (h_close : tokens[b]!.val = .flowSequenceEnd)
    (h_opener : flowBracketBalance tokens (a - 1) a = 1)
    (h_path : SeqPathAllSeq tokens (a - 1))
    (h_win_lo : 2 + 1 ≤ a)
    (h_win_ab : a < b)
    (h_win_hi : b < tokens.size - 2) :
    SeqLocateGuard tokens a b 2 (tokens.size - 2)
      ((tokens.toList.take (tokens.size - 2)).drop 2) := by
  refine ⟨h_domain, seqRoot_recseqbody items tokens h_scan h_ne h_all, rfl, ?_,
    Nat.sub_le tokens.size 2, h_typed, h_close, h_opener, h_path, h_win_lo, h_win_ab,
    h_win_hi, h_window⟩
  -- bound : 2 + body₀.length ≤ tokens.size - 2 ; body₀.length = min (size-2) size - 2, strict
  -- target bounds (win_lo/win_ab/win_hi) force size ≥ 6 so omega closes it.
  simp only [List.length_drop, List.length_take, Array.length_toList]
  omega

/-- **The nested-FBC emission LOCATOR — BRICK D complete** —
    `(i'-b-B2c-nested-fbc-emission-locator-skeleton-brick-d)`, R385.  Closes the emission-spine-walk
    locator: at any all-seq-path target window `[a, b)` inside the top-level flow sequence `[2, size-2)`
    (gated by the seven target discriminators), the target IS a real nested seq entry — there is a `lo`
    (`= a - 1`) and an `op'`/`cl'`/`interior'` with `op'.val = .flowSequenceStart`, `interior' ≠ []`, and
    the slice `(take (b+1)).drop lo` equal to that seq entry, a `RecSeqEntry`.

    Wires the three landed pieces with NO new analysis ([[ref-from-located-assembler-direction]] — the
    root seed factored the DESCENT out; this composes them): the MEASURE driver
    `seqLocateRecDriver` (R365, `Nat.strongRecOn`-on-`body.length`) instantiated at `G := SeqLocateGuard
    tokens a b` and `Q :=` the seq-entry existential, fed the assembled per-window step
    `nestedSeq_recseqentry_locate_hstep` (R384) and the ROOT SEED `nestedSeq_recseqentry_locate_root_seed`
    (R385) at the outer window `(2, size-2, body₀)`.  This CONSUMES `hstep` (retyping the BRICK-D residual
    from execution to structural, [[ref-reduction-by-import]]) — the eight cells + assembly are now load-
    bearing under a real consumer.

    **Now HYPOTHESIS-FREE over emission (R386).**  The root-structural `h_domain`/`h_window` R385 took as
    hypotheses are derived inline from `h_scan`/`h_ne`/`h_all` via `seqRoot_seqPathAllSeq` /
    `seqRoot_flowBodyWindow` (their content already proven inside `scanFiltered_emitSeq_nonempty_structure`
    for the `FlowSubrangesOk` consumer; the per-item coercion `emitScansInFlowBlock_of_flowRecEntry`
    bridges the gap).  So the locator takes only `h_scan` + the seven target discriminators and is ready to
    CONSUME — verified-but-unconsumed until the map mirror (`RecMapBody` axis) and
    `flowSubrangesOk_of_window_producers` feed the two `FlowSubrangesOk` sorries
    (`NonemptyStructure.lean:7502`/`:7743`).  References no sorry site, frontier sorry count unchanged at
    4. -/
theorem nestedSeq_recseqentry_locate
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v)
    (h_typed : SeqTypedInterior tokens a b)
    (h_close : tokens[b]!.val = .flowSequenceEnd)
    (h_opener : flowBracketBalance tokens (a - 1) a = 1)
    (h_path : SeqPathAllSeq tokens (a - 1))
    (h_win_lo : 2 + 1 ≤ a)
    (h_win_ab : a < b)
    (h_win_hi : b < tokens.size - 2) :
    ∃ lo op' cl' interior', lo + 1 = a ∧ a ≤ b ∧
      RecSeqEntry (op' :: (interior' ++ [cl'])) ∧
      op'.val = .flowSequenceStart ∧ interior' ≠ [] ∧
      (tokens.toList.take (b + 1)).drop lo = op' :: (interior' ++ [cl']) :=
  seqLocateRecDriver (SeqLocateGuard tokens a b)
    (nestedSeq_recseqentry_locate_hstep tokens a b)
    2 (tokens.size - 2) ((tokens.toList.take (tokens.size - 2)).drop 2)
    (nestedSeq_recseqentry_locate_root_seed items tokens a b h_scan h_ne h_all
      (seqRoot_seqPathAllSeq items tokens h_scan h_ne h_all)
      (seqRoot_flowBodyWindow items tokens h_scan h_ne h_all)
      h_typed h_close h_opener h_path h_win_lo h_win_ab h_win_hi)

/-- **The located nested seq's interior `RecSeqBody`** —
    `(i'-b-B2c-nested-fbc-emission-locator-CONSUME-recseqbody)`, R388.  The DELIVERABLE-SHAPED consumer
    of the now-hypothesis-free locator `nestedSeq_recseqentry_locate` (R386): at any all-seq-path nested
    seq window `[a, b)` (the seven target discriminators), it projects the located entry to the
    *recursive* seq body `RecSeqBody ((tokens.toList.take b).drop a)` — the EXACT type the per-window
    producer `h_seq_rec` of `flowSubrangesOk_of_window_producers` demands
    (`RecSeqBody ((take hi).drop lo)`), produced DIRECTLY from emission with NO carrier, NO width
    fixpoint, NO `desc`.

    Three landed pieces, NO new analysis (the `RecSeqBody` core that `nestedSeq_safeBodyUnit_of_locator`
    R387 already computed, here factored out BEFORE its `.toSafeBodyUnit` projection): (1)
    `nestedSeq_recseqentry_locate` delivers the seq entry `op' :: (interior' ++ [cl'])`
    (`op'.val = .flowSequenceStart`, `interior' ≠ []`, slice `(take (b+1)).drop lo`, `lo + 1 = a`); (2)
    `recseqentry_seq_extract` reads off the stored `RecSeqBody interior'` (opener + non-empty interior
    force the `.seq` constructor); (3) `nestedSeq_recseqentry_locate_descend` (rest = []) re-cuts
    `interior'` to `(take b).drop a` via the length identity `lo + 1 + interior'.length = b`.

    **De-risk redirect (R388 — the B2c-CONSUME plan correction, [[ref-locate-consumer-by-gate-strength]]).**
    The R387 doc and the prior blueprint Next step said this family "feeds `seqRoot_seqInteriorSeparators`'s
    `desc` hypothesis" — a MISATTRIBUTION.  `desc` quantifies over a GENERAL gated window `[a,b)`
    (`SeqTypedInterior`, where `tokens[a-1]` may be a `.flowEntry` separator — the window sits mid-body),
    and is served by the BACKWARD enclosing-opener scan `seqEnclosingOpener_of_gate` (R319, landed
    term-for-term) inside `seqDescent_provider_of_gate`; its only residual is the width fixpoint `h_enc`,
    NOT this locator.  This forward locator's window is STRICTLY NARROWER — `h_opener : balance (a-1) a = 1`
    forces `tokens[a-1]` to BE the opener, so `[a,b)` is a complete nested-seq interior, a strict subset of
    `desc`'s windows.  Its genuine downstream is `h_seq_rec`, whose window-guard is WEAKER (bracket facts
    only: `tokens[lo-1]! = .flowSequenceStart`, `tokens[hi]! = .flowSequenceEnd`, balance-0, `2 ≤ lo`,
    `hi ≤ size-2` — no Dyck floor, no enclosing mark, no all-seq path, not strict).  So the locator is
    too-NARROW-for-`desc` (cannot serve it) AND too-STRONG-vs-`h_seq_rec` (a GATE-STRENGTHENING bridge —
    `h_seq_rec`'s bracket guards + global well-typedness ⟹ this locator's `SeqTypedInterior` +
    `SeqPathAllSeq` gate — is the next residual).  Located by comparing GATE STRENGTH against each
    candidate consumer's window-guard, in BOTH directions.  Map mirror (`RecMapBody` axis) owed for
    `:7743` regardless.  References no sorry site, frontier sorry count unchanged at 4. -/
theorem nestedSeq_recseqbody_of_locator
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v)
    (h_typed : SeqTypedInterior tokens a b)
    (h_close : tokens[b]!.val = .flowSequenceEnd)
    (h_opener : flowBracketBalance tokens (a - 1) a = 1)
    (h_path : SeqPathAllSeq tokens (a - 1))
    (h_win_lo : 2 + 1 ≤ a)
    (h_win_ab : a < b)
    (h_win_hi : b < tokens.size - 2) :
    RecSeqBody ((tokens.toList.take b).drop a) := by
  obtain ⟨lo, op', cl', interior', h_lo, _h_ab, h_entry, h_open, h_int_ne, h_slice⟩ :=
    nestedSeq_recseqentry_locate items tokens a b h_scan h_ne h_all h_typed h_close
      h_opener h_path h_win_lo h_win_ab h_win_hi
  -- The located entry is a `.seq` (opener `[`, non-empty interior): extract its interior `RecSeqBody`.
  have h_recbody : RecSeqBody interior' :=
    recseqentry_seq_extract h_entry op' cl' interior' rfl h_open h_int_ne
  -- Slice length: interior'.length determined by the window, so `lo + 1 + interior'.length = b`.
  have h_lenfact := congrArg List.length h_slice
  simp only [List.length_drop, List.length_take, Array.length_toList,
    List.length_cons, List.length_append, List.length_nil] at h_lenfact
  have h_len : lo + 1 + interior'.length = b := by omega
  -- Re-cut the interior via the descend-slice lemma (rest = []).
  have h_bound : lo + (op' :: (interior' ++ [cl'])).length ≤ b + 1 := by
    simp only [List.length_cons, List.length_append, List.length_nil]; omega
  have h_islice : interior'
      = (tokens.toList.take (lo + 1 + interior'.length)).drop (lo + 1) :=
    nestedSeq_recseqentry_locate_descend tokens (op' :: (interior' ++ [cl'])) [] interior'
      op' cl' lo (b + 1) h_slice.symm h_bound (by rw [List.append_nil])
  rw [h_len, h_lo] at h_islice
  rw [h_islice] at h_recbody
  exact h_recbody

/-- **The located nested seq's per-window `FlowBodyContent`** —
    `(i'-b-B2c-desc-fixpoint-navigator-read-CONSUME)`, R507: the CONSUME side of R506
    (`flowBodyContent_of_located_seq_entry`), the `FlowBodyContent` twin of `nestedSeq_recseqbody_of_locator`
    (R388, the `RecSeqBody` projection).  Feeds the now-landed, hypothesis-free-over-emission navigator
    `nestedSeq_recseqentry_locate` (R385/R386) — which LOCATES the enclosing seq entry from emission + the
    seven target discriminators — straight into R506's terminal READ, yielding the per-window content
    `FlowBodyContent tokens a b` carrier-free.  This RETYPES R506's residual from execution to structural
    ([[ref-reduction-by-import]]): R506 was verified-but-unconsumed pending "the wrapper that produces the
    located entry"; that wrapper already exists, so R506 is now load-bearing under a real producer.

    **The decisive scope finding this brick records (the architectural correction).**  The summary/blueprint
    Next step said to "build the spine-walk recursion wrapper" — but reading the code, that wrapper was
    ALREADY assembled (R384 `nestedSeq_recseqentry_locate_hstep` + R385 `nestedSeq_recseqentry_locate` over
    `seqLocateRecDriver`), so this turn consumes it rather than building it.  More importantly, the navigator
    — and the WHOLE R350–R388/R447 seq-locator infrastructure — carries `h_path : SeqPathAllSeq tokens (a-1)`
    (EVERY enclosing frame `[`-typed), so it serves ONLY all-seq-path windows.  But the frontier consumer
    `h_seq_rec` (of `flowSubrangesOk_of_window_producers`, via `seqLocator_of_window_recseqbody`) fires on
    EVERY balanced seq-bracket window — INCLUDING a map-nested seq like `[{a: [b]}]`'s inner `[b]`, where
    `SeqPathAllSeq` is FALSE (a `false` from the `{` sits below the top, though `SeqEnclosed` — the TOP
    frame — still holds).  So neither this brick nor R388 can discharge `h_seq_rec` in general: they cover
    the all-seq-path fragment only.

    **Why this still matters, and where it points.**  The R505 recursion route's per-window provider gate is
    `FlowBodyWindow ∧ FlowBodyContentDeepSeq ∧ SeqEnclosed` — the path-FREE `SeqEnclosed` (immediate `[`),
    NOT the global `SeqPathAllSeq` — so the R505 route is the architecture that CAN reach the map-nested
    seqs the navigator cannot ([[ref-stored-vs-projected-severs-recursion-edge]]: the recursion threads
    descent structurally through its own IH, never the global spine).  Its open residual is a path-FREE (or
    joint seq+map) per-window `FlowBodyContent` source for `bodySucc`; this all-seq-path provider is the
    discharged ARM of the eventual dispatch.  Composes only landed lemmas (navigator + R506), references no
    sorry site, frontier sorry count unchanged; axiom-clean. -/
theorem nestedSeq_flowBodyContent_of_locator
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v)
    (h_deep : FlowBodyContentDeepSeq tokens a b)
    (h_typed : SeqTypedInterior tokens a b)
    (h_close : tokens[b]!.val = .flowSequenceEnd)
    (h_opener : flowBracketBalance tokens (a - 1) a = 1)
    (h_path : SeqPathAllSeq tokens (a - 1))
    (h_win_lo : 2 + 1 ≤ a)
    (h_win_ab : a < b)
    (h_win_hi : b < tokens.size - 2) :
    FlowBodyContent tokens a b := by
  -- The navigator LOCATES the enclosing seq entry from emission + the seven discriminators.
  obtain ⟨lo, op', cl', interior', h_lo, _h_ab, h_entry, h_open, h_int_ne, h_slice⟩ :=
    nestedSeq_recseqentry_locate items tokens a b h_scan h_ne h_all h_typed h_close
      h_opener h_path h_win_lo h_win_ab h_win_hi
  -- R506 reads the content off the located entry — carrier-free, no production.
  exact flowBodyContent_of_located_seq_entry tokens a b (by omega) h_deep
    lo op' cl' interior' h_lo h_entry h_open h_int_ne h_slice

/-- **The located nested seq's windowed `SafeBodyUnit`** —
    `(i'-b-B2c-nested-fbc-emission-locator-CONSUME-safebodyunit)`, R387 (R388: now a thin
    `.toSafeBodyUnit` wrapper of `nestedSeq_recseqbody_of_locator`).  At any all-seq-path nested seq
    window `[a, b)` (the seven target discriminators), it projects the located entry's interior recursive
    body to the flat `SafeBodyUnit ContentStartTok ((tokens.toList.take b).drop a)` — the substrate the
    seq separator-fact lemmas key on (`seqSeparatorFacts_of_windowed_safebodyunit`,
    `seqInteriorFeContentStart_of_windowed_safebodyunit`, `seqEnclosingFacts_of_windowed_safebodyunit`)
    for the carrier-route `FlowBodyContent` thread.

    The `RecSeqBody` core is `nestedSeq_recseqbody_of_locator` (R388); this wrapper is its
    `RecSeqBody.toSafeBodyUnit` projection.  Both share the locator's NARROW window class (opener-headed
    complete nested-seq interior, `h_opener : balance (a-1) a = 1`): per the R388 de-risk redirect that
    is too narrow for `desc` (served by the backward scan) and the `RecSeqBody` form — not this
    `SafeBodyUnit` one — is the direct deliverable for `h_seq_rec` (modulo a gate-strengthening bridge).
    The seq sorry (`NonemptyStructure.lean:7502`) cannot close on the seq locator ALONE: `FlowSubrangesOk
    tokens` also quantifies a `map` half (a top-level seq can nest a mapping, `[{a: b}]`), so the map
    mirror (`RecMapBody` axis) is owed regardless.  References no sorry site, frontier sorry count
    unchanged at 4. -/
theorem nestedSeq_safeBodyUnit_of_locator
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v)
    (h_typed : SeqTypedInterior tokens a b)
    (h_close : tokens[b]!.val = .flowSequenceEnd)
    (h_opener : flowBracketBalance tokens (a - 1) a = 1)
    (h_path : SeqPathAllSeq tokens (a - 1))
    (h_win_lo : 2 + 1 ≤ a)
    (h_win_ab : a < b)
    (h_win_hi : b < tokens.size - 2) :
    SafeBodyUnit ContentStartTok ((tokens.toList.take b).drop a) :=
  (nestedSeq_recseqbody_of_locator items tokens a b h_scan h_ne h_all h_typed h_close
    h_opener h_path h_win_lo h_win_ab h_win_hi).toSafeBodyUnit

/-- **The per-window `SafeBodyUnit` source — ROOT-vs-NESTED dispatch** —
    `(i'-b-B2c-(d) — STEP D: the within-window circularity `h_safe` source)`, R447.  The unified,
    carrier-FREE producer of the per-window `h_safe : SafeBodyUnit ContentStartTok ((take hi).drop lo)`
    that `seqLocalCarrier_of_widthEnc` (R446) consumes — the half of the carrier↔recursion
    co-construction that breaks the within-window circularity.

    **Why a dispatch.**  The carrier(lo,hi) needs `h_safe(lo,hi)`, and body(lo,hi) needs carrier(lo,hi);
    if `h_safe` came from body it would be circular.  It must be sourced INDEPENDENTLY from emission.
    Reading the landed code (R447), there are exactly two carrier-free emission sources, split by whether
    the window IS the root span:

    * **ROOT** (`lo = 2 ∧ hi = tokens.size - 2`): the FLAT `seqRoot_safeBodyUnit` (`NonemptyStructure`),
      `RecSeqBody.toSafeBodyUnit` of the whole-body `seqRoot_recseqbody` — NO locate, NO `SeqPathAllSeq`.
    * **NESTED** (`3 ≤ lo`): `nestedSeq_safeBodyUnit_of_locator`, which LOCATES the stored `RecSeqEntry`
      whose interior is `[lo,hi)` by walking an all-seq bracket SPINE — so it carries the locator's
      `h_path : SeqPathAllSeq tokens (lo - 1)` (EVERY enclosing frame is `[`-typed).

    **The `SeqPathAllSeq` gate is a NEW guard conjunct, not a projection.**  `SeqPathAllSeq tokens (lo-1)`
    is STRICTLY STRONGER than the joint-induction guard's `SeqEnclosed tokens lo` (top frame only) — a seq
    reached through a map (`[{a:[b]}]`'s `[b]`) is `SeqEnclosed` but NOT `SeqPathAllSeq` (a `false` sits
    deeper in the stack), proven by `SeqPathAllSeqGateProbe` (`#guard`: same TOP `some true`, different
    `s.all`).  So the joint induction CANNOT derive it from `FlowBodyWindow`/`FlowBodyContentDeep`/
    `SeqEnclosed`; it must THREAD `SeqPathAllSeq tokens (lo-1)` through its guard for nested windows.  This
    is sound — the seq recursion only ever descends `[`→`[` (the `{` branch is the near-leaf map oracle, no
    seq IH, line 2709), so every window it visits is all-seq-path — but it is a genuine descend-edge
    obligation (the btFold-push preservation of `SeqPathAllSeq` across a located `[`), the next residual.
    The root is the SOLE exception: `SeqPathAllSeq tokens 1` FAILS (empty stack before the outer `[`,
    `SeqPathAllSeqGateProbe`), which is exactly why the root arm uses the flat producer
    ([[ref-root-seed-discriminator-not-from-gate]]).

    This wrapper NAMES the exact `h_safe` interface the joint induction consumes and isolates the
    `SeqPathAllSeq`-threading as the nested arm's lone non-emission hypothesis
    ([[ref-consumer-joint-before-producer]] / [[ref-parametric-assembler-extraction]]).  Composes only
    landed lemmas, references no sorry site, frontier sorry count unchanged at 4; axiom-clean. -/
theorem seqWindow_safeBodyUnit
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v)
    (h_disp : (lo = 2 ∧ hi = tokens.size - 2)
              ∨ (SeqTypedInterior tokens lo hi ∧ tokens[hi]!.val = .flowSequenceEnd
                 ∧ flowBracketBalance tokens (lo - 1) lo = 1 ∧ SeqPathAllSeq tokens (lo - 1)
                 ∧ 2 + 1 ≤ lo ∧ lo < hi ∧ hi < tokens.size - 2)) :
    SafeBodyUnit ContentStartTok ((tokens.toList.take hi).drop lo) := by
  rcases h_disp with ⟨hlo, hhi⟩ | ⟨h_typed, h_close, h_opener, h_path, h_win_lo, h_win_ab, h_win_hi⟩
  · subst hlo; subst hhi
    exact seqRoot_safeBodyUnit items tokens h_scan h_ne h_all
  · exact nestedSeq_safeBodyUnit_of_locator items tokens lo hi h_scan h_ne h_all
      h_typed h_close h_opener h_path h_win_lo h_win_ab h_win_hi

end L4YAML.Proofs.EmitterScannability
