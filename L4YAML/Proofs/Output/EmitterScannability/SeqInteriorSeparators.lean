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
  obtain ⟨j, h_pj, h_jhi, h_jclose, h_inner⟩ :=
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
    (h_ih : ∀ lo' hi', hi' - lo' < hi - p →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' →
        RecSeqBody ((tokens.toList.take hi').drop lo'))
    (h_pj : p < j) (h_jhi : j < hi) (h_jclose : tokens[j]!.val = .flowSequenceEnd)
    (h_inner : flowBracketBalance tokens (p + 1) j = 0)
    (h_floor : ∀ i, p < i → i ≤ j → flowBracketBalance tokens p i ≥ 1) :
    SafeBodyUnit ContentStartTok ((tokens.toList.take j).drop (p + 1)) :=
  ((recseqentry_seqbracket_oracle tokens p hi h_window h_deep h_content h_open h_ih)
    j h_pj h_jhi h_jclose h_inner h_floor).1.toSafeBodyUnit

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

end L4YAML.Proofs.EmitterScannability
