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

/-- **The seq ROOT CARRIER reduced to the width CO-CONSTRUCTION** — `(i'-b-B2c-(d) — STEP D)`, R443.
    Produces `SeqInteriorSeparators tokens 2 (tokens.size - 2)` (the root carrier
    `seqRoot_seqInteriorSeparators` builds from its `desc` argument) from a SINGLE residual hypothesis
    `h_widthEnc` — the per-window enclosing-facts + width-recursion IH supplier.

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
    SeqInteriorSeparators tokens 2 (tokens.size - 2) := by
  apply seqRoot_seqInteriorSeparators items tokens h_scan h_ne h_all
  intro a b h2a hab hb _hbal hgate
  have h_a_sz : a ≤ tokens.size := by omega
  obtain ⟨p, h_pa, h_delta, h_body_bal, h_loc_floor⟩ :=
    seqEnclosingOpener_of_gate tokens a b h_a_sz hgate
  obtain ⟨hi, h_b_hi, h_hi_sz, h_window, h_deep, h_content, h_ih⟩ :=
    h_widthEnc a b p h2a hab hb hgate h_pa h_delta h_body_bal h_loc_floor
  have h_q_succ : SeqEnclosed tokens (p + 1) :=
    seqEnclosed_succ_of_located_opener tokens a p h_pa h_a_sz h_delta h_body_bal h_loc_floor hgate.2.1
  exact seqDescent_provider_of_located tokens a b p hi h_pa hab h_b_hi h_delta h_body_bal
    h_loc_floor hgate h_window h_deep h_content (SeqEnclosed tokens) h_q_succ h_ih

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

end L4YAML.Proofs.EmitterScannability
