/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Proofs.Scanner.PendingKeySound
public import L4YAML.Proofs.Coupling.TabIndentBridge

@[expose] public section Blanket

/-!
# The register witness, stated and seeded (DOCS item 342)

Item 340 built the flip (`PackAlt sc := ExplicitValueRefused sc`) to a fixpoint
and found 72 consumer sites STARVED: a park whose register is LIVE owes the
informative side of its pack — the `?` the register names and that `?`'s route
to the stream — and nothing in the scanner state said which `?` that was.
Item 338's `Sound` ties the register to the innermost marked slot of
`pendingKeys`; this module ties each marked slot to a surface `?`:

* `AtCol input c sp` — `sp` is a suffix of `input` standing at column `c`.
  Item 341 named this relation `AtLineCol`; the LINE half is not stated.  No
  fact in the tree relates `sc.line` to the input (`ScannerSurfCorr` carries
  `col_eq` and `input_prefix`, nothing about newlines), so a line component
  would have no cursor bridge and the seed could not pay it.  No consumer reads
  the register's line (item 338 deleted the hook's `line != ekLine` guard), so
  the column and the suffix are the whole of what the witness must say.
* `QuestionEntry input sp_start c sp_q` — the informative side of the
  `?`-entry pack, keyed by the `?`'s column: `sp_q` stands at `c`, reads `?`,
  and every `[186]` entry it opens closes the stream.
* `SlotWitness input sc sp_start i` — a marked slot `pendingKeys[i] = some l` at
  column `indentColumns[i] = c` has a `QuestionEntry` at `c` in `input` — the
  stream's constant, taken as a parameter rather than read off `sc.input` so no
  writer owes an input-preservation lemma (item 343).
* `RegWitness sc sp_start` — outside flow, a live register `(some l, c)` has a
  `QuestionEntry` at `c`; `regWitness_of_slots` derives it from `RegOk` and
  the slot witnesses (`innermost_some_mem`), so the writers carry the slots.
* `scanKey_witness` — the seed: the `?` just scanned is `sp_q`, its route is
  the premise `question_open_map` already holds (`h_expl`'s informative side).

The writer lemmas through `scanNextToken` are item 343's; the flip that reads
`inl`/`inr` off the register is item 344's.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.RegisterWitness

open L4YAML.Scanner
open L4YAML.Surface
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.PendingKeySound
open L4YAML.Proofs.IndentStackBase (SentinelBase)
open L4YAML.Proofs.CloseStaleExplicitKey
open L4YAML.Proofs.PendingKeysStable

/-! ## §1  The relations -/

/-- `sp` is the suffix of `input` standing at column `c`. -/
def AtCol (input : String) (c : Nat) (sp : SurfPos) : Prop :=
  sp.col = c ∧ ∃ pre : List Char, input.toList = pre ++ sp.chars

/-- The cursor bridge: the scanner's own surface position stands at its column. -/
lemma AtCol.of_corr {sc : ScannerState} {sp : SurfPos} (h : ScannerSurfCorr sc sp) :
    AtCol sc.input sc.col sp :=
  ⟨h.col_eq, let ⟨pre, hpre, _⟩ := h.input_prefix; ⟨pre, hpre⟩⟩

/-- Where the `?` landed (item 343): a stream reaches the column-0 line position `sp_land`,
    and `sp_q` stands `c` spaces into it — exactly what the `?` opener holds
    (`question_open_map`'s `h_stream_land`/`hcol_land`/`h_ind`).  Item 342 stated the
    stream-closing route (`SBlockMapEntry c sp_q sp_v → SLYamlStream sp_start sp_v`) here;
    that needs the resume ladder the landing does not have, so it stays the consumer's. -/
def QuestionLanding (sp_start : SurfPos) (c : Nat) (sp_q : SurfPos) : Prop :=
  ∃ sp_land : SurfPos, SLYamlStream sp_start sp_land ∧ sp_land.col = 0 ∧ SIndent c sp_land sp_q

/-- The informative side of the `?`-entry pack, keyed by the `?`'s column `c`. -/
def QuestionEntry (input : String) (sp_start : SurfPos) (c : Nat) (sp_q : SurfPos) : Prop :=
  AtCol input c sp_q ∧ (∃ sp_q' : SurfPos, GLit '?' sp_q sp_q') ∧ QuestionLanding sp_start c sp_q

/-- A marked slot names a `?` at its level's column. -/
def SlotWitness (input : String) (sc : ScannerState) (sp_start : SurfPos) (i : Nat) : Prop :=
  ∀ l : Nat, sc.pendingKeys[i]? = some (some l) →
    ∃ (c : Nat) (sp_q : SurfPos), sc.indentColumns[i]? = some (c : Int) ∧
      QuestionEntry input sp_start c sp_q

/-- Item 354 — the value-line domain a park owes: every marked slot's column is in `ns`.
    `scanValue` emits the explicit-key `:` only at the innermost marked column, so this is
    the exact domain of the `∃ ns` faces (`MarkedSlotsEnclosing` pins that after a landing
    the marked slots are the strictly enclosing `?`s). -/
def MarkedColsIn (sc : ScannerState) (ns : List Nat) : Prop :=
  ∀ (i l : Nat) (c : Int), sc.pendingKeys[i]? = some (some l) →
    sc.indentColumns[i]? = some c → c.toNat ∈ ns

/-- Item 405 (Rule 8): the marked columns READ OFF the state — the projection that
    re-indexes the `?`-park chain fields (`pendingBlock.h_kslot` and its content twin),
    so they carry no `∃ ns` binder: every slot `i` whose `pendingKeys` entry is a mark
    contributes its indent column. -/
def markedCols (sc : ScannerState) : List Nat :=
  (List.range sc.pendingKeys.size).filterMap fun i =>
    match sc.pendingKeys[i]?, sc.indentColumns[i]? with
    | some (some _), some c => some c.toNat
    | _, _ => none

lemma markedCols_mem {sc : ScannerState} {x : Nat} :
    x ∈ markedCols sc ↔ ∃ (i l : Nat) (c : Int),
      sc.pendingKeys[i]? = some (some l) ∧ sc.indentColumns[i]? = some c ∧ c.toNat = x := by
  simp only [markedCols, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, _, h⟩
    revert h
    cases hpk : sc.pendingKeys[i]? with
    | none => simp
    | some pk =>
      cases pk with
      | none => simp
      | some l =>
        cases hc : sc.indentColumns[i]? with
        | none => simp
        | some c =>
          intro h
          simp only [Option.some.injEq] at h
          exact ⟨i, l, c, hpk, hc, h⟩
  · rintro ⟨i, l, c, hpk, hc, rfl⟩
    exact ⟨i, (Array.getElem?_eq_some_iff.mp hpk).1, by rw [hpk, hc]⟩

/-- `markedCols` reads `pendingKeys` and `indents` only (item 408): two states that agree on both
    project the same chain — the flow carrier's two conjuncts move it from the open to the close. -/
lemma markedCols_congr {s s' : ScannerState}
    (hpk : s'.pendingKeys = s.pendingKeys) (hind : s'.indents = s.indents) :
    markedCols s' = markedCols s := by
  unfold markedCols ScannerState.indentColumns
  rw [hpk, hind]

/-- The projection IS a domain: every mark's column is in it. -/
lemma MarkedColsIn.self (sc : ScannerState) : MarkedColsIn sc (markedCols sc) :=
  fun i l c hi hc => markedCols_mem.mpr ⟨i, l, c, hi, hc, rfl⟩

/-- The empty projection is the empty cover: a state with `markedCols sc = []` holds no mark
    (item 410 — the markless face's refusal reads it). -/
lemma MarkedColsIn.of_markedCols_nil {sc : ScannerState} (h : markedCols sc = []) :
    MarkedColsIn sc [] :=
  fun i l c hi hc => by rw [← h]; exact markedCols_mem.mpr ⟨i, l, c, hi, hc, rfl⟩

/-- Spend a chain's routes at the projection: a domain `ns` of `s'` and a route for
    every member of `ns` give a route for every marked column of `s'`.  Births use it
    with `s' = sc` and the chain they hold; relays with `MarkedColsIn.self` transported
    across the step. -/
lemma MarkedColsIn.relay {s' : ScannerState} {ns : List Nat} {P : Nat → Prop}
    (h : MarkedColsIn s' ns) (hP : ∀ nv ∈ ns, P nv) : ∀ nv ∈ markedCols s', P nv := by
  intro nv hnv
  obtain ⟨i, l, c, hi, hc, rfl⟩ := markedCols_mem.mp hnv
  exact hP _ (h i l c hi hc)

/-- A domain is kept by any superset. -/
lemma MarkedColsIn.mono {sc : ScannerState} {ns ns' : List Nat}
    (h : MarkedColsIn sc ns) (hsub : ∀ x, x ∈ ns → x ∈ ns') : MarkedColsIn sc ns' :=
  fun i l c hi hc => hsub _ (h i l c hi hc)

lemma MarkedColsIn.union_left {sc : ScannerState} {ns ns' : List Nat}
    (h : MarkedColsIn sc ns) : MarkedColsIn sc (ns ++ ns') :=
  h.mono fun _ hx => List.mem_append_left _ hx

/-- Transport along a step that moves neither field the domain reads. -/
lemma MarkedColsIn.transport {s s' : ScannerState} {ns : List Nat}
    (h : MarkedColsIn s ns)
    (hpk : s'.pendingKeys = s.pendingKeys) (hind : s'.indents = s.indents) :
    MarkedColsIn s' ns := by
  intro i l c hi hc
  rw [hpk] at hi
  rw [ScannerState.indentColumns, hind] at hc
  exact h i l c hi hc

/-- `closeStale` empties slots and re-marks none. -/
lemma MarkedColsIn.closeStale {s : ScannerState} {ns : List Nat}
    (h : MarkedColsIn s ns) (c : Char) : MarkedColsIn (s.closeStaleAt c) ns := by
  intro i l col hi hc
  simp only [ScannerState.closeStaleAt] at hi hc
  exact h i l col (closeStale_marked _ _ _ _ _ _ _ hi) hc

/-- A popped level takes its slot with it; the slots below keep their columns. -/
lemma MarkedColsIn.pop {s s' : ScannerState} {ns : List Nat}
    (h : MarkedColsIn s ns)
    (hind : s'.indents = s.indents.pop) (hpk : s'.pendingKeys = s.pendingKeys.pop) :
    MarkedColsIn s' ns := by
  intro i l c hi hc
  rw [hpk, Array.getElem?_pop] at hi
  split at hi
  · rw [indentColumns_getElem?, hind, Array.getElem?_pop] at hc
    split at hc
    · rw [← indentColumns_getElem?] at hc
      exact h i l c hi hc
    · cases hc
  · cases hi

/-- Every marked slot names a `?`. -/
def SlotsWitness (input : String) (sc : ScannerState) (sp_start : SurfPos) : Prop :=
  ∀ i : Nat, SlotWitness input sc sp_start i

/-- Outside flow, a live register names a `?` at its column. -/
def RegWitness (input : String) (sc : ScannerState) (sp_start : SurfPos) : Prop :=
  sc.flowLevel = 0 → ∀ (l : Nat) (c : Int),
    sc.explicitKeyLine = some l → sc.explicitKeyCol = c →
    ∃ (cn : Nat) (sp_q : SurfPos), c = (cn : Int) ∧ QuestionEntry input sp_start cn sp_q

/-- The register's witness is the innermost marked slot's (`RegOk`). -/
lemma regWitness_of_slots {input : String} {sc : ScannerState} {sp_start : SurfPos}
    (hreg : RegOk sc) (hw : SlotsWitness input sc sp_start) : RegWitness input sc sp_start := by
  intro h0 l c hl hc
  have hinn : PendingKeys.innermost sc.indentColumns sc.pendingKeys = (some l, c) := by
    rw [← innermostPendingKey_eq, ← hreg h0, hl, hc]
  obtain ⟨i, _, hi, hci⟩ := innermost_some_mem _ _ _ _ hinn
  obtain ⟨cn, sp_q, hcol, hq⟩ := hw i l hi
  refine ⟨cn, sp_q, ?_, hq⟩
  rw [hcol] at hci
  simpa using hci.symm

/-- Transport along a step that moves neither field the witness reads.  (The input is the
    stream's constant — a parameter, not a field — so no step has to preserve it.) -/
lemma SlotsWitness.transport {input : String} {s s' : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start)
    (hpk : s'.pendingKeys = s.pendingKeys) (hind : s'.indents = s.indents) :
    SlotsWitness input s' sp_start := by
  intro i l hi
  rw [hpk] at hi
  obtain ⟨c, sp_q, hc, hq⟩ := h i l hi
  exact ⟨c, sp_q, by rw [ScannerState.indentColumns, hind]; exact hc, hq⟩

/-! ## §2  The seed -/

lemma scanKey_input {s s' : ScannerState} (hok : scanKey s = .ok s') : s'.input = s.input := by
  unfold scanKey at hok
  simp only [bind, Except.bind] at hok
  repeat' split at hok
  all_goals first
    | (simp only [Except.ok.injEq] at hok
       subst hok
       show (ScannerState.advance (ScannerState.emit _ _)).input = _
       rw [advance_input]
       simp [ScannerState.emit, L4YAML.Proofs.ScannerProgress.pushMappingIndent_input])
    | simp_all

/-- Below the top, `pushMappingIndent` moves neither a slot nor a column. -/
lemma pushMappingIndent_getElem?_of_lt (s : ScannerState) (col : Int) (i : Nat)
    (hi : i < s.indents.size) (hsz : s.pendingKeys.size = s.indents.size) :
    (pushMappingIndent s col).pendingKeys[i]? = s.pendingKeys[i]? ∧
    (pushMappingIndent s col).indentColumns[i]? = s.indentColumns[i]? := by
  unfold pushMappingIndent
  split
  · simp only [ScannerState.indentColumns, ScannerState.emit]
    constructor
    · rw [Array.getElem?_push, if_neg (by omega)]
    · rw [Array.map_push, Array.getElem?_push, if_neg (by simpa using Nat.ne_of_lt hi)]
  · exact ⟨rfl, rfl⟩

/-- **The seed.**  A `?` scanned outside flow marks the level at its own column, and
    the `?` itself is the witness: the surface position the cursor stood on reads `?`
    (`peek_corr`), stands at the register's column (`AtCol.of_corr`), and its
    `[186]` route is the premise the `?` producer holds. -/
lemma scanKey_witness {s s' : ScannerState} {sp sp_start : SurfPos}
    (hcorr : ScannerSurfCorr s sp) (h_noflow : s.inFlow = false)
    (hok : scanKey s = .ok s') (hs : SlotsOk s) (hbase : SentinelBase s)
    (hcol : s.currentIndent ≤ (s.col : Int)) (hpeek : s.peek? = some '?')
    (h_land : QuestionLanding sp_start s.col sp)
    (hw : SlotsWitness s.input s sp_start) : SlotsWitness s.input s' sp_start := by
  have hind := L4YAML.Proofs.PreprocessIndentStable.scanKey_indents h_noflow hok
  have hpk := scanKey_pendingKeys h_noflow hok
  obtain ⟨pm, hpm⟩ : ∃ pm, pm = pushMappingIndent s (s.col : Int) := ⟨_, rfl⟩
  rw [← hpm] at hind hpk
  have hsl : SlotsOk pm := hpm ▸ pushMappingIndent_slots s _ hs
  have hsz := hsl.1
  have hpos : 0 < pm.indents.size :=
    hpm ▸ (L4YAML.Proofs.IndentStackBase.pushMappingIndent_base s _ hbase).size_pos
  have htop_ci : pm.currentIndent = (s.col : Int) := by
    rw [hpm]
    exact Int.le_antisymm (L4YAML.Proofs.IndentStackCover.pushMappingIndent_top_le hcol)
      (L4YAML.Proofs.PreprocessIndentStable.pushMappingIndent_le s _)
  have htop : pm.indentColumns[pm.indents.size - 1]? = some (s.col : Int) := by
    rw [indentColumns_getElem?, Array.getElem?_eq_getElem (by omega)]
    simp only [Option.map_some]
    rw [← L4YAML.Proofs.IndentStackMono.currentIndent_eq_last hpos, htop_ci]
  have hcols' : s'.indentColumns = pm.indentColumns := by
    simp [ScannerState.indentColumns, hind]
  -- the `?` the cursor stands on
  have hmore : s.offset < s.inputEnd := by
    by_cases hne : s.offset < s.inputEnd
    · exact hne
    · simp [ScannerState.peek?, hne] at hpeek
  obtain ⟨c, rest, hchars, hpc⟩ := peek_corr s sp hcorr hmore
  rw [hpeek] at hpc
  have hc : c = '?' := (Option.some.inj hpc).symm
  subst hc
  have hq : QuestionEntry s.input sp_start s.col sp := by
    refine ⟨AtCol.of_corr hcorr, ⟨⟨rest, sp.col + 1⟩, ?_⟩, h_land⟩
    have : sp = ⟨'?' :: rest, sp.col⟩ := by cases sp; simp_all
    rw [this]; exact GLit.mk rest sp.col
  intro i l hi
  rw [hcols']
  rw [hpk, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hi
  split at hi
  · rename_i heq
    subst heq
    exact ⟨s.col, sp, htop, hq⟩
  · rename_i hne
    have hi' : i < pm.indents.size := by
      obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.1 hi
      omega
    by_cases hlt : i < s.indents.size
    · obtain ⟨hpk_i, hcol_i⟩ := hpm ▸ pushMappingIndent_getElem?_of_lt s (s.col : Int) i hlt hs.1
      rw [hpk_i] at hi
      obtain ⟨c, sp_q, hc, hq'⟩ := hw i l hi
      exact ⟨c, sp_q, by rw [hcol_i]; exact hc, hq'⟩
    · -- `i` is the pushed level's slot, which is empty
      exfalso
      rw [hpm] at hi
      unfold pushMappingIndent at hi
      have hsz0 := hs.1
      split at hi
      · simp only [ScannerState.emit] at hi
        rw [Array.getElem?_push] at hi
        split at hi
        · simp at hi
        · obtain ⟨hlt', _⟩ := Array.getElem?_eq_some_iff.1 hi
          omega
      · obtain ⟨hlt', _⟩ := Array.getElem?_eq_some_iff.1 hi
        omega


/-- **Item 357: the `?`'s own mark.**  A `?` scanned outside flow marks the level at its
    own column, so the marked columns after the scan are the old ones plus the `?`'s
    column — the domain `question_open_map` owes for `k :: ns`.  Lockstep (`SlotsOk`)
    is what pairs the marked slot with the pushed column. -/
lemma scanKey_markedCols {s s' : ScannerState} {ns : List Nat}
    (h_noflow : s.inFlow = false) (hok : scanKey s = .ok s') (hs : SlotsOk s)
    (hbase : SentinelBase s) (hcol : s.currentIndent ≤ (s.col : Int))
    (h : MarkedColsIn s ns) : MarkedColsIn s' ((s.col : Int).toNat :: ns) := by
  have hind := L4YAML.Proofs.PreprocessIndentStable.scanKey_indents h_noflow hok
  have hpk := scanKey_pendingKeys h_noflow hok
  obtain ⟨pm, hpm⟩ : ∃ pm, pm = pushMappingIndent s (s.col : Int) := ⟨_, rfl⟩
  rw [← hpm] at hind hpk
  have hsl : SlotsOk pm := hpm ▸ pushMappingIndent_slots s _ hs
  have hsz := hsl.1
  have hpos : 0 < pm.indents.size :=
    hpm ▸ (L4YAML.Proofs.IndentStackBase.pushMappingIndent_base s _ hbase).size_pos
  have htop_ci : pm.currentIndent = (s.col : Int) := by
    rw [hpm]
    exact Int.le_antisymm (L4YAML.Proofs.IndentStackCover.pushMappingIndent_top_le hcol)
      (L4YAML.Proofs.PreprocessIndentStable.pushMappingIndent_le s _)
  have htop : pm.indentColumns[pm.indents.size - 1]? = some (s.col : Int) := by
    rw [indentColumns_getElem?, Array.getElem?_eq_getElem (by omega)]
    simp only [Option.map_some]
    rw [← L4YAML.Proofs.IndentStackMono.currentIndent_eq_last hpos, htop_ci]
  have hcols' : s'.indentColumns = pm.indentColumns := by
    simp [ScannerState.indentColumns, hind]
  intro i l c hi hc
  rw [hcols'] at hc
  rw [hpk, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hi
  split at hi
  · rename_i heq
    subst heq
    rw [htop] at hc
    cases hc
    exact List.mem_cons_self
  · rename_i hne
    have hi' : i < pm.indents.size := by
      obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.1 hi
      omega
    by_cases hlt : i < s.indents.size
    · obtain ⟨hpk_i, hcol_i⟩ := hpm ▸ pushMappingIndent_getElem?_of_lt s (s.col : Int) i hlt hs.1
      rw [hpk_i] at hi
      rw [hcol_i] at hc
      exact List.mem_cons_of_mem _ (h i l c hi hc)
    · exfalso
      rw [hpm] at hi
      unfold pushMappingIndent at hi
      have hsz0 := hs.1
      split at hi
      · simp only [ScannerState.emit] at hi
        rw [Array.getElem?_push] at hi
        split at hi
        · simp at hi
        · obtain ⟨hlt', _⟩ := Array.getElem?_eq_some_iff.1 hi
          omega
      · obtain ⟨hlt', _⟩ := Array.getElem?_eq_some_iff.1 hi
        omega

/-! ## §3  The writers (DOCS item 343)

`SlotsWitness` reads `pendingKeys`, `indents` and `input` only, so a writer is one of
three shapes: a PUSH (one empty slot on top, the slots below untouched), a POP (the
top slot goes, the slots below untouched), or a CLOSE (`PendingKeys.closeAt`: a slot
is kept or emptied, never re-marked).  Everything else is `SlotsWitness.transport`. -/

/-- A pushed level's own slot is `none`; the slots below are the pre-state's. -/
lemma SlotsWitness.push {input : String} {s s' : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start)
    (e : IndentEntry) (hind : s'.indents = s.indents.push e)
    (hpk : s'.pendingKeys = s.pendingKeys.push none)
    (hsz : s.pendingKeys.size = s.indents.size) : SlotsWitness input s' sp_start := by
  intro i l hi
  rw [hpk, Array.getElem?_push] at hi
  split at hi
  · simp at hi
  · obtain ⟨c, sp_q, hc, hq⟩ := h i l hi
    refine ⟨c, sp_q, ?_, hq⟩
    rw [indentColumns_getElem?] at hc
    have hlt : i < s.indents.size := by
      rcases hx : s.indents[i]? with _ | e
      · simp [hx] at hc
      · exact (Array.getElem?_eq_some_iff.1 hx).1
    rw [indentColumns_getElem?, hind, Array.getElem?_push, if_neg (by omega)]
    exact hc

/-- Popping the top level keeps every remaining slot's witness. -/
lemma SlotsWitness.pop {input : String} {s s' : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start)
    (hind : s'.indents = s.indents.pop) (hpk : s'.pendingKeys = s.pendingKeys.pop)
    (hsz : s.pendingKeys.size = s.indents.size) :
    SlotsWitness input s' sp_start := by
  intro i l hi
  rw [hpk, Array.getElem?_pop] at hi
  split at hi
  · obtain ⟨c, sp_q, hc, hq⟩ := h i l hi
    refine ⟨c, sp_q, ?_, hq⟩
    rw [indentColumns_getElem?, hind, Array.getElem?_pop, if_pos (by omega)]
    rw [indentColumns_getElem?] at hc; exact hc
  · cases hi

/-- `closeAt` empties slots and re-marks none, so every slot still marked keeps its witness. -/
lemma SlotsWitness.close {input : String} {s : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) (col : Int) :
    SlotsWitness input (s.clearPendingKeyAt col) sp_start := by
  intro i l hi
  simp only [ScannerState.clearPendingKeyAt] at hi
  exact h i l (closeAt_marked _ _ _ _ _ hi).1

/-- `closeStale` empties slots and re-marks none, so every slot still marked keeps its witness. -/
lemma SlotsWitness.closeStale {input : String} {s : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) (c : Char) :
    SlotsWitness input (s.closeStaleAt c) sp_start := by
  intro i l hi
  simp only [ScannerState.closeStaleAt] at hi
  exact h i l (closeStale_marked _ _ _ _ _ _ _ hi)

lemma pushMappingIndent_witness {input : String} {s : ScannerState} {sp_start : SurfPos} (col : Int)
    (h : SlotsWitness input s sp_start) (hsz : s.pendingKeys.size = s.indents.size) :
    SlotsWitness input (pushMappingIndent s col) sp_start := by
  unfold pushMappingIndent
  split
  · exact h.push { column := col, isSequence := false } (by simp [ScannerState.emit])
      (by simp [ScannerState.emit]) hsz
  · exact h

lemma pushSequenceIndent_witness {input : String} {s : ScannerState} {sp_start : SurfPos} (col : Int)
    (h : SlotsWitness input s sp_start) (hsz : s.pendingKeys.size = s.indents.size) :
    SlotsWitness input (pushSequenceIndent s col) sp_start := by
  unfold pushSequenceIndent
  split
  · exact h.push { column := col, isSequence := true } (by simp [ScannerState.emit])
      (by simp [ScannerState.emit]) hsz
  · exact h

/-- The re-read writes the register only. -/
lemma readPendingKey_witness {input : String} {s : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) : SlotsWitness input s.readPendingKey sp_start := h

/-- The stale-key hook: the identity, or a close followed by the re-read. -/
lemma closeStaleExplicitKey_witness {input : String} {s : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) : SlotsWitness input (closeStaleExplicitKey s) sp_start := by
  rcases closeStaleExplicitKey_cases s with heq | ⟨_, _, heq⟩ <;> rw [heq]
  · exact h
  · exact readPendingKey_witness (h.closeStale _)

lemma unwindIndentsLoop_witness {input : String} (s : ScannerState) (col : Int) (fuel : Nat)
    {sp_start : SurfPos} (h : SlotsWitness input s sp_start) (hs : SlotsOk s) :
    SlotsWitness input (unwindIndentsLoop s col fuel) sp_start := by
  induction fuel generalizing s with
  | zero => simpa [unwindIndentsLoop] using h
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · obtain ⟨h1, h2, -⟩ := unwindPop_fields s
      exact ih _ (h.pop h1 h2 hs.1) (hs.pop h1 h2)
    · exact h

lemma unwindIndents_witness {input : String} (s : ScannerState) (col : Int) {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) (hs : SlotsOk s) :
    SlotsWitness input (unwindIndents s col) sp_start :=
  unwindIndentsLoop_witness s col _ h hs


/-! ### Item 354: the domain `MarkedColsIn` along the same writers -/

lemma MarkedColsIn.unwindLoop (s : ScannerState) (col : Int) (fuel : Nat) {ns : List Nat}
    (h : MarkedColsIn s ns) : MarkedColsIn (unwindIndentsLoop s col fuel) ns := by
  induction fuel generalizing s with
  | zero => simpa [unwindIndentsLoop] using h
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · obtain ⟨h1, h2, -⟩ := unwindPop_fields s
      exact ih _ (h.pop h1 h2)
    · exact h

lemma MarkedColsIn.unwind (s : ScannerState) (col : Int) {ns : List Nat}
    (h : MarkedColsIn s ns) : MarkedColsIn (unwindIndents s col) ns :=
  MarkedColsIn.unwindLoop s col _ h

lemma MarkedColsIn.readPendingKey {s : ScannerState} {ns : List Nat}
    (h : MarkedColsIn s ns) : MarkedColsIn s.readPendingKey ns :=
  h.transport rfl rfl

lemma MarkedColsIn.closeStaleExplicitKey {s : ScannerState} {ns : List Nat}
    (h : MarkedColsIn s ns) : MarkedColsIn (closeStaleExplicitKey s) ns := by
  rcases closeStaleExplicitKey_cases s with heq | ⟨_, _, heq⟩ <;> rw [heq]
  · exact h
  · exact (h.closeStale _).readPendingKey

/-! ### Batch 2: the `:`, the `-`, the document markers, the flow arms, the content arm -/

/-- A `closeAt` written as array equalities (the `:` arm's `settle`). -/
lemma SlotsWitness.closeAt_eq {input : String} {s s' : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) (col : Int)
    (hpk : s'.pendingKeys = PendingKeys.closeAt s.indentColumns s.pendingKeys col)
    (hind : s'.indents = s.indents) : SlotsWitness input s' sp_start := by
  intro i l hi
  rw [hpk] at hi
  obtain ⟨c, sp_q, hc, hq⟩ := h i l (closeAt_marked _ _ _ _ _ hi).1
  exact ⟨c, sp_q, by rw [ScannerState.indentColumns, hind]; exact hc, hq⟩

lemma scanValueClearKey_witness {input : String} {s : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) : SlotsWitness input (scanValueClearKey s) sp_start :=
  h.transport (scanValueClearKey_core s).2.1 (scanValueClearKey_core s).1

lemma scanValuePrepare_witness {input : String} {s : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) (hsz : s.pendingKeys.size = s.indents.size) :
    SlotsWitness input (scanValuePrepare s) sp_start := by
  unfold scanValuePrepare
  split
  · split
    · split
      · exact h.push _ rfl rfl hsz
      · exact h
    · exact h
  · split
    · exact h
    · split
      · exact pushMappingIndent_witness _ h hsz
      · exact h

/-- The `:` arm: clear-key and prepare (a push at most), emit, advance, then `settle` keeps the
    slots or closes the explicit key's level. -/
lemma scanValue_witness {input : String} {s s' : ScannerState} {sp_start : SurfPos}
    (hok : scanValue s = .ok s') (h : SlotsWitness input s sp_start) (hs : SlotsOk s) :
    SlotsWitness input s' sp_start := by
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  simp only [Except.ok.injEq] at hok
  subst hok
  have hs_kc : SlotsOk (scanValueClearKey s) := by
    refine ⟨by rw [(scanValueClearKey_core s).2.1, (scanValueClearKey_core s).1]; exact hs.1, ?_⟩
    intro i l hi
    have hcols : (scanValueClearKey s).indentColumns = s.indentColumns := by
      simp [ScannerState.indentColumns, (scanValueClearKey_core s).1]
    rw [hcols]; exact hs.2 i l ((scanValueClearKey_core s).2.1 ▸ hi)
  have hw_p : SlotsWitness input (scanValuePrepare (scanValueClearKey s)) sp_start :=
    scanValuePrepare_witness (scanValueClearKey_witness h) hs_kc.1
  have hadv_pk : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).pendingKeys
      = (scanValuePrepare (scanValueClearKey s)).pendingKeys := by
    rw [advance_preserves_pendingKeys, emit_pendingKeys]
  have hadv_ind : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).indents
      = (scanValuePrepare (scanValueClearKey s)).indents := by
    rw [L4YAML.Proofs.EmitterScannability.advance_preserves_indents]; rfl
  have hw_adv : SlotsWitness input (((scanValuePrepare (scanValueClearKey s)).emit .value).advance)
      sp_start := hw_p.transport hadv_pk hadv_ind
  split
  · exact hw_adv.transport rfl rfl
  · split
    · exact hw_adv.transport rfl rfl
    · exact hw_adv.closeAt_eq _ rfl rfl

lemma scanBlockEntry_witness {input : String} {s s' : ScannerState} {sp_start : SurfPos}
    (hnf : s.inFlow = false) (hok : scanBlockEntry s = .ok s')
    (h : SlotsWitness input s sp_start) (hs : SlotsOk s) : SlotsWitness input s' sp_start :=
  (pushSequenceIndent_witness (s.col : Int) h hs.1).transport
    (scanBlockEntry_pendingKeys hnf hok)
    (L4YAML.Proofs.PreprocessIndentStable.scanBlockEntry_indents hnf hok)

/-! ### Item 357: the domain `MarkedColsIn` along the block writers

Mirrors of the `SlotsWitness` writers above: a PUSH adds an empty slot (no new mark), a
CLOSE keeps or empties a slot, and the `?` mark is `scanKey_markedCols`.  Every block
indicator step therefore lands in the domain `(s.col).toNat :: ns` — the `?`'s own
column joins, the others only shrink. -/

lemma MarkedColsIn.push {s s' : ScannerState} {ns : List Nat}
    (h : MarkedColsIn s ns)
    (e : IndentEntry) (hind : s'.indents = s.indents.push e)
    (hpk : s'.pendingKeys = s.pendingKeys.push none)
    (hsz : s.pendingKeys.size = s.indents.size) : MarkedColsIn s' ns := by
  intro i l c hi hc
  rw [hpk, Array.getElem?_push] at hi
  split at hi
  · simp at hi
  · have hlt : i < s.pendingKeys.size := (Array.getElem?_eq_some_iff.1 hi).1
    rw [indentColumns_getElem?, hind, Array.getElem?_push, if_neg (by omega)] at hc
    exact h i l c hi (by rw [indentColumns_getElem?]; exact hc)

lemma MarkedColsIn.closeAt_eq {s s' : ScannerState} {ns : List Nat}
    (h : MarkedColsIn s ns) (col : Int)
    (hpk : s'.pendingKeys = PendingKeys.closeAt s.indentColumns s.pendingKeys col)
    (hind : s'.indents = s.indents) : MarkedColsIn s' ns := by
  intro i l c hi hc
  rw [hpk] at hi
  rw [ScannerState.indentColumns, hind] at hc
  exact h i l c (closeAt_marked _ _ _ _ _ hi).1 hc

lemma pushSequenceIndent_markedCols {s : ScannerState} {ns : List Nat} (col : Int)
    (h : MarkedColsIn s ns) (hsz : s.pendingKeys.size = s.indents.size) :
    MarkedColsIn (pushSequenceIndent s col) ns := by
  unfold pushSequenceIndent
  split
  · exact h.push { column := col, isSequence := true } (by simp [ScannerState.emit])
      (by simp [ScannerState.emit]) hsz
  · exact h

lemma pushMappingIndent_markedCols {s : ScannerState} {ns : List Nat} (col : Int)
    (h : MarkedColsIn s ns) (hsz : s.pendingKeys.size = s.indents.size) :
    MarkedColsIn (pushMappingIndent s col) ns := by
  unfold pushMappingIndent
  split
  · exact h.push { column := col, isSequence := false } (by simp [ScannerState.emit])
      (by simp [ScannerState.emit]) hsz
  · exact h

lemma scanValueClearKey_markedCols {s : ScannerState} {ns : List Nat}
    (h : MarkedColsIn s ns) : MarkedColsIn (scanValueClearKey s) ns :=
  h.transport (scanValueClearKey_core s).2.1 (scanValueClearKey_core s).1

lemma scanValuePrepare_markedCols {s : ScannerState} {ns : List Nat}
    (h : MarkedColsIn s ns) (hsz : s.pendingKeys.size = s.indents.size) :
    MarkedColsIn (scanValuePrepare s) ns := by
  unfold scanValuePrepare
  split
  · split
    · split
      · exact h.push _ rfl rfl hsz
      · exact h
    · exact h
  · split
    · exact h
    · split
      · exact pushMappingIndent_markedCols _ h hsz
      · exact h

lemma scanValue_markedCols {s s' : ScannerState} {ns : List Nat}
    (hok : scanValue s = .ok s') (h : MarkedColsIn s ns) (hs : SlotsOk s) :
    MarkedColsIn s' ns := by
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  simp only [Except.ok.injEq] at hok
  subst hok
  have hsz_kc : (scanValueClearKey s).pendingKeys.size = (scanValueClearKey s).indents.size := by
    rw [(scanValueClearKey_core s).2.1, (scanValueClearKey_core s).1]; exact hs.1
  have hw_p : MarkedColsIn (scanValuePrepare (scanValueClearKey s)) ns :=
    scanValuePrepare_markedCols (scanValueClearKey_markedCols h) hsz_kc
  have hadv_pk : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).pendingKeys
      = (scanValuePrepare (scanValueClearKey s)).pendingKeys := by
    rw [advance_preserves_pendingKeys, emit_pendingKeys]
  have hadv_ind : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).indents
      = (scanValuePrepare (scanValueClearKey s)).indents := by
    rw [L4YAML.Proofs.EmitterScannability.advance_preserves_indents]; rfl
  have hw_adv : MarkedColsIn (((scanValuePrepare (scanValueClearKey s)).emit .value).advance) ns :=
    hw_p.transport hadv_pk hadv_ind
  split
  · exact hw_adv.transport rfl rfl
  · split
    · exact hw_adv.transport rfl rfl
    · exact hw_adv.closeAt_eq _ rfl rfl

/-- Marks only at column `nv` and the register live ⇒ the register's column IS `nv`. -/
lemma explicitKeyCol_of_marked {s : ScannerState} {nv i l : Nat} (hs : Sound s) (hfl : s.flowLevel = 0)
    (hm : MarkedColsIn s [nv]) (hi : s.pendingKeys[i]? = some (some l)) :
    s.explicitKeyLine.isSome = true ∧ s.explicitKeyCol = (nv : Int) := by
  have hr := hs.reg hfl
  rw [innermostPendingKey_eq, innermost_eq_go] at hr
  have hi' : i < s.pendingKeys.size := by
    rcases Nat.lt_or_ge i s.pendingKeys.size with hlt | hge
    · exact hlt
    · simp [Array.getElem?_eq_none_iff.mpr hge] at hi
  have hne := go_fst_some_of_marked s.indentColumns s.pendingKeys _ i l hi' hi
  cases hgo : go s.indentColumns s.pendingKeys s.pendingKeys.size with
  | mk ol c =>
    rw [hgo] at hr hne
    cases ol with
    | none => exact absurd rfl hne
    | some l' =>
      obtain ⟨j, -, hj, hcj⟩ := go_some_mem _ _ _ _ _ hgo
      obtain ⟨cj, hcj', hcj0⟩ := hs.slots.2 j l' hj
      have hmem := hm j l' cj hj hcj'
      simp only [List.mem_singleton] at hmem
      rw [hcj'] at hcj; simp only [Option.getD_some] at hcj
      have hprod := Prod.mk.inj hr
      refine ⟨by rw [hprod.1]; rfl, ?_⟩
      rw [hprod.2, ← hcj]; omega



/-- **The explicit `:` under an OUTERMOST `?` kills the register** (item 359, K7's payer): when
    every marked slot sits at the `:`'s own column `nv` and the only simple key possible is the
    cursor's, the `:` is the explicit value ([197]), closes the level and re-reads an empty stack.
    Capstone chain (Rule 1): Group 7.2 `scan_content_gives_stream_v2` ← `scanNextToken_accum_step`
    ← `accum_block_pending` ← `accum_block_on_closeThenBlock`/`_pendingBlockContent`/`_pendingBlock`
    ← `colon_open_map_explicit`/`compact_open_map`, whose `PendingNode.pendingMapValue` value-park
    faces pay `PackAlt.ofRefused` from this lemma once the park's `Sound`, `MarkedColsIn` domain and
    the preprocess simple-key fact reach them (item 360); until then it has no library caller. -/
lemma scanValue_refused_of_outer {s s' : ScannerState} {nv : Nat}
    (hok : scanValue s = .ok s') (hs : Sound s) (hfl : s.flowLevel = 0)
    (hm : MarkedColsIn s [nv]) (hcol : s.col = nv)
    (hkey : s.simpleKey.possible = true → s.simpleKey.pos.col = s.col) :
    s'.explicitKeyLine = none := by
  have hs' : Sound s' := scanValue_sound hok hs
  have hfl' : s'.flowLevel = 0 := by
    rw [L4YAML.Proofs.ScannerCorrectness.scanValue_preserves_flowLevel s s' hok]; exact hfl
  by_cases hmk : ∃ (i l : Nat), (s.pendingKeys[i]? : Option (Option Nat)) = some (some l)
  · obtain ⟨i, l, hi⟩ := hmk
    obtain ⟨hsome, hekc⟩ := explicitKeyCol_of_marked hs hfl hm hi
    have h_noflow : s.inFlow = false := (inFlow_false_iff s).2 hfl
    have h_kc : (scanValueClearKey s).explicitKeyCol = s.explicitKeyCol :=
      L4YAML.Proofs.ExplicitKeyCoupling.scanValueClearKey_preserves_explicitKeyCol s
    have h_kl : (scanValueClearKey s).explicitKeyLine = s.explicitKeyLine :=
      L4YAML.Proofs.ExplicitKeyCoupling.scanValueClearKey_preserves_explicitKeyLine s
    have h_sk := L4YAML.Proofs.PreprocessIndentStable.scanValueClearKey_simpleKey s
    obtain ⟨hck1, hck2, hck3, hck4, hck5, hck6⟩ := scanValueClearKey_core s
    have hs_kc : SlotsOk (scanValueClearKey s) := by
      refine ⟨by rw [hck1, hck2]; exact hs.slots.1, ?_⟩
      intro j l' hj; rw [hck2] at hj
      have hcols : (scanValueClearKey s).indentColumns = s.indentColumns := by
        simp [ScannerState.indentColumns, hck1]
      rw [hcols]; exact hs.slots.2 j l' hj
    have hsz_kc : (scanValueClearKey s).pendingKeys.size = (scanValueClearKey s).indents.size := by
      rw [hck2, hck1]; exact hs.slots.1
    obtain ⟨hp1, -, -, -, -, -⟩ := scanValuePrepare_core _ hs_kc
    have hw_p : MarkedColsIn (scanValuePrepare (scanValueClearKey s)) [nv] :=
      scanValuePrepare_markedCols (scanValueClearKey_markedCols hm) hsz_kc
    have hadv_pk : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).pendingKeys
        = (scanValuePrepare (scanValueClearKey s)).pendingKeys := by
      rw [advance_preserves_pendingKeys, emit_pendingKeys]
    have hadv_ind : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).indents
        = (scanValuePrepare (scanValueClearKey s)).indents := by
      rw [L4YAML.Proofs.EmitterScannability.advance_preserves_indents]; rfl
    have hadv_cols : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).indentColumns
        = (scanValuePrepare (scanValueClearKey s)).indentColumns := by
      simp [ScannerState.indentColumns, hadv_ind]
    have hw_adv : MarkedColsIn (((scanValuePrepare (scanValueClearKey s)).emit .value).advance) [nv] :=
      hw_p.transport hadv_pk hadv_ind
    have hadv_slots : SlotsOk (((scanValuePrepare (scanValueClearKey s)).emit .value).advance) := by
      refine ⟨by rw [hadv_pk, hadv_ind]; exact hp1.1, ?_⟩
      intro j l' hj; rw [hadv_pk] at hj; rw [hadv_cols]; exact hp1.2 j l' hj
    unfold scanValue at hok
    simp only [bind, Except.bind] at hok
    split at hok <;> try contradiction
    split at hok <;> try contradiction
    split at hok <;> try contradiction
    simp only [Except.ok.injEq] at hok
    subst hok
    show (if s.inFlow = true then _
        else if _ then (_, (scanValueClearKey s).explicitKeyLine, _)
        else PendingKeys.close _ _ (scanValueClearKey s).explicitKeyCol).2.1 = none
    rw [ite_eq_right (by simp [h_noflow])]
    by_cases hsv : scanValueKeySurvives s (scanValueClearKey s) = true
    · rw [ite_eq_left hsv]
      exfalso
      unfold scanValueKeySurvives at hsv
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hsv
      rcases hsv with ⟨-, h0 | ⟨-, hgt⟩⟩
      · rw [h_kl] at h0; simp [hsome] at h0
      · rw [h_kc, hekc] at hgt
        split at hgt
        · rename_i h_poss_kc
          rcases h_sk with h_eq | h_false
          · rw [h_eq] at hgt h_poss_kc
            rw [hkey h_poss_kc, hcol] at hgt
            exact absurd hgt (Int.lt_irrefl _)
          · rw [h_false] at h_poss_kc; cases h_poss_kc
        · rw [hcol] at hgt; exact absurd hgt (Int.lt_irrefl _)
    · rw [ite_eq_right hsv]
      show (PendingKeys.innermost _ (PendingKeys.closeAt _ _ _)).1 = none
      apply innermost_fst_none_of_noMarks
      intro j l' hj
      obtain ⟨hmark, hne⟩ := closeAt_marked _ _ _ _ _ hj
      obtain ⟨cj, hcj, hcj0⟩ := hadv_slots.2 j l' hmark
      have hmem := hw_adv j l' cj hmark hcj
      simp only [List.mem_singleton] at hmem
      apply hne
      rw [hcj, h_kc, hekc]
      congr 1; omega
  · have hm0 : MarkedColsIn s [] := by
      intro j l' c hj _; exact absurd ⟨j, l', hj⟩ hmk
    have hm0' := scanValue_markedCols hok hm0 hs.slots
    apply explicitKeyLine_none_of_noMarks hs' hfl'
    intro j l' hj
    obtain ⟨c, hc, -⟩ := hs'.slots.2 j l' hj
    have := hm0' j l' c hj hc
    simp at this

/-- **An EMPTY marked domain is the dead register** (item 361, the flow lane's payer): with no
    marked slot at all (`MarkedColsIn s []` under `SlotsOk`, which gives every marked slot a column)
    the innermost pending key is `(none, -1)`, and `Sound.reg` reads it back as `explicitKeyLine`.
    Capstone chain (Rule 1): Group 7.2 `scan_content_gives_stream_v2` ← `scanNextToken_accum_step`
    ← `accum_step_flow` ← `accum_flow_open_depth0`, whose `PackAlt sc` faces over the block state at
    a `[`/`{` pay `PackAlt.ofRefused` from this lemma when the enclosing park's domain is empty. -/
lemma refused_of_markedCols_nil {s : ScannerState} (hs : Sound s) (hfl : s.flowLevel = 0)
    (hm : MarkedColsIn s []) : s.explicitKeyLine = none := by
  apply explicitKeyLine_none_of_noMarks hs hfl
  intro j l' hj
  obtain ⟨c, hc, -⟩ := hs.slots.2 j l' hj
  have := hm j l' c hj hc
  simp at this

/-- **The `?` park's own-mark fact, read as its contrapositive** (item 410): a markless
    projection at a block-context sound state is a DEAD register — no class-A `:` can fire
    there — so a face whose `markedCols` is `[]` refuses honestly (`ExplicitValueRefused`),
    it never declines. -/
lemma refused_of_markedCols_eq_nil {s : ScannerState} (hs : Sound s) (hfl : s.flowLevel = 0)
    (h : markedCols s = []) : s.explicitKeyLine = none :=
  refused_of_markedCols_nil hs hfl (MarkedColsIn.of_markedCols_nil h)

lemma scanBlockEntry_markedCols {s s' : ScannerState} {ns : List Nat}
    (hnf : s.inFlow = false) (hok : scanBlockEntry s = .ok s')
    (h : MarkedColsIn s ns) (hs : SlotsOk s) : MarkedColsIn s' ns :=
  (pushSequenceIndent_markedCols (s.col : Int) h hs.1).transport
    (scanBlockEntry_pendingKeys hnf hok)
    (L4YAML.Proofs.PreprocessIndentStable.scanBlockEntry_indents hnf hok)

/-- A block step that is not a `?` adds no mark: the domain transports unchanged. -/
lemma dispatchBlockIndicators_markedCols_of_ne {s s' : ScannerState} {c : Char} {ns : List Nat}
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (hne : c ≠ '?') (h : MarkedColsIn s ns) (hs : SlotsOk s) : MarkedColsIn s' ns := by
  by_cases hf : s.inFlow = true
  · exact h.transport (dispatchBlockIndicators_preserves_pendingKeys hf hok)
      (L4YAML.Proofs.FlowIndentStable.dispatchBlockIndicators_preserves_indents hf hok)
  · have hnf : s.inFlow = false := by simpa using hf
    unfold scanNextToken_dispatchBlockIndicators at hok
    simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
    repeat (any_goals (split at hok))
    any_goals contradiction
    all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
    any_goals contradiction
    all_goals (try subst_vars)
    all_goals first
      | exact scanBlockEntry_markedCols hnf (by assumption) h hs
      | (exfalso
         have hq := ‹(c == '?' && isKeyCandidate s && flowKeyPredecessorOk s
           && flowKeyFollowerOk s) = true›
         simp only [Bool.and_eq_true, beq_iff_eq] at hq
         exact hne hq.1.1.1)
      | exact scanValue_markedCols (by assumption) h hs

/-- **The block step lands in `(s.col).toNat :: ns`**: `-` and `:` add no mark, the `?` adds
    its own column. -/
lemma dispatchBlockIndicators_markedCols {s s' : ScannerState} {c : Char} {ns : List Nat}
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (h : MarkedColsIn s ns) (hs : SlotsOk s)
    (hbase : SentinelBase s) (hcol : s.inFlow = false → s.currentIndent ≤ (s.col : Int)) :
    MarkedColsIn s' ((s.col : Int).toNat :: ns) := by
  have hmono : ∀ t, MarkedColsIn t ns → MarkedColsIn t ((s.col : Int).toNat :: ns) :=
    fun _ ht => ht.mono (fun _ hx => List.mem_cons_of_mem _ hx)
  by_cases hf : s.inFlow = true
  · exact hmono _ (h.transport (dispatchBlockIndicators_preserves_pendingKeys hf hok)
      (L4YAML.Proofs.FlowIndentStable.dispatchBlockIndicators_preserves_indents hf hok))
  · have hnf : s.inFlow = false := by simpa using hf
    unfold scanNextToken_dispatchBlockIndicators at hok
    simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
    repeat (any_goals (split at hok))
    any_goals contradiction
    all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
    any_goals contradiction
    all_goals (try subst_vars)
    all_goals first
      | exact hmono _ (scanBlockEntry_markedCols hnf (by assumption) h hs)
      | exact scanKey_markedCols hnf (by assumption) hs hbase (hcol hnf) h
      | exact hmono _ (scanValue_markedCols (by assumption) h hs)

/-- A document marker unwinds to the sentinel; the witness follows the unwind and nothing after
    it touches a slot. -/
lemma SlotsWitness.of_doc_reset {input : String} {s s' : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) (hs : SlotsOk s)
    (hpk : s'.pendingKeys = (unwindIndents s (-1)).pendingKeys)
    (hind : s'.indents = (unwindIndents s (-1)).indents) : SlotsWitness input s' sp_start :=
  (unwindIndents_witness s (-1) h hs).transport hpk hind

lemma scanDocumentStart_witness {input : String} {s : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) (hs : SlotsOk s) :
    SlotsWitness input (scanDocumentStart s) sp_start := by
  refine h.of_doc_reset hs ?_ ?_
  · unfold scanDocumentStart; simp [advanceN_preserves_pendingKeys, emit_pendingKeys]
  · unfold scanDocumentStart
    simp [L4YAML.Proofs.IndentStackBase.advanceN_preserves_indents,
      L4YAML.Proofs.ScannerContracts.emit_indents]

lemma scanDocumentEnd_witness {input : String} {s s' : ScannerState} {sp_start : SurfPos}
    (hok : scanDocumentEnd s = .ok s') (h : SlotsWitness input s sp_start) (hs : SlotsOk s) :
    SlotsWitness input s' sp_start := by
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals refine h.of_doc_reset hs ?_ ?_
  all_goals (try simp [advanceN_preserves_pendingKeys, emit_pendingKeys])
  all_goals (try simp [L4YAML.Proofs.IndentStackBase.advanceN_preserves_indents,
      L4YAML.Proofs.ScannerContracts.emit_indents])

/-- The four flow brackets and the flow entry never touch a slot. -/
lemma scanFlowSequenceStart_witness {input : String} {s : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) : SlotsWitness input (scanFlowSequenceStart s) sp_start :=
  h.transport (scanFlowSequenceStart_preserves_pendingKeys s) (by
    unfold scanFlowSequenceStart; dsimp only []
    simp only [L4YAML.Proofs.EmitterScannability.advance_preserves_indents, ScannerState.emit])

lemma scanFlowMappingStart_witness {input : String} {s : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) : SlotsWitness input (scanFlowMappingStart s) sp_start :=
  h.transport (scanFlowMappingStart_preserves_pendingKeys s) (by
    unfold scanFlowMappingStart; dsimp only []
    simp only [L4YAML.Proofs.EmitterScannability.advance_preserves_indents, ScannerState.emit])

lemma scanFlowSequenceEnd_witness {input : String} {s : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) : SlotsWitness input (scanFlowSequenceEnd s) sp_start :=
  h.transport (scanFlowSequenceEnd_preserves_pendingKeys s) (by
    unfold scanFlowSequenceEnd; dsimp only []
    simp only [L4YAML.Proofs.EmitterScannability.advance_preserves_indents, ScannerState.emit])

lemma scanFlowMappingEnd_witness {input : String} {s : ScannerState} {sp_start : SurfPos}
    (h : SlotsWitness input s sp_start) : SlotsWitness input (scanFlowMappingEnd s) sp_start :=
  h.transport (scanFlowMappingEnd_preserves_pendingKeys s) (by
    unfold scanFlowMappingEnd; dsimp only []
    simp only [L4YAML.Proofs.EmitterScannability.advance_preserves_indents, ScannerState.emit])

lemma scanFlowEntry_witness {input : String} {s s' : ScannerState} {sp_start : SurfPos}
    (hok : scanFlowEntry s = .ok s') (h : SlotsWitness input s sp_start) :
    SlotsWitness input s' sp_start :=
  h.transport (scanFlowEntry_preserves_pendingKeys hok)
    (L4YAML.Proofs.FlowIndentStable.scanFlowEntry_preserves_indents hok)

/-- The content arm (scalars, props, aliases) never touches a slot. -/
lemma dispatchContent_witness {input : String} {s s' : ScannerState} {c : Char} {sp_start : SurfPos}
    (hok : scanNextToken_dispatchContent s c = .ok s') (h : SlotsWitness input s sp_start) :
    SlotsWitness input s' sp_start :=
  h.transport (dispatchContent_pendingKeys hok)
    (L4YAML.Proofs.IndentStackBase.dispatchContent_preserves_indents hok)


/-! ### Batch 3: the preprocess, the dispatchers, the step -/

lemma SlotsOk.of_eq' {s s' : ScannerState} (hs : SlotsOk s)
    (hpk : s'.pendingKeys = s.pendingKeys) (hind : s'.indents = s.indents) : SlotsOk s' := by
  refine ⟨by rw [hpk, hind]; exact hs.1, ?_⟩
  intro i l hi
  rw [hpk] at hi
  rw [ScannerState.indentColumns, hind]; exact hs.2 i l hi

/-- The preprocess: skip to content, then (an unwind, the hook and) the simple-key save —
    none of which re-marks a slot. -/
lemma preprocess_witness {input : String} {s s' : ScannerState} {c : Char} {sp_start : SurfPos}
    (hok : scanNextToken_preprocess s = .ok (some (s', c))) (h : SlotsWitness input s sp_start)
    (hs : SlotsOk s) : SlotsWitness input s' sp_start := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  split at hok
  · contradiction
  · rename_i s_skip h_skip
    have hind_skip := L4YAML.Proofs.PreprocessIndentStable.skipToContent_preserves_indents s s_skip h_skip
    have hpk_skip := skipToContent_preserves_pendingKeys s s_skip h_skip
    have hW : SlotsWitness input s_skip sp_start := h.transport hpk_skip hind_skip
    have hS : SlotsOk s_skip := SlotsOk.of_eq' hs hpk_skip hind_skip
    have hsave : ∀ t : ScannerState, SlotsWitness input t sp_start →
        SlotsWitness input (saveSimpleKey t) sp_start := fun t ht =>
      ht.transport (saveSimpleKey_preserves_pendingKeys t)
        (L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_preserves_indents t)
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            exact closeStaleExplicitKey_witness (hsave _ (unwindIndents_witness _ _ hW hS))
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            exact closeStaleExplicitKey_witness (hsave _ hW)

/-- Item 354: the content dispatch moves neither field the domain reads. -/
lemma dispatchContent_markedCols {s s' : ScannerState} {c : Char} {ns : List Nat}
    (hok : scanNextToken_dispatchContent s c = .ok s') (h : MarkedColsIn s ns) :
    MarkedColsIn s' ns :=
  h.transport (dispatchContent_pendingKeys hok)
    (L4YAML.Proofs.IndentStackBase.dispatchContent_preserves_indents hok)

set_option maxHeartbeats 2000000 in
/-- Item 354: the preprocess only unwinds, closes and saves — no slot is re-marked. -/
lemma preprocess_markedCols {s s' : ScannerState} {c : Char} {ns : List Nat}
    (hok : scanNextToken_preprocess s = .ok (some (s', c))) (h : MarkedColsIn s ns) :
    MarkedColsIn s' ns := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  split at hok
  · contradiction
  · rename_i s_skip h_skip
    have hind_skip := L4YAML.Proofs.PreprocessIndentStable.skipToContent_preserves_indents s s_skip h_skip
    have hpk_skip := skipToContent_preserves_pendingKeys s s_skip h_skip
    have hW : MarkedColsIn s_skip ns := h.transport hpk_skip hind_skip
    have hsave : ∀ t : ScannerState, MarkedColsIn t ns → MarkedColsIn (saveSimpleKey t) ns :=
      fun t ht => ht.transport (saveSimpleKey_preserves_pendingKeys t)
        (L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_preserves_indents t)
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            exact MarkedColsIn.closeStaleExplicitKey (hsave _ (MarkedColsIn.unwind _ _ hW))
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            exact MarkedColsIn.closeStaleExplicitKey (hsave _ hW)

set_option maxHeartbeats 2000000 in
lemma dispatchStructural_witness {input : String} {s s' : ScannerState} {c : Char} {sp_start : SurfPos}
    (hok : scanNextToken_dispatchStructural s c = .ok (some s')) (h : SlotsWitness input s sp_start)
    (hs : SlotsOk s) : SlotsWitness input s' sp_start := by
  unfold scanNextToken_dispatchStructural at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  repeat (any_goals (split at hok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | with_reducible exact scanDocumentStart_witness h hs
    | with_reducible exact scanDocumentEnd_witness (by assumption) h hs
    | with_reducible exact h.transport (scanDirective_preserves_pendingKeys ‹_›) (L4YAML.Proofs.IndentStackBase.scanDirective_preserves_indents ‹_›)

set_option maxHeartbeats 2000000 in
lemma dispatchFlowIndicators_witness {input : String} {s s' : ScannerState} {c : Char}
    {sp_start : SurfPos} (hok : scanNextToken_dispatchFlowIndicators s c = .ok (some s'))
    (h : SlotsWitness input s sp_start) : SlotsWitness input s' sp_start := by
  unfold scanNextToken_dispatchFlowIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (try (simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok))
  all_goals first
    | with_reducible exact scanFlowSequenceStart_witness h
    | with_reducible exact scanFlowMappingStart_witness h
    | with_reducible exact scanFlowSequenceEnd_witness h
    | with_reducible exact scanFlowMappingEnd_witness h
    | with_reducible exact scanFlowEntry_witness (by assumption) h
    | simp_all

/-- The block indicators: the `?` arm is the seed and takes the route; the `-` and `:` arms
    are the batch-2 writers. -/
lemma dispatchBlockIndicators_witness {s s' : ScannerState} {c : Char} {sp sp_start : SurfPos}
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (hcorr : ScannerSurfCorr s sp) (h : SlotsWitness s.input s sp_start) (hs : SlotsOk s)
    (hbase : SentinelBase s) (hcol : s.inFlow = false → s.currentIndent ≤ (s.col : Int))
    (hpeek : s.peek? = some c)
    (h_land : c = '?' → s.inFlow = false → QuestionLanding sp_start s.col sp) :
    SlotsWitness s.input s' sp_start := by
  by_cases hf : s.inFlow = true
  · exact h.transport (dispatchBlockIndicators_preserves_pendingKeys hf hok)
      (L4YAML.Proofs.FlowIndentStable.dispatchBlockIndicators_preserves_indents hf hok)
  · have hnf : s.inFlow = false := by simpa using hf
    unfold scanNextToken_dispatchBlockIndicators at hok
    simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
    repeat (any_goals (split at hok))
    any_goals contradiction
    all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
    any_goals contradiction
    all_goals (try subst_vars)
    all_goals first
      | exact scanBlockEntry_witness hnf (by assumption) h hs
      | (have hc : c = '?' := by
           have hq := ‹(c == '?' && isKeyCandidate s && flowKeyPredecessorOk s
             && flowKeyFollowerOk s) = true›
           simp only [Bool.and_eq_true, beq_iff_eq] at hq
           exact hq.1.1.1
         subst hc
         exact scanKey_witness hcorr hnf (by assumption) hs hbase (hcol hnf) hpeek
           (h_land rfl hnf) h)
      | exact scanValue_witness (by assumption) h hs

/-! ## §4  The step -/

/-- The landing a `?` step owes: for the preprocessed state the `?` is read on (its
    correspondence `sp_pos`), where the stream reached the column-0 line it is indented
    from.  `question_open_map` holds it as `h_stream_land`/`hcol_land`/`h_ind`. -/
def StepLanding (s : ScannerState) (sp_start : SurfPos) : Prop :=
  ∀ (s_prep : ScannerState) (c : Char) (sp_pos : SurfPos),
    scanNextToken_preprocess s = .ok (some (s_prep, c)) → c = '?' → s_prep.inFlow = false →
    ScannerSurfCorr s_prep sp_pos → QuestionLanding sp_start s_prep.col sp_pos

set_option maxHeartbeats 1000000 in
/-- **The step keeps every marked slot's `?` named** — `scanNextToken_sound`'s twin for the
    witness: the `?` arm takes the landing, every other arm is a writer lemma of §3. -/
lemma scanNextToken_witness {s s' : ScannerState} {sp sp_start : SurfPos}
    (hok : scanNextToken s = .ok (some s')) (hcorr : ScannerSurfCorr s sp)
    (h : Sound s) (hm : L4YAML.Proofs.IndentStackMono.Mono s) (hbase : SentinelBase s)
    (hfloor : PreprocessFloor s) (hw : SlotsWitness s.input s sp_start)
    (h_land : StepLanding s sp_start) : SlotsWitness s.input s' sp_start := by
  unfold scanNextToken at hok
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at hok
  split at hok
  · cases hok
  · split at hok
    · simp at hok
    · rename_i sp_s c h_pre
      have h_in : sp_s.input = s.input := L4YAML.Proofs.TabIndentBridge.preprocess_input h_pre
      have h_ps : Sound sp_s := preprocess_sound h_pre h hm
      have h_pb : SentinelBase sp_s := L4YAML.Proofs.IndentStackBase.preprocess_base h_pre hbase
      have h_pc : sp_s.inFlow = false → sp_s.currentIndent ≤ (sp_s.col : Int) := hfloor sp_s c h_pre
      have h_pw : SlotsWitness s.input sp_s sp_start := preprocess_witness h_pre hw h.slots
      obtain ⟨sp_pos, h_pcorr⟩ :=
        L4YAML.Proofs.ScanStrictCoupling.scanNextToken_preprocess_corr s sp hcorr sp_s c h_pre
      have h_pk : sp_s.peek? = some c :=
        L4YAML.Proofs.ScannerCorrectness.preprocess_peek_eq s sp_s c h_pre
      have h_pl : c = '?' → sp_s.inFlow = false → QuestionLanding sp_start sp_s.col sp_pos :=
        fun hc hnf => h_land sp_s c sp_pos h_pre hc hnf h_pcorr
      rw [← h_in] at h_pw ⊢
      split at hok
      · cases hok
      split at hok
      · cases hok
      split at hok
      · cases hok
      · split at hok
        · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
          exact dispatchStructural_witness ‹_› h_pw h_ps.slots
        · split at hok
          · cases hok
          split at hok
          · cases hok
          · rcases h_ad : sp_s.allowDirectives with _ | _
            <;> simp only [h_ad, Bool.false_eq_true, ↓reduceIte] at hok
            · generalize h_fi : scanNextToken_dispatchFlowIndicators sp_s c = fi at hok
              cases fi with
              | error => cases hok
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                  exact dispatchFlowIndicators_witness h_fi h_pw
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp_s c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact dispatchBlockIndicators_witness h_bi h_pcorr h_pw h_ps.slots h_pb h_pc
                        h_pk h_pl
                    | none =>
                      generalize h_av : scanNextToken_checkAdjacentValue sp_s c = av at hok
                      cases av with
                      | error => cases hok
                      | ok _ =>
                      generalize h_dc : scanNextToken_dispatchContent sp_s c = dc at hok
                      cases dc with
                      | error => cases hok
                      | ok s_dc =>
                        simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                        exact dispatchContent_witness h_dc h_pw
            · generalize h_sp2 :
                (({ sp_s with allowDirectives := false, documentEverStarted := true }
                  : ScannerState)) = sp2 at hok
              have h_ps2 : Sound sp2 := by
                rw [← h_sp2]; exact Sound.of_eq h_ps rfl rfl rfl rfl rfl rfl
              have h_pb2 : SentinelBase sp2 := by rw [← h_sp2]; exact h_pb
              have h_pc2 : sp2.inFlow = false → sp2.currentIndent ≤ (sp2.col : Int) := by
                rw [← h_sp2]; exact h_pc
              have h_pw2 : SlotsWitness sp_s.input sp2 sp_start := by
                rw [← h_sp2]; exact h_pw.transport rfl rfl
              have h_in2 : sp2.input = sp_s.input := by rw [← h_sp2]
              have h_pcorr2 : ScannerSurfCorr sp2 sp_pos := by
                rw [← h_sp2]
                exact ⟨h_pcorr.chars_from, h_pcorr.col_eq, h_pcorr.end_eq, h_pcorr.input_prefix,
                  h_pcorr.indent_cols_nonneg⟩
              have h_pk2 : sp2.peek? = some c := by rw [← h_sp2]; exact h_pk
              have h_pl2 : c = '?' → sp2.inFlow = false → QuestionLanding sp_start sp2.col sp_pos := by
                rw [← h_sp2]; exact h_pl
              rw [← h_in2] at h_pw2 ⊢
              generalize h_fi : scanNextToken_dispatchFlowIndicators sp2 c = fi at hok
              cases fi with
              | error => cases hok
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                  exact dispatchFlowIndicators_witness h_fi h_pw2
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp2 c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact dispatchBlockIndicators_witness h_bi h_pcorr2 h_pw2 h_ps2.slots h_pb2
                        h_pc2 h_pk2 h_pl2
                    | none =>
                      generalize h_av : scanNextToken_checkAdjacentValue sp2 c = av at hok
                      cases av with
                      | error => cases hok
                      | ok _ =>
                      generalize h_dc : scanNextToken_dispatchContent sp2 c = dc at hok
                      cases dc with
                      | error => cases hok
                      | ok s_dc =>
                        simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                        exact dispatchContent_witness h_dc h_pw2

end L4YAML.Proofs.RegisterWitness

end Blanket
