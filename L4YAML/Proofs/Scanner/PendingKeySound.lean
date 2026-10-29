/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import L4YAML.Proofs.Scanner.PendingKeysStable
public import L4YAML.Proofs.Scanner.IndentStackMono
public import L4YAML.Proofs.Scanner.ExplicitKeyCoupling
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey
public import L4YAML.Proofs.Scanner.ScannerEkStackPreservation
public import L4YAML.Proofs.Scanner.IndentStackCover
@[expose] public section Blanket

/-!
# The explicit-key register IS the innermost pending key (DOCS item 338)

Item 335 gave every indentation level one `pendingKeys` slot and made the
scanner re-read the register (`explicitKeyLine`, `explicitKeyCol`) off the
innermost marked level whenever a level closes.  Item 337's hook closes a level
on a dedenting `-`.  What those two items bought is a TOKEN-LEVEL invariant,
stated and carried here:

* `SlotsOk` — `pendingKeys` is in lockstep with `indents`, and a marked slot sits
  on a level of column `≥ 0` (never the sentinel);
* `RegOk`   — outside flow, the register pair equals `PendingKeys.innermost`;
* `BaseOk`  — inside flow, the pair saved at the OUTERMOST flow open (the bottom
  of `explicitKeyStack`) equals the innermost pending key, which no flow token
  moves (the block writers are `!inFlow`-guarded) — lane (d) of item 334;
* `StackOk` — `explicitKeyStack` has one saved pair per open flow level.

It is a property of the state BETWEEN tokens, not of every intermediate state:
`unwindIndents` pops marked levels before the stale-key hook re-reads the
register (which is why it is not a `ScannerSurfCorr` field — item 338 priced
and refuted that shape), and the one hook exemption that survives a pop is the
`?` the next `scanKey` overwrites.  So `preprocess_sound` concludes `RegOk` only
for `c ≠ '?'`, and `scanKey_sound` needs no `RegOk` premise.

§1 the `PendingKeys` array lemmas (`innermost` read structurally).  §2 the
predicate and its transport.  §3 the writers.  §4 the preprocess and the four
dispatchers.  §5 the step and the seed.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.PendingKeySound

open L4YAML.Scanner
open L4YAML.Proofs.PendingKeysStable
open L4YAML.Proofs.CloseStaleExplicitKey
open L4YAML.Proofs.IndentStackBase (SentinelBase)
open L4YAML.Proofs.IndentStackMono (Mono)

/-! ## §1  `PendingKeys.innermost`, read structurally -/

/-- `innermost` read top-down, structurally. -/
def go (cols : Array Int) (pks : Array (Option Nat)) : Nat → Option Nat × Int
  | 0 => (none, -1)
  | i + 1 =>
    match pks[i]?.getD none with
    | some l => (some l, cols[i]?.getD (-1))
    | none => go cols pks i

lemma findSomeRev_range_eq (cols : Array Int) (pks : Array (Option Nat)) (n : Nat) :
    ((Array.range n).findSomeRev? (fun i =>
        (pks[i]?.getD none).map fun l => (l, cols[i]?.getD (-1)))) =
      match go cols pks n with
      | (some l, c) => some (l, c)
      | (none, _) => none := by
  induction n with
  | zero =>
    first
      | rfl
      | (rw [show Array.range 0 = #[] from Array.eq_empty_of_size_eq_zero (by simp)]; rfl)
      | simp [go]
  | succ n ih =>
    rw [Array.range_succ, Array.append_singleton, Array.findSomeRev?_push]
    simp only [go]
    cases h : pks[n]?.getD none with
    | none => simp; split <;> simp_all
    | some l => simp

lemma go_none_snd (cols : Array Int) (pks : Array (Option Nat)) (n : Nat)
    (h : (go cols pks n).1 = none) : (go cols pks n).2 = -1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [go] at h ⊢
    split at h
    · simp at h
    · exact ih h

lemma innermost_eq_go (cols : Array Int) (pks : Array (Option Nat)) :
    PendingKeys.innermost cols pks = go cols pks pks.size := by
  unfold PendingKeys.innermost
  rw [findSomeRev_range_eq]
  cases h : go cols pks pks.size with
  | mk l c =>
    cases l with
    | some l => simp
    | none =>
      have := go_none_snd cols pks pks.size (by rw [h])
      rw [h] at this; simp at this; simp [this]

/-- `go` only reads slots below `n`; pushing a slot above them changes nothing. -/
lemma go_push (cols : Array Int) (pks : Array (Option Nat)) (c : Int) (x : Option Nat)
    (hsz : cols.size = pks.size) (n : Nat) (hn : n ≤ pks.size) :
    go (cols.push c) (pks.push x) n = go cols pks n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [go]
    rw [Array.getElem?_push_lt (by omega), Array.getElem?_push_lt (by omega),
        Array.getElem?_eq_getElem (by omega : n < pks.size),
        Array.getElem?_eq_getElem (by omega : n < cols.size), ih (by omega)]

lemma innermost_push_none (cols : Array Int) (pks : Array (Option Nat)) (c : Int)
    (hsz : cols.size = pks.size) :
    PendingKeys.innermost (cols.push c) (pks.push none) = PendingKeys.innermost cols pks := by
  rw [innermost_eq_go, innermost_eq_go, Array.size_push]
  simp only [go, Array.getElem?_push_size, Option.getD_some]
  exact go_push cols pks c none hsz pks.size (Nat.le_refl _)

lemma go_pop (cols : Array Int) (pks : Array (Option Nat)) (n : Nat) (hn : n < pks.size)
    (hc : n < cols.size) :
    go cols.pop pks.pop n = go cols pks n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [go]
    rw [Array.getElem?_pop, Array.getElem?_pop]
    simp only [show n < pks.size - 1 from by omega, show n < cols.size - 1 from by omega, ↓reduceIte]
    rw [ih (by omega) (by omega)]

/-- Popping an UNMARKED top slot keeps the innermost pending key. -/
lemma innermost_pop_of_top_none (cols : Array Int) (pks : Array (Option Nat))
    (hsz : cols.size = pks.size) (hpos : 0 < pks.size)
    (htop : pks[pks.size - 1]? = some none) :
    PendingKeys.innermost cols.pop pks.pop = PendingKeys.innermost cols pks := by
  rw [innermost_eq_go, innermost_eq_go, Array.size_pop]
  obtain ⟨k, hk⟩ : ∃ k, pks.size = k + 1 := ⟨pks.size - 1, by omega⟩
  rw [hk]; simp only [Nat.add_sub_cancel, go]
  rw [hk] at htop; simp only [Nat.add_sub_cancel] at htop
  rw [htop]; simp only [Option.getD_some]
  exact go_pop cols pks k (by omega) (by omega)

/-- Marking the top slot makes it the innermost pending key. -/
lemma innermost_set_top (cols : Array Int) (pks : Array (Option Nat)) (l : Nat)
    (_hsz : cols.size = pks.size) (hpos : 0 < pks.size) :
    PendingKeys.innermost cols (pks.set! (pks.size - 1) (some l)) =
      (some l, cols[pks.size - 1]?.getD (-1)) := by
  rw [innermost_eq_go, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
  obtain ⟨k, hk⟩ : ∃ k, pks.size = k + 1 := ⟨pks.size - 1, by omega⟩
  rw [hk]; simp only [Nat.add_sub_cancel, go]
  rw [Array.getElem?_setIfInBounds_self]
  simp only [show k < pks.size from by omega, ↓reduceIte, Option.getD_some]

/-- A marked slot's witness: the innermost pair names a slot of `pks`. -/
lemma go_some_mem (cols : Array Int) (pks : Array (Option Nat)) (n : Nat) (l : Nat) (c : Int)
    (h : go cols pks n = (some l, c)) :
    ∃ i, i < n ∧ pks[i]? = some (some l) ∧ cols[i]?.getD (-1) = c := by
  induction n with
  | zero => simp [go] at h
  | succ n ih =>
    simp only [go] at h
    cases hp : pks[n]?.getD none with
    | some l' =>
      rw [hp] at h; simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨n, Nat.lt_succ_self _, ?_, rfl⟩
      cases hq : pks[n]? with
      | none => simp [hq] at hp
      | some v => simp [hq] at hp; simp [hp]
    | none =>
      rw [hp] at h
      obtain ⟨i, hi, h1, h2⟩ := ih h
      exact ⟨i, Nat.lt_succ_of_lt hi, h1, h2⟩

lemma innermost_some_mem (cols : Array Int) (pks : Array (Option Nat)) (l : Nat) (c : Int)
    (h : PendingKeys.innermost cols pks = (some l, c)) :
    ∃ i, i < pks.size ∧ pks[i]? = some (some l) ∧ cols[i]?.getD (-1) = c := by
  rw [innermost_eq_go] at h; exact go_some_mem cols pks _ l c h

/-- `closeAt` only erases slots. -/
lemma closeAt_getElem? (cols : Array Int) (pks : Array (Option Nat)) (col : Int) (i : Nat) :
    (PendingKeys.closeAt cols pks col)[i]? =
      if i < pks.size then some (if cols[i]? == some col then none else pks[i]?.getD none)
      else none := by
  unfold PendingKeys.closeAt
  rw [Array.getElem?_map, Array.getElem?_range]
  split <;> rfl

lemma closeAt_size (cols : Array Int) (pks : Array (Option Nat)) (col : Int) :
    (PendingKeys.closeAt cols pks col).size = pks.size := by
  simp [PendingKeys.closeAt]

lemma closeAt_marked (cols : Array Int) (pks : Array (Option Nat)) (col : Int) (i l : Nat)
    (h : (PendingKeys.closeAt cols pks col)[i]? = some (some l)) :
    pks[i]? = some (some l) ∧ cols[i]? ≠ some col := by
  rw [closeAt_getElem?] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · cases h
    · rename_i hne
      refine ⟨?_, fun hc => hne (by simp [hc])⟩
      cases hq : pks[i]? with
      | none => simp [hq] at h
      | some v => simp [hq] at h; simp [h]
  · cases h


/-! ## §2  The predicate -/

/-- `pendingKeys` is in lockstep with `indents`, and every marked slot sits on a
    level of column `≥ 0`. -/
def SlotsOk (s : ScannerState) : Prop :=
  s.pendingKeys.size = s.indents.size ∧
  ∀ (i l : Nat), s.pendingKeys[i]? = some (some l) →
    ∃ c, s.indentColumns[i]? = some c ∧ 0 ≤ c

/-- Outside flow the register IS the innermost pending key. -/
def RegOk (s : ScannerState) : Prop :=
  s.flowLevel = 0 → (s.explicitKeyLine, s.explicitKeyCol) = s.innermostPendingKey

/-- Inside flow the pair saved at the outermost open is the innermost pending key. -/
def BaseOk (s : ScannerState) : Prop :=
  0 < s.flowLevel → s.explicitKeyStack[0]? = some s.innermostPendingKey

/-- One saved pair per open flow level. -/
def StackOk (s : ScannerState) : Prop := s.explicitKeyStack.size = s.flowLevel

structure Sound (s : ScannerState) : Prop where
  slots : SlotsOk s
  reg : RegOk s
  base : BaseOk s
  stack : StackOk s

lemma indentColumns_size (s : ScannerState) : s.indentColumns.size = s.indents.size := by
  simp [ScannerState.indentColumns]

lemma innermostPendingKey_eq (s : ScannerState) :
    s.innermostPendingKey = PendingKeys.innermost s.indentColumns s.pendingKeys := rfl

/-- Transport along a step that moves none of the six fields the predicate reads. -/
lemma Sound.of_eq {s s' : ScannerState} (h : Sound s)
    (hpk : s'.pendingKeys = s.pendingKeys) (hind : s'.indents = s.indents)
    (hfl : s'.flowLevel = s.flowLevel)
    (hekl : s'.explicitKeyLine = s.explicitKeyLine) (hekc : s'.explicitKeyCol = s.explicitKeyCol)
    (hst : s'.explicitKeyStack = s.explicitKeyStack) : Sound s' := by
  have hcols : s'.indentColumns = s.indentColumns := by
    simp [ScannerState.indentColumns, hind]
  have hinn : s'.innermostPendingKey = s.innermostPendingKey := by
    simp [innermostPendingKey_eq, hcols, hpk]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpk, hind]; exact h.slots.1
  · intro i l hi; rw [hcols]; exact h.slots.2 i l (hpk ▸ hi)
  · intro h0; rw [hekl, hekc, hinn]; exact h.reg (hfl ▸ h0)
  · intro h0; rw [hst, hinn]; exact h.base (hfl ▸ h0)
  · show s'.explicitKeyStack.size = s'.flowLevel
    rw [hst, hfl]; exact h.stack

/-! ## §3  The writers -/

lemma indentColumns_push (s : ScannerState) (e : IndentEntry) :
    ({ s with indents := s.indents.push e } : ScannerState).indentColumns =
      s.indentColumns.push e.column := by
  simp [ScannerState.indentColumns]

lemma SlotsOk.push_none {s s' : ScannerState} (h : SlotsOk s) (e : IndentEntry)
    (hind : s'.indents = s.indents.push e) (hpk : s'.pendingKeys = s.pendingKeys.push none) :
    SlotsOk s' := by
  have hsz := h.1
  have hcols : s'.indentColumns = s.indentColumns.push e.column := by
    simp [ScannerState.indentColumns, hind]
  refine ⟨by simp [hind, hpk, hsz], ?_⟩
  intro i l hi
  rw [hpk] at hi
  rw [hcols]
  by_cases hlt : i < s.pendingKeys.size
  · rw [Array.getElem?_push_lt hlt] at hi
    obtain ⟨c, hc, hc0⟩ := h.2 i l (by rw [Array.getElem?_eq_getElem hlt]; exact hi)
    refine ⟨c, ?_, hc0⟩
    rw [Array.getElem?_push_lt (by rw [indentColumns_size]; omega)]
    rw [Array.getElem?_eq_getElem (by rw [indentColumns_size]; omega)] at hc
    exact hc
  · by_cases heq : i = s.pendingKeys.size
    · subst heq; rw [Array.getElem?_push_size] at hi; cases hi
    · rw [Array.getElem?_eq_none (by simp [Array.size_push]; omega)] at hi; cases hi

lemma pushMappingIndent_slots (s : ScannerState) (col : Int) (h : SlotsOk s) :
    SlotsOk (pushMappingIndent s col) := by
  unfold pushMappingIndent
  split
  · exact h.push_none { column := col, isSequence := false } (by simp [ScannerState.emit])
      (by simp [ScannerState.emit])
  · exact h

/-- A level pushed with an empty slot: nothing the predicate reads moves except
    the lockstep sizes. -/
lemma Sound.push_none {s s' : ScannerState} (h : Sound s) (e : IndentEntry)
    (hind : s'.indents = s.indents.push e) (hpk : s'.pendingKeys = s.pendingKeys.push none)
    (hfl : s'.flowLevel = s.flowLevel)
    (hekl : s'.explicitKeyLine = s.explicitKeyLine) (hekc : s'.explicitKeyCol = s.explicitKeyCol)
    (hst : s'.explicitKeyStack = s.explicitKeyStack) : Sound s' := by
  have hsz := h.slots.1
  have hcols : s'.indentColumns = s.indentColumns.push e.column := by
    simp [ScannerState.indentColumns, hind]
  have hinn : s'.innermostPendingKey = s.innermostPendingKey := by
    rw [innermostPendingKey_eq, innermostPendingKey_eq, hcols, hpk]
    exact innermost_push_none _ _ _ (by rw [indentColumns_size]; exact hsz.symm)
  refine ⟨⟨by simp [hind, hpk, hsz], ?_⟩, ?_, ?_, ?_⟩
  · intro i l hi
    rw [hpk] at hi
    rw [hcols]
    by_cases hlt : i < s.pendingKeys.size
    · rw [Array.getElem?_push_lt hlt] at hi
      obtain ⟨c, hc, hc0⟩ := h.slots.2 i l (by rw [Array.getElem?_eq_getElem hlt]; exact hi)
      refine ⟨c, ?_, hc0⟩
      rw [Array.getElem?_push_lt (by rw [indentColumns_size]; omega)]
      rw [Array.getElem?_eq_getElem (by rw [indentColumns_size]; omega)] at hc
      exact hc
    · by_cases heq : i = s.pendingKeys.size
      · subst heq; rw [Array.getElem?_push_size] at hi; cases hi
      · rw [Array.getElem?_eq_none (by simp [Array.size_push]; omega)] at hi; cases hi
  · intro h0; rw [hekl, hekc, hinn]; exact h.reg (hfl ▸ h0)
  · intro h0; rw [hst, hinn]; exact h.base (hfl ▸ h0)
  · show s'.explicitKeyStack.size = s'.flowLevel
    rw [hst, hfl]; exact h.stack

lemma pushSequenceIndent_sound (s : ScannerState) (col : Int) (h : Sound s) :
    Sound (pushSequenceIndent s col) := by
  unfold pushSequenceIndent
  split
  · exact h.push_none _ rfl rfl rfl rfl rfl rfl
  · exact h

lemma pushMappingIndent_sound (s : ScannerState) (col : Int) (h : Sound s) :
    Sound (pushMappingIndent s col) := by
  unfold pushMappingIndent
  split
  · exact h.push_none _ rfl rfl rfl rfl rfl rfl
  · exact h

/-- `closeStale` only erases slots. -/
lemma closeStale_getElem? (cols : Array Int) (pks : Array (Option Nat)) (col : Int) (c : Char)
    (next : Option Char) (i : Nat) :
    (PendingKeys.closeStale cols pks col c next)[i]? =
      if i < pks.size then
        some (match cols[i]? with
          | some m => if PendingKeys.staleGate col m c next then none else pks[i]?.getD none
          | none => pks[i]?.getD none)
      else none := by
  unfold PendingKeys.closeStale
  rw [Array.getElem?_map, Array.getElem?_range]
  split <;> rfl

lemma closeStale_size (cols : Array Int) (pks : Array (Option Nat)) (col : Int) (c : Char)
    (next : Option Char) : (PendingKeys.closeStale cols pks col c next).size = pks.size := by
  simp [PendingKeys.closeStale]

/-- A slot still marked after `closeStale` was marked before. -/
lemma closeStale_marked (cols : Array Int) (pks : Array (Option Nat)) (col : Int) (c : Char)
    (next : Option Char) (i l : Nat)
    (h : (PendingKeys.closeStale cols pks col c next)[i]? = some (some l)) :
    pks[i]? = some (some l) := by
  rw [closeStale_getElem?] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · split at h
      · cases h
      · cases hq : pks[i]? with
        | none => simp [hq] at h
        | some v => simp [hq] at h; simp [h]
    · cases hq : pks[i]? with
      | none => simp [hq] at h
      | some v => simp [hq] at h; simp [h]
  · cases h

/-- `closeAt` only erases slots, so `SlotsOk` survives it. -/
lemma clearPendingKeyAt_slots {s : ScannerState} (h : SlotsOk s) (col : Int) :
    SlotsOk (s.clearPendingKeyAt col) := by
  refine ⟨by simp [ScannerState.clearPendingKeyAt, closeAt_size, h.1], ?_⟩
  intro i l hi
  simp only [ScannerState.clearPendingKeyAt] at hi
  exact h.2 i l (closeAt_marked _ _ _ _ _ hi).1

/-- A content character (no `-`/`:` indicator under the cursor) at or left of a level closes it. -/
lemma staleGate_true_of_noInd {col m : Int} {c : Char} {next : Option Char} (h0 : col ≤ m)
    (hind : PendingKeys.indicatorAt c next = false) :
    PendingKeys.staleGate col m c next = true := by
  simp [PendingKeys.staleGate, hind, h0]

/-- When the gate does not fire, the cursor is at or right of the level's column. -/
lemma staleGate_false_le {col m : Int} {c : Char} {next : Option Char}
    (h : PendingKeys.staleGate col m c next = false) : m ≤ col := by
  by_cases hle : m ≤ col
  · exact hle
  · exfalso
    have hlt : col < m := by omega
    have : PendingKeys.staleGate col m c next = true := by
      simp [PendingKeys.staleGate, Int.le_of_lt hlt, hlt, (show col ≠ m by omega)]
    rw [this] at h; cases h

/-- `closeStale` only erases slots, so `SlotsOk` survives it. -/
lemma closeStaleAt_slots {s : ScannerState} (h : SlotsOk s) (c : Char) :
    SlotsOk (s.closeStaleAt c) := by
  refine ⟨by simp [ScannerState.closeStaleAt, closeStale_size, h.1], ?_⟩
  intro i l hi
  simp only [ScannerState.closeStaleAt] at hi
  exact h.2 i l (closeStale_marked _ _ _ _ _ _ _ hi)

/-- Re-reading the register off the stack restores `RegOk` by construction, and
    touches nothing else. -/
lemma readPendingKey_sound {s : ScannerState} (hs : SlotsOk s) (hb : BaseOk s) (hst : StackOk s) :
    Sound s.readPendingKey :=
  ⟨hs, fun _ => rfl, hb, hst⟩

/-- The hook is the identity in flow, and in block context `BaseOk` is vacuous,
    so the re-read restores `RegOk` and costs nothing else. -/
lemma closeStaleExplicitKey_sound {s : ScannerState} (h : Sound s) :
    Sound (closeStaleExplicitKey s) := by
  by_cases hf : s.inFlow = true
  · rw [closeStaleExplicitKey_of_inFlow s hf]; exact h
  · have h0 : s.flowLevel = 0 := by
      simp [ScannerState.inFlow] at hf; omega
    rcases closeStaleExplicitKey_cases s with heq | ⟨_, _, heq⟩ <;> rw [heq]
    · exact h
    · exact readPendingKey_sound (closeStaleAt_slots h.slots _)
        (fun hpos => absurd hpos (by simp [ScannerState.closeStaleAt, h0])) h.stack

lemma indentColumns_getElem? (s : ScannerState) (i : Nat) :
    s.indentColumns[i]? = s.indents[i]?.map (·.column) := by
  simp [ScannerState.indentColumns]

/-- One pop of the loop: both arrays lose their top, nothing else the predicate
    reads moves. -/
lemma unwindPop_fields (s : ScannerState) :
    let s' : ScannerState :=
      { (s.emit .blockEnd) with indents := (s.emit .blockEnd).indents.pop,
                                pendingKeys := (s.emit .blockEnd).pendingKeys.pop }
    s'.indents = s.indents.pop ∧ s'.pendingKeys = s.pendingKeys.pop ∧
    s'.flowLevel = s.flowLevel ∧ s'.explicitKeyLine = s.explicitKeyLine ∧
    s'.explicitKeyCol = s.explicitKeyCol ∧ s'.explicitKeyStack = s.explicitKeyStack := by
  simp [ScannerState.emit, ScannerState.emitAt]

lemma SlotsOk.pop {s s' : ScannerState} (h : SlotsOk s)
    (hind : s'.indents = s.indents.pop) (hpk : s'.pendingKeys = s.pendingKeys.pop) :
    SlotsOk s' := by
  refine ⟨by simp [hind, hpk, Array.size_pop, h.1], ?_⟩
  intro i l hi
  rw [hpk, Array.getElem?_pop] at hi
  split at hi
  · obtain ⟨c, hc, hc0⟩ := h.2 i l hi
    refine ⟨c, ?_, hc0⟩
    rw [indentColumns_getElem?, hind, Array.getElem?_pop]
    rw [indentColumns_getElem?] at hc
    have hsz := h.1
    rw [if_pos (by omega)]; exact hc
  · cases hi

lemma unwindIndentsLoop_slots (s : ScannerState) (col : Int) (fuel : Nat) (h : SlotsOk s) :
    SlotsOk (unwindIndentsLoop s col fuel) := by
  induction fuel generalizing s with
  | zero => simpa [unwindIndentsLoop] using h
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · obtain ⟨h1, h2, -⟩ := unwindPop_fields s
      exact ih _ (h.pop h1 h2)
    · exact h

/-- The top slot is empty when the top column exceeds every marked column. -/
lemma top_slot_none {s : ScannerState} (hs : SlotsOk s) (col : Int)
    (hmarked : ∀ (i l : Nat), s.pendingKeys[i]? = some (some l) →
      s.indentColumns[i]?.getD (-1) ≤ col)
    (hgt : s.currentIndent > col) (hpos : 0 < s.indents.size) :
    s.pendingKeys[s.pendingKeys.size - 1]? = some none := by
  have hsz := hs.1
  have hlt : s.pendingKeys.size - 1 < s.pendingKeys.size := by omega
  rw [Array.getElem?_eq_getElem hlt]
  cases hv : s.pendingKeys[s.pendingKeys.size - 1] with
  | none => rfl
  | some l =>
    exfalso
    have hm := hmarked _ l (by rw [Array.getElem?_eq_getElem hlt, hv])
    rw [indentColumns_getElem?] at hm
    unfold ScannerState.currentIndent at hgt
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)] at hgt
    rw [hsz, Array.getElem?_eq_getElem (by omega)] at hm
    simp at hm hgt
    omega

/-- Popping levels whose columns exceed every marked slot's column keeps the
    innermost pending key (the popped slots are empty). -/
lemma innermost_of_pop {s s' : ScannerState} (hs : SlotsOk s)
    (hind : s'.indents = s.indents.pop) (hpk : s'.pendingKeys = s.pendingKeys.pop)
    (hpos : 0 < s.pendingKeys.size)
    (htop : s.pendingKeys[s.pendingKeys.size - 1]? = some none) :
    s'.innermostPendingKey = s.innermostPendingKey := by
  rw [innermostPendingKey_eq, innermostPendingKey_eq]
  have hcols : s'.indentColumns = s.indentColumns.pop := by
    simp [ScannerState.indentColumns, hind, Array.map_pop]
  rw [hcols, hpk]
  exact innermost_pop_of_top_none _ _ (by rw [indentColumns_size]; exact hs.1.symm) hpos htop

lemma unwindIndentsLoop_innermost (s : ScannerState) (col : Int) (fuel : Nat)
    (hs : SlotsOk s)
    (hmarked : ∀ (i l : Nat), s.pendingKeys[i]? = some (some l) →
      s.indentColumns[i]?.getD (-1) ≤ col) :
    (unwindIndentsLoop s col fuel).innermostPendingKey = s.innermostPendingKey := by
  induction fuel generalizing s with
  | zero => simp [unwindIndentsLoop]
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · rename_i hguard
      obtain ⟨h1, h2, -⟩ := unwindPop_fields s
      have hsz := hs.1
      have hg : s.currentIndent > col ∧ s.indents.size > 1 := by simpa using hguard
      refine (ih _ (hs.pop h1 h2) ?_).trans
        (innermost_of_pop hs h1 h2 (by omega) (top_slot_none hs col hmarked hg.1 (by omega)))
      intro i l hi
      rw [h2, Array.getElem?_pop] at hi
      split at hi
      · have := hmarked i l hi
        rw [indentColumns_getElem?, h1, Array.getElem?_pop, if_pos (by omega)]
        rw [indentColumns_getElem?] at this; exact this
      · cases hi
    · rfl

/-- The `?`'s own write, block context: the level under it is marked. -/
lemma scanKey_pendingKeys {s s' : ScannerState} (h_noflow : s.inFlow = false)
    (hok : scanKey s = .ok s') :
    s'.pendingKeys = (pushMappingIndent s (s.col : Int)).pendingKeys.set!
      ((pushMappingIndent s (s.col : Int)).indents.size - 1) (some s.line) := by
  unfold scanKey at hok
  simp only [bind, Except.bind, h_noflow, Bool.not_false, ite_true] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals simp [h_noflow, advance_preserves_pendingKeys, emit_pendingKeys,
    L4YAML.Proofs.EmitterScannability.advance_preserves_indents, ScannerState.emit]

lemma inFlow_false_iff (s : ScannerState) : s.inFlow = false ↔ s.flowLevel = 0 := by
  simp [ScannerState.inFlow]

lemma scanKey_sound {s s' : ScannerState} (hok : scanKey s = .ok s')
    (hs : SlotsOk s) (hb : BaseOk s) (hst : StackOk s) (hbase : SentinelBase s)
    (hcol : s.inFlow = false → s.currentIndent ≤ (s.col : Int)) : Sound s' := by
  have hfl : s'.flowLevel = s.flowLevel :=
    L4YAML.Proofs.ScannerCorrectness.scanKey_preserves_flowLevel s s' hok
  have hstk : s'.explicitKeyStack = s.explicitKeyStack :=
    L4YAML.Proofs.ScannerEkStack.scanKey_preserves_explicitKeyStack s s' hok
  obtain ⟨hekl, hekc⟩ := L4YAML.Proofs.ExplicitKeyCoupling.scanKey_ok_explicitKey hok
  by_cases hf : s.inFlow = true
  · -- flow: slots and stack untouched, the register conjunct is vacuous
    have hpk := scanKey_pendingKeys_of_inFlow hf hok
    have hind := L4YAML.Proofs.FlowIndentStable.scanKey_indents_of_inFlow hf hok
    have hcols : s'.indentColumns = s.indentColumns := by simp [ScannerState.indentColumns, hind]
    have hinn : s'.innermostPendingKey = s.innermostPendingKey := by
      rw [innermostPendingKey_eq, innermostPendingKey_eq, hcols, hpk]
    have hpos : 0 < s.flowLevel := by simpa [ScannerState.inFlow] using hf
    refine ⟨⟨by rw [hpk, hind]; exact hs.1, ?_⟩, ?_, ?_, ?_⟩
    · intro i l hi; rw [hcols]; exact hs.2 i l (hpk ▸ hi)
    · intro h0; rw [hfl] at h0; omega
    · intro _; rw [hstk, hinn]; exact hb hpos
    · show s'.explicitKeyStack.size = s'.flowLevel; rw [hstk, hfl]; exact hst
  · have h_noflow : s.inFlow = false := by simpa using hf
    have h0 : s.flowLevel = 0 := (inFlow_false_iff s).1 h_noflow
    have hind := L4YAML.Proofs.PreprocessIndentStable.scanKey_indents h_noflow hok
    have hpk := scanKey_pendingKeys h_noflow hok
    obtain ⟨sp, hsp⟩ : ∃ sp, sp = pushMappingIndent s (s.col : Int) := ⟨_, rfl⟩
    rw [← hsp] at hind hpk
    have hsl : SlotsOk sp := hsp ▸ pushMappingIndent_slots s _ hs
    have hsz := hsl.1
    have hpos : 0 < sp.indents.size :=
      hsp ▸ (L4YAML.Proofs.IndentStackBase.pushMappingIndent_base s _ hbase).size_pos
    -- the top of the pushed stack is the `?`'s own column
    have htop_ci : sp.currentIndent = (s.col : Int) := by
      rw [hsp]
      exact Int.le_antisymm (L4YAML.Proofs.IndentStackCover.pushMappingIndent_top_le (hcol h_noflow))
        (L4YAML.Proofs.PreprocessIndentStable.pushMappingIndent_le s _)
    have htop : sp.indentColumns[sp.indents.size - 1]? = some (s.col : Int) := by
      rw [indentColumns_getElem?, Array.getElem?_eq_getElem (by omega)]
      simp only [Option.map_some]
      rw [← L4YAML.Proofs.IndentStackMono.currentIndent_eq_last hpos, htop_ci]
    have hcols' : s'.indentColumns = sp.indentColumns := by
      simp [ScannerState.indentColumns, hind]
    have hinn : s'.innermostPendingKey = (some s.line, (s.col : Int)) := by
      rw [innermostPendingKey_eq, hcols', hpk, ← hsz,
        innermost_set_top _ _ _ (by rw [indentColumns_size]; exact hsz.symm) (by omega)]
      rw [hsz, htop]; rfl
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hpk, hind, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hsz
    · intro i l hi
      rw [hpk, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hi
      rw [hcols']
      split at hi
      · rename_i heq
        subst heq
        exact ⟨(s.col : Int), htop, by omega⟩
      · exact hsl.2 i l hi
    · intro _; rw [hekl, hekc, hinn]
    · intro hpos'; rw [hfl] at hpos'; omega
    · show s'.explicitKeyStack.size = s'.flowLevel; rw [hstk, hfl]; exact hst

lemma scanValueClearKey_core (s : ScannerState) :
    (scanValueClearKey s).indents = s.indents ∧ (scanValueClearKey s).pendingKeys = s.pendingKeys ∧
    (scanValueClearKey s).flowLevel = s.flowLevel ∧
    (scanValueClearKey s).explicitKeyLine = s.explicitKeyLine ∧
    (scanValueClearKey s).explicitKeyCol = s.explicitKeyCol ∧
    (scanValueClearKey s).explicitKeyStack = s.explicitKeyStack := by
  unfold scanValueClearKey
  split <;> (try split) <;> (try split) <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `scanValuePrepare` pushes at most one empty slot: `SlotsOk` and the innermost
    pending key survive, as do the flow fields and the register. -/
lemma scanValuePrepare_core (s : ScannerState) (hs : SlotsOk s) :
    SlotsOk (scanValuePrepare s) ∧
    (scanValuePrepare s).innermostPendingKey = s.innermostPendingKey ∧
    (scanValuePrepare s).flowLevel = s.flowLevel ∧
    (scanValuePrepare s).explicitKeyLine = s.explicitKeyLine ∧
    (scanValuePrepare s).explicitKeyCol = s.explicitKeyCol ∧
    (scanValuePrepare s).explicitKeyStack = s.explicitKeyStack := by
  unfold scanValuePrepare
  split
  · split
    · split
      · refine ⟨hs.push_none { column := (s.simpleKey.pos.col : Int), isSequence := false } rfl rfl,
          ?_, rfl, rfl, rfl, rfl⟩
        rw [innermostPendingKey_eq, innermostPendingKey_eq]
        simp only [ScannerState.indentColumns, Array.map_push]
        exact innermost_push_none _ _ _ (by simp [hs.1])
      · exact ⟨hs, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨hs, rfl, rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨hs, rfl, rfl, rfl, rfl, rfl⟩
    · split
      · refine ⟨pushMappingIndent_slots s _ hs, ?_, ?_, ?_, ?_, ?_⟩ <;>
          unfold pushMappingIndent <;> split <;> try rfl
        rw [innermostPendingKey_eq, innermostPendingKey_eq]
        simp only [ScannerState.indentColumns, ScannerState.emit, Array.map_push]
        exact innermost_push_none _ _ _ (by simp [hs.1])
      · exact ⟨hs, rfl, rfl, rfl, rfl, rfl⟩

lemma innermost_none_snd (cols : Array Int) (pks : Array (Option Nat))
    (h : (PendingKeys.innermost cols pks).1 = none) : (PendingKeys.innermost cols pks).2 = -1 := by
  rw [innermost_eq_go] at h ⊢; exact go_none_snd cols pks _ h

/-- Item 359: no marked slot ⇒ the innermost pending key is empty, and under `Sound` in
    block context the register is `none` — `ExplicitValueRefused`'s scanner side. -/
lemma go_fst_none_of_noMarks (cols : Array Int) (pks : Array (Option Nat)) (n : Nat)
    (h : ∀ (i l : Nat), (pks[i]? : Option (Option Nat)) ≠ some (some l)) : (go cols pks n).1 = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [go]
    split
    · rename_i l hl
      exfalso
      cases hp : pks[n]? with
      | none => simp [hp] at hl
      | some o =>
        cases o with
        | none => simp [hp] at hl
        | some l' => exact h n l' hp
    · exact ih

lemma go_fst_some_of_marked (cols : Array Int) (pks : Array (Option Nat)) (n i l : Nat)
    (hi : i < n) (h : pks[i]? = some (some l)) : (go cols pks n).1 ≠ none := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [go]
    split
    · simp
    · rename_i hnone
      apply ih
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
      · exact hlt
      · subst heq; simp [h] at hnone

lemma innermost_fst_none_of_noMarks (cols : Array Int) (pks : Array (Option Nat))
    (h : ∀ (i l : Nat), (pks[i]? : Option (Option Nat)) ≠ some (some l)) :
    (PendingKeys.innermost cols pks).1 = none := by
  rw [innermost_eq_go]; exact go_fst_none_of_noMarks cols pks _ h

lemma explicitKeyLine_none_of_noMarks {s : ScannerState} (hs : Sound s) (hfl : s.flowLevel = 0)
    (h : ∀ (i l : Nat), (s.pendingKeys[i]? : Option (Option Nat)) ≠ some (some l)) :
    s.explicitKeyLine = none := by
  have hr := hs.reg hfl
  have := congrArg Prod.fst hr
  simp only at this
  rw [this, innermostPendingKey_eq]
  exact innermost_fst_none_of_noMarks _ _ h

lemma scanValue_sound {s s' : ScannerState} (hok : scanValue s = .ok s') (h : Sound s) :
    Sound s' := by
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  simp only [Except.ok.injEq] at hok; subst hok
  obtain ⟨hck1, hck2, hck3, hck4, hck5, hck6⟩ := scanValueClearKey_core s
  have hs_kc : SlotsOk (scanValueClearKey s) := by
    refine ⟨by rw [hck1, hck2]; exact h.slots.1, ?_⟩
    intro i l hi; rw [hck2] at hi
    have hcols : (scanValueClearKey s).indentColumns = s.indentColumns := by
      simp [ScannerState.indentColumns, hck1]
    rw [hcols]; exact h.slots.2 i l hi
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := scanValuePrepare_core _ hs_kc
  have hinn_kc : (scanValueClearKey s).innermostPendingKey = s.innermostPendingKey := by
    simp [innermostPendingKey_eq, ScannerState.indentColumns, hck1, hck2]
  -- the emitted-and-advanced state before the final write
  have hadv_pk : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).pendingKeys
      = (scanValuePrepare (scanValueClearKey s)).pendingKeys := by
    rw [advance_preserves_pendingKeys, emit_pendingKeys]
  have hadv_ind : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).indents
      = (scanValuePrepare (scanValueClearKey s)).indents := by
    rw [L4YAML.Proofs.EmitterScannability.advance_preserves_indents]; rfl
  have hadv_cols : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).indentColumns
      = (scanValuePrepare (scanValueClearKey s)).indentColumns := by
    simp [ScannerState.indentColumns, hadv_ind]
  have hadv_fl : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).flowLevel
      = s.flowLevel := by
    rw [L4YAML.Proofs.ScannerLoopInvariant.advance_flowLevel]; simp [ScannerState.emit, ScannerState.emitAt, hp3, hck3]
  have hadv_st : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).explicitKeyStack
      = s.explicitKeyStack := by
    rw [L4YAML.Proofs.ScannerEkStack.advance_preserves_explicitKeyStack,
        L4YAML.Proofs.ScannerEkStack.emit_preserves_explicitKeyStack, hp6, hck6]
  have hadv_inn : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).innermostPendingKey
      = s.innermostPendingKey := by
    rw [innermostPendingKey_eq, hadv_cols, hadv_pk, ← innermostPendingKey_eq, hp2, hinn_kc]
  have hadv_slots : SlotsOk (((scanValuePrepare (scanValueClearKey s)).emit .value).advance) := by
    refine ⟨by rw [hadv_pk, hadv_ind]; exact hp1.1, ?_⟩
    intro i l hi; rw [hadv_pk] at hi; rw [hadv_cols]; exact hp1.2 i l hi
  by_cases hf : s.inFlow = true
  · -- flow: the `:` ends any pending key; the stack and the slots are untouched
    have hpos : 0 < s.flowLevel := by simpa [ScannerState.inFlow] using hf
    simp only [hf, Bool.true_or, ite_true]
    refine ⟨⟨hadv_slots.1, hadv_slots.2⟩, ?_, ?_, ?_⟩
    · intro h0; simp only [hadv_fl] at h0; omega
    · intro _
      change ((((scanValuePrepare (scanValueClearKey s)).emit .value).advance).explicitKeyStack)[0]? = some (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).innermostPendingKey
      rw [hadv_st, hadv_inn]; exact h.base hpos
    · show _ = _; rw [hadv_st, hadv_fl]; exact h.stack
  · have h_noflow : s.inFlow = false := by simpa using hf
    have h0 : s.flowLevel = 0 := (inFlow_false_iff s).1 h_noflow
    simp only [h_noflow, Bool.false_eq_true, ↓reduceIte]
    by_cases hsv : scanValueKeySurvives s (scanValueClearKey s) = true
    · simp only [hsv, ↓reduceIte]
      refine ⟨⟨hadv_slots.1, hadv_slots.2⟩, ?_, ?_, ?_⟩
      · intro _
        change (_, _) = (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).innermostPendingKey
        rw [hck4, hck5, hadv_inn, ← h.reg h0]
        cases hek : s.explicitKeyLine with
        | some l => rfl
        | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
          have := innermost_none_snd s.indentColumns s.pendingKeys
            (by rw [← innermostPendingKey_eq, ← h.reg h0, hek])
          rw [← innermostPendingKey_eq, ← h.reg h0] at this
          simp only at this; rw [this]
      · intro hpos; simp only [hadv_fl] at hpos; omega
      · show _ = _; rw [hadv_st, hadv_fl]; exact h.stack
    · simp only [hsv, Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · show (PendingKeys.closeAt _ _ _).size = _
        rw [closeAt_size]; exact hadv_slots.1
      · intro i l hi
        obtain ⟨hm, -⟩ := closeAt_marked _ _ _ _ _ hi
        exact hadv_slots.2 i l hm
      · intro _; rfl
      · intro hpos; simp only [hadv_fl] at hpos; omega
      · show _ = _; rw [hadv_st, hadv_fl]; exact h.stack

/-- Inside flow the register is not read by `Sound`; transport along a step that
    keeps the slots, the frames, the flow level and the saved pairs. -/
lemma Sound.of_eq_inFlow {s s' : ScannerState} (h : Sound s) (hpos : 0 < s.flowLevel)
    (hpk : s'.pendingKeys = s.pendingKeys) (hind : s'.indents = s.indents)
    (hfl : s'.flowLevel = s.flowLevel) (hst : s'.explicitKeyStack = s.explicitKeyStack) :
    Sound s' := by
  have hcols : s'.indentColumns = s.indentColumns := by
    simp [ScannerState.indentColumns, hind]
  have hinn : s'.innermostPendingKey = s.innermostPendingKey := by
    simp [innermostPendingKey_eq, hcols, hpk]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpk, hind]; exact h.slots.1
  · intro i l hi; rw [hcols]; exact h.slots.2 i l (hpk ▸ hi)
  · intro h0; rw [hfl] at h0; omega
  · intro _; rw [hst, hinn]; exact h.base hpos
  · show s'.explicitKeyStack.size = s'.flowLevel
    rw [hst, hfl]; exact h.stack

lemma pushSequenceIndent_flowLevel (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).flowLevel = s.flowLevel := by
  unfold pushSequenceIndent; split <;> rfl

lemma pushSequenceIndent_explicitKeyLine (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).explicitKeyLine = s.explicitKeyLine := by
  unfold pushSequenceIndent; split <;> rfl

lemma pushSequenceIndent_explicitKeyCol (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).explicitKeyCol = s.explicitKeyCol := by
  unfold pushSequenceIndent; split <;> rfl

lemma pushSequenceIndent_explicitKeyStack (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).explicitKeyStack = s.explicitKeyStack := by
  unfold pushSequenceIndent; split <;> rfl

lemma scanBlockEntry_pendingKeys {s s' : ScannerState} (hnf : s.inFlow = false)
    (hok : scanBlockEntry s = .ok s') :
    s'.pendingKeys = (pushSequenceIndent s (s.col : Int)).pendingKeys := by
  unfold scanBlockEntry at hok
  simp only [bind, Except.bind, hnf, Bool.not_false, if_true] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals simp [advance_preserves_pendingKeys, emit_pendingKeys]

/-- `-` in block context: the sequence level is pushed (empty slot), the
    register and the saved pairs are untouched. -/
lemma scanBlockEntry_sound {s s' : ScannerState} (hnf : s.inFlow = false)
    (hok : scanBlockEntry s = .ok s') (h : Sound s) : Sound s' := by
  obtain ⟨hekl, hekc⟩ := L4YAML.Proofs.ExplicitKeyCoupling.scanBlockEntry_preserves_explicitKey hok
  refine Sound.of_eq (pushSequenceIndent_sound s (s.col : Int) h)
    (scanBlockEntry_pendingKeys hnf hok)
    (L4YAML.Proofs.PreprocessIndentStable.scanBlockEntry_indents hnf hok) ?_ ?_ ?_ ?_
  · rw [pushSequenceIndent_flowLevel]
    exact L4YAML.Proofs.ScannerCorrectness.scanBlockEntry_preserves_flowLevel s s' hok
  · rw [pushSequenceIndent_explicitKeyLine]; exact hekl
  · rw [pushSequenceIndent_explicitKeyCol]; exact hekc
  · rw [pushSequenceIndent_explicitKeyStack]
    exact L4YAML.Proofs.ScannerEkStack.scanBlockEntry_preserves_explicitKeyStack s s' hok

/-- Opening a flow collection saves the register pair on the stack and clears
    the register.  At depth 0 the saved pair is the innermost pending key
    (`RegOk`); deeper, slot 0 of the stack is untouched (`BaseOk`). -/
lemma scanFlowSequenceStart_sound (s : ScannerState) (h : Sound s) :
    Sound (scanFlowSequenceStart s) := by
  have hpk := scanFlowSequenceStart_preserves_pendingKeys s
  have hind : (scanFlowSequenceStart s).indents = s.indents := by
    unfold scanFlowSequenceStart
    simp only [L4YAML.Proofs.EmitterScannability.advance_preserves_indents, ScannerState.emit,
      ScannerState.emitAt]
  have hst := L4YAML.Proofs.ScannerCorrectness.scanFlowSequenceStart_ek_pushed s
  have hfl := L4YAML.Proofs.ScannerContracts.scanFlowSequenceStart_flowLevel s
  have hcols : (scanFlowSequenceStart s).indentColumns = s.indentColumns := by
    simp [ScannerState.indentColumns, hind]
  have hinn : (scanFlowSequenceStart s).innermostPendingKey = s.innermostPendingKey := by
    simp [innermostPendingKey_eq, hcols, hpk]
  have hsz : s.explicitKeyStack.size = s.flowLevel := h.stack
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpk, hind]; exact h.slots.1
  · intro i l hi; rw [hcols]; exact h.slots.2 i l (hpk ▸ hi)
  · intro h0; rw [hfl] at h0; omega
  · intro _
    rw [hst, hinn, Array.getElem?_push]
    rcases Nat.eq_zero_or_pos s.flowLevel with h0 | hpos
    · rw [if_pos (by omega), h.reg h0]
    · rw [if_neg (by omega)]; exact h.base hpos
  · show (scanFlowSequenceStart s).explicitKeyStack.size = (scanFlowSequenceStart s).flowLevel
    rw [hst, hfl, Array.size_push, hsz]

lemma scanFlowMappingStart_sound (s : ScannerState) (h : Sound s) :
    Sound (scanFlowMappingStart s) := by
  have hpk := scanFlowMappingStart_preserves_pendingKeys s
  have hind : (scanFlowMappingStart s).indents = s.indents := by
    unfold scanFlowMappingStart
    simp only [L4YAML.Proofs.EmitterScannability.advance_preserves_indents, ScannerState.emit,
      ScannerState.emitAt]
  have hst := L4YAML.Proofs.ScannerCorrectness.scanFlowMappingStart_ek_pushed s
  have hfl := L4YAML.Proofs.ScannerContracts.scanFlowMappingStart_flowLevel s
  have hcols : (scanFlowMappingStart s).indentColumns = s.indentColumns := by
    simp [ScannerState.indentColumns, hind]
  have hinn : (scanFlowMappingStart s).innermostPendingKey = s.innermostPendingKey := by
    simp [innermostPendingKey_eq, hcols, hpk]
  have hsz : s.explicitKeyStack.size = s.flowLevel := h.stack
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpk, hind]; exact h.slots.1
  · intro i l hi; rw [hcols]; exact h.slots.2 i l (hpk ▸ hi)
  · intro h0; rw [hfl] at h0; omega
  · intro _
    rw [hst, hinn, Array.getElem?_push]
    rcases Nat.eq_zero_or_pos s.flowLevel with h0 | hpos
    · rw [if_pos (by omega), h.reg h0]
    · rw [if_neg (by omega)]; exact h.base hpos
  · show (scanFlowMappingStart s).explicitKeyStack.size = (scanFlowMappingStart s).flowLevel
    rw [hst, hfl, Array.size_push, hsz]

/-- Closing a flow collection restores the saved pair.  Back at depth 0 the
    restored pair is slot 0 (`BaseOk` of the opener); deeper, slot 0 survives
    the pop. -/
lemma scanFlowSequenceEnd_sound (s : ScannerState) (h : Sound s) (hpos : 0 < s.flowLevel) :
    Sound (scanFlowSequenceEnd s) := by
  have hpk := scanFlowSequenceEnd_preserves_pendingKeys s
  have hind : (scanFlowSequenceEnd s).indents = s.indents := by
    unfold scanFlowSequenceEnd; dsimp only []
    simp only [L4YAML.Proofs.EmitterScannability.advance_preserves_indents, ScannerState.emit]
  have hst := L4YAML.Proofs.ScannerCorrectness.scanFlowSequenceEnd_ekstack_popped s
  have hfl := L4YAML.Proofs.ScannerFlowCollection.scanFlowSequenceEnd_flowLevel_pos s hpos
  have hreg : ((scanFlowSequenceEnd s).explicitKeyLine, (scanFlowSequenceEnd s).explicitKeyCol)
      = s.explicitKeyStack.back?.getD (none, -1) := rfl
  have hcols : (scanFlowSequenceEnd s).indentColumns = s.indentColumns := by
    simp [ScannerState.indentColumns, hind]
  have hinn : (scanFlowSequenceEnd s).innermostPendingKey = s.innermostPendingKey := by
    simp [innermostPendingKey_eq, hcols, hpk]
  have hsz : s.explicitKeyStack.size = s.flowLevel := h.stack
  have hb := h.base hpos
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpk, hind]; exact h.slots.1
  · intro i l hi; rw [hcols]; exact h.slots.2 i l (hpk ▸ hi)
  · intro h0
    rw [hfl] at h0
    have h1 : s.explicitKeyStack.size - 1 = 0 := by omega
    rw [hreg, hinn, Array.back?, h1, hb]; rfl
  · intro hpos'
    rw [hfl] at hpos'
    rw [hst, hinn, Array.getElem?_pop, if_pos (by omega)]; exact hb
  · show (scanFlowSequenceEnd s).explicitKeyStack.size = (scanFlowSequenceEnd s).flowLevel
    rw [hst, hfl, Array.size_pop, hsz]

lemma scanFlowMappingEnd_sound (s : ScannerState) (h : Sound s) (hpos : 0 < s.flowLevel) :
    Sound (scanFlowMappingEnd s) := by
  have hpk := scanFlowMappingEnd_preserves_pendingKeys s
  have hind : (scanFlowMappingEnd s).indents = s.indents := by
    unfold scanFlowMappingEnd; dsimp only []
    simp only [L4YAML.Proofs.EmitterScannability.advance_preserves_indents, ScannerState.emit]
  have hst := L4YAML.Proofs.ScannerCorrectness.scanFlowMappingEnd_ekstack_popped s
  have hfl := L4YAML.Proofs.ScannerFlowCollection.scanFlowMappingEnd_flowLevel_pos s hpos
  have hreg : ((scanFlowMappingEnd s).explicitKeyLine, (scanFlowMappingEnd s).explicitKeyCol)
      = s.explicitKeyStack.back?.getD (none, -1) := rfl
  have hcols : (scanFlowMappingEnd s).indentColumns = s.indentColumns := by
    simp [ScannerState.indentColumns, hind]
  have hinn : (scanFlowMappingEnd s).innermostPendingKey = s.innermostPendingKey := by
    simp [innermostPendingKey_eq, hcols, hpk]
  have hsz : s.explicitKeyStack.size = s.flowLevel := h.stack
  have hb := h.base hpos
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpk, hind]; exact h.slots.1
  · intro i l hi; rw [hcols]; exact h.slots.2 i l (hpk ▸ hi)
  · intro h0
    rw [hfl] at h0
    have h1 : s.explicitKeyStack.size - 1 = 0 := by omega
    rw [hreg, hinn, Array.back?, h1, hb]; rfl
  · intro hpos'
    rw [hfl] at hpos'
    rw [hst, hinn, Array.getElem?_pop, if_pos (by omega)]; exact hb
  · show (scanFlowMappingEnd s).explicitKeyStack.size = (scanFlowMappingEnd s).flowLevel
    rw [hst, hfl, Array.size_pop, hsz]

/-- `,` is dispatched only inside flow (`flowEndOutsideFlow` otherwise); it
    clears the register line, which `Sound` does not read there. -/
lemma scanFlowEntry_sound {s s' : ScannerState} (hok : scanFlowEntry s = .ok s') (h : Sound s)
    (hpos : 0 < s.flowLevel) : Sound s' :=
  Sound.of_eq_inFlow h hpos (scanFlowEntry_preserves_pendingKeys hok)
    (L4YAML.Proofs.FlowIndentStable.scanFlowEntry_preserves_indents hok)
    (L4YAML.Proofs.ScannerFlowCollection.scanFlowEntry_preserves_flowLevel s s' hok)
    (L4YAML.Proofs.ScannerEkStack.scanFlowEntry_preserves_explicitKeyStack s s' hok)

/-! ### Document markers: unwinding to the sentinel leaves no marked slot -/

lemma unwindIndents_slots (s : ScannerState) (col : Int) (h : SlotsOk s) :
    SlotsOk (unwindIndents s col) := by
  unfold unwindIndents; exact unwindIndentsLoop_slots s col _ h

/-- Unwinding to `-1` on a monotone sentinel-based stack pops every level with a
    column ≥ 0, hence (by `SlotsOk`) every marked slot: the innermost pending
    key reads `(none, -1)`. -/
lemma unwindIndents_neg_innermost {s : ScannerState} (hs : SlotsOk s) (hm : Mono s)
    (hbase : SentinelBase s) :
    (unwindIndents s (-1)).innermostPendingKey = (none, -1) := by
  have hs' := unwindIndents_slots s (-1) hs
  have hm' : Mono (unwindIndents s (-1)) := L4YAML.Proofs.IndentStackMono.unwindIndents_mono s (-1) hm
  have hb' : SentinelBase (unwindIndents s (-1)) :=
    L4YAML.Proofs.IndentStackBase.unwindIndents_base s (-1) hbase
  have htop : (unwindIndents s (-1)).currentIndent ≤ -1 := by
    rcases L4YAML.Proofs.PreprocessIndentStable.unwindIndents_terminal s (-1) with h1 | h2
    · exact h1
    · rw [hb'.currentIndent_of_size_le_one h2]; exact Int.le_refl _
  have hnone : ∀ (i l : Nat), (unwindIndents s (-1)).pendingKeys[i]? = some (some l) → False := by
    intro i l hi
    obtain ⟨c, hc, hc0⟩ := hs'.2 i l hi
    simp only [ScannerState.indentColumns, Array.getElem?_map, Option.map_eq_some_iff] at hc
    obtain ⟨e, he, hec⟩ := hc
    have hle := hm'.le_currentIndent e (Array.mem_of_getElem? he)
    omega
  rcases hinn : (unwindIndents s (-1)).innermostPendingKey with ⟨ol, c⟩
  rcases ol with _ | l
  · rw [innermostPendingKey_eq, innermost_eq_go] at hinn
    have h2 := go_none_snd _ _ _ (by rw [hinn])
    rw [hinn] at h2
    simp only at h2
    rw [h2]
  · exfalso
    rw [innermostPendingKey_eq] at hinn
    obtain ⟨i, _, hi, _⟩ := innermost_some_mem _ _ l c hinn
    exact hnone i l hi

/-- The shape both document markers share: unwind to the sentinel, reset the
    register, keep the saved pairs (empty at depth 0). -/
lemma Sound.of_doc_reset {s s' : ScannerState} (h : Sound s) (hfl : s.flowLevel = 0)
    (hm : Mono s) (hbase : SentinelBase s)
    (hpk : s'.pendingKeys = (unwindIndents s (-1)).pendingKeys)
    (hind : s'.indents = (unwindIndents s (-1)).indents)
    (hfl' : s'.flowLevel = s.flowLevel)
    (hekl : s'.explicitKeyLine = none) (hekc : s'.explicitKeyCol = -1)
    (hst : s'.explicitKeyStack = s.explicitKeyStack) : Sound s' := by
  have hs' := unwindIndents_slots s (-1) h.slots
  have hinn0 := unwindIndents_neg_innermost h.slots hm hbase
  have hcols : s'.indentColumns = (unwindIndents s (-1)).indentColumns := by
    simp [ScannerState.indentColumns, hind]
  have hinn : s'.innermostPendingKey = (none, -1) := by
    rw [innermostPendingKey_eq, hcols, hpk, ← innermostPendingKey_eq, hinn0]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpk, hind]; exact hs'.1
  · intro i l hi; rw [hcols]; exact hs'.2 i l (hpk ▸ hi)
  · intro _; rw [hekl, hekc, hinn]
  · intro h0; rw [hfl', hfl] at h0; omega
  · show s'.explicitKeyStack.size = s'.flowLevel
    rw [hst, hfl', h.stack]

lemma scanDocumentStart_sound (s : ScannerState) (h : Sound s) (hfl : s.flowLevel = 0)
    (hm : Mono s) (hbase : SentinelBase s) : Sound (scanDocumentStart s) := by
  refine Sound.of_doc_reset h hfl hm hbase ?_ ?_ ?_ rfl rfl
    (L4YAML.Proofs.ScannerEkStack.scanDocumentStart_preserves_explicitKeyStack s)
  · unfold scanDocumentStart; simp [advanceN_preserves_pendingKeys, emit_pendingKeys]
  · unfold scanDocumentStart
    simp [L4YAML.Proofs.IndentStackBase.advanceN_preserves_indents,
      L4YAML.Proofs.ScannerContracts.emit_indents]
  · unfold scanDocumentStart
    simp [L4YAML.Proofs.ScannerCorrectness.advanceN_preserves_flowLevel, ScannerState.emit,
      ScannerState.emitAt, L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_flowLevel]

lemma scanDocumentEnd_sound {s s' : ScannerState} (hok : scanDocumentEnd s = .ok s') (h : Sound s)
    (hfl : s.flowLevel = 0) (hm : Mono s) (hbase : SentinelBase s) : Sound s' := by
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals
    refine Sound.of_doc_reset h hfl hm hbase ?_ ?_ ?_ rfl rfl ?_
  all_goals (try simp [advanceN_preserves_pendingKeys, emit_pendingKeys])
  all_goals (try simp [L4YAML.Proofs.IndentStackBase.advanceN_preserves_indents,
      L4YAML.Proofs.ScannerContracts.emit_indents])
  all_goals (try simp [L4YAML.Proofs.ScannerCorrectness.advanceN_preserves_flowLevel,
      ScannerState.emit, ScannerState.emitAt,
      L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_flowLevel])
  all_goals simp [L4YAML.Proofs.ScannerEkStack.advanceN_preserves_explicitKeyStack,
      L4YAML.Proofs.ScannerEkStack.emit_preserves_explicitKeyStack,
      L4YAML.Proofs.ScannerEkStack.unwindIndents_preserves_explicitKeyStack]

/-! ## §4  The preprocess and the dispatchers -/

/-- The preprocess keeps everything but `RegOk`, and keeps `RegOk` unless the
    next character is a `?` — the one hook exemption that can outlive the pop
    of the key's level (`- ? a⏎? b`); `scanKey` overwrites the register. -/
lemma SlotsOk.of_eq {s s' : ScannerState} (h : SlotsOk s)
    (hpk : s'.pendingKeys = s.pendingKeys) (hind : s'.indents = s.indents) : SlotsOk s' := by
  have hcols : s'.indentColumns = s.indentColumns := by simp [ScannerState.indentColumns, hind]
  refine ⟨?_, ?_⟩
  · rw [hpk, hind]; exact h.1
  · intro i l hi; rw [hcols]; exact h.2 i l (hpk ▸ hi)

/-- Every marked slot sits at or left of the innermost pending key: `go` returns
    the marked slot of largest index, and the stack is monotone. -/
lemma go_marked_le (cols : Array Int) (pks : Array (Option Nat)) (n i l : Nat) (hi : i < n)
    (hpk : pks[i]? = some (some l))
    (hmono : ∀ (i j : Nat), i ≤ j → ∀ (ci cj : Int), cols[i]? = some ci → cols[j]? = some cj →
      ci ≤ cj)
    (hcols : ∀ (j l' : Nat), pks[j]? = some (some l') → ∃ c, cols[j]? = some c) :
    cols[i]?.getD (-1) ≤ (go cols pks n).2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [go]
    rcases Nat.lt_or_ge i n with hlt | hge
    · split
      · rename_i l' hl'
        have hpn : pks[n]? = some (some l') := by
          rcases hn : pks[n]? with _ | x
          · simp [hn] at hl'
          · simp [hn] at hl'; rw [hl']
        obtain ⟨ci, hci⟩ := hcols i l hpk
        obtain ⟨cn, hcn⟩ := hcols n l' hpn
        simp only [hci, hcn, Option.getD_some]
        exact hmono i n (Nat.le_of_lt hlt) ci cn hci hcn
      · exact ih hlt
    · have hin : i = n := by omega
      subst hin
      split
      · exact Int.le_refl _
      · rename_i hl'; rw [hpk] at hl'; simp at hl'

lemma marked_le_innermost {s : ScannerState} (hs : SlotsOk s) (hm : Mono s) (i l : Nat)
    (hi : s.pendingKeys[i]? = some (some l)) :
    s.indentColumns[i]?.getD (-1) ≤ s.innermostPendingKey.2 := by
  rw [innermostPendingKey_eq, innermost_eq_go]
  have hlt : i < s.pendingKeys.size := by
    rcases Nat.lt_or_ge i s.pendingKeys.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hi
  refine go_marked_le _ _ _ i l hlt hi ?_ ?_
  · intro i j hij ci cj hci hcj
    simp only [ScannerState.indentColumns, Array.getElem?_map, Option.map_eq_some_iff] at hci hcj
    obtain ⟨ei, hei, rfl⟩ := hci
    obtain ⟨ej, hej, rfl⟩ := hcj
    have hj : j < s.indents.size := by
      rcases Nat.lt_or_ge j s.indents.size with h | h
      · exact h
      · simp [Array.getElem?_eq_none h] at hej
    have hi' : i < s.indents.size := by omega
    have hle := L4YAML.Proofs.IndentStackMono.MonoArr.le_last hm j hj i hi' hij
    rw [Array.getElem?_eq_getElem hi', Option.some.injEq] at hei
    rw [Array.getElem?_eq_getElem hj, Option.some.injEq] at hej
    subst hei; subst hej; exact hle
  · intro j l' hj
    obtain ⟨c, hc, _⟩ := hs.2 j l' hj
    exact ⟨c, hc⟩

/-- The hook never moves the cursor. -/
lemma closeStaleExplicitKey_peek (s : ScannerState) :
    (closeStaleExplicitKey s).peek? = s.peek? := by
  rcases closeStaleExplicitKey_cases s with h | ⟨_, _, h⟩ <;> rw [h] <;> rfl

/-- Outside flow, with a character under the cursor, the hook either re-reads
    the register or leaves it because the cursor is at or right of the register
    column (or the register is already dead). -/
lemma closeStaleExplicitKey_spec (s : ScannerState) (hnf : s.inFlow = false) {c : Char}
    (hpeek : s.peek? = some c) :
    closeStaleExplicitKey s = (s.closeStaleAt c).readPendingKey ∨
    (closeStaleExplicitKey s = s ∧
      (s.explicitKeyLine = none ∨ s.explicitKeyCol ≤ (s.col : Int))) := by
  unfold closeStaleExplicitKey
  rw [hnf, hpeek]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rcases hekl : s.explicitKeyLine with _ | ekLine
  · exact Or.inr ⟨rfl, Or.inl rfl⟩
  · dsimp only
    split
    · exact Or.inl rfl
    · rename_i hcond
      exact Or.inr ⟨rfl, Or.inr (staleGate_false_le (Bool.eq_false_iff.mpr hcond))⟩

/-- The hook after an unwind at the cursor column.  The unwind may have popped
    the register's own level; whatever it popped, the hook either re-reads the
    register (`RegOk` by construction) or finds the cursor at or right of the
    register column, in which case no marked slot was popped and the register is
    still the innermost. -/
lemma hook_after_unwind {s0 : ScannerState} (h : Sound s0) (hm : Mono s0) (hnf : s0.inFlow = false)
    {c : Char} (t : ScannerState)
    (ht_pk : t.pendingKeys = (unwindIndents s0 (s0.col : Int)).pendingKeys)
    (ht_ind : t.indents = (unwindIndents s0 (s0.col : Int)).indents)
    (ht_fl : t.flowLevel = s0.flowLevel)
    (ht_ekl : t.explicitKeyLine = s0.explicitKeyLine) (ht_ekc : t.explicitKeyCol = s0.explicitKeyCol)
    (ht_st : t.explicitKeyStack = s0.explicitKeyStack) (ht_col : t.col = s0.col)
    (hpeek : (closeStaleExplicitKey t).peek? = some c) :
    Sound (closeStaleExplicitKey t) := by
  have h0 : s0.flowLevel = 0 := by simp [ScannerState.inFlow] at hnf; omega
  have hsu : SlotsOk (unwindIndents s0 (s0.col : Int)) := unwindIndents_slots _ _ h.slots
  have hs_t : SlotsOk t := SlotsOk.of_eq hsu ht_pk ht_ind
  have hfl_t : t.flowLevel = 0 := ht_fl.trans h0
  have hb_t : BaseOk t := fun hp => by rw [hfl_t] at hp; exact absurd hp (Nat.lt_irrefl 0)
  have hstk_t : StackOk t := by
    show t.explicitKeyStack.size = t.flowLevel
    rw [ht_st, ht_fl]; exact h.stack
  have hnf_t : t.inFlow = false := by simp [ScannerState.inFlow, hfl_t]
  have hpeek_t : t.peek? = some c := by rw [← closeStaleExplicitKey_peek t]; exact hpeek
  have hreg0 := h.reg h0
  have hmarked : ∀ (i l : Nat), s0.pendingKeys[i]? = some (some l) →
      s0.indentColumns[i]?.getD (-1) ≤ s0.explicitKeyCol := by
    intro i l hi
    have hle := marked_le_innermost h.slots hm i l hi
    rw [← hreg0] at hle
    exact hle
  rcases closeStaleExplicitKey_spec t hnf_t hpeek_t with hre | ⟨hid, hwhy⟩
  · rw [hre]
    refine readPendingKey_sound (closeStaleAt_slots hs_t _) (fun hp => ?_) hstk_t
    simp only [ScannerState.closeStaleAt] at hp
    rw [hfl_t] at hp; exact absurd hp (Nat.lt_irrefl 0)
  · rw [hid]
    refine ⟨hs_t, fun _ => ?_, hb_t, hstk_t⟩
    -- the marked slots of `s0` sit at or left of the cursor, so the unwind kept them
    have hmarked' : ∀ (i l : Nat), s0.pendingKeys[i]? = some (some l) →
        s0.indentColumns[i]?.getD (-1) ≤ (s0.col : Int) := by
      intro i l hi
      have hle := hmarked i l hi
      rcases hwhy with hnone | hcol
      · rw [ht_ekl] at hnone
        have hsnd : s0.innermostPendingKey.2 = -1 := by
          rw [innermostPendingKey_eq, innermost_eq_go]
          apply go_none_snd
          rw [← innermost_eq_go, ← innermostPendingKey_eq, ← hreg0, hnone]
        rw [← hreg0] at hsnd
        simp only at hsnd
        have : (0 : Int) ≤ (s0.col : Int) := Int.ofNat_nonneg _
        omega
      · rw [ht_ekc, ht_col] at hcol
        exact Int.le_trans hle hcol
    have hinn_u : (unwindIndents s0 (s0.col : Int)).innermostPendingKey = s0.innermostPendingKey := by
      unfold unwindIndents; exact unwindIndentsLoop_innermost s0 _ _ h.slots hmarked'
    have hcols_t : t.indentColumns = (unwindIndents s0 (s0.col : Int)).indentColumns := by
      simp [ScannerState.indentColumns, ht_ind]
    show (t.explicitKeyLine, t.explicitKeyCol) = t.innermostPendingKey
    rw [ht_ekl, ht_ekc, innermostPendingKey_eq, hcols_t, ht_pk, ← innermostPendingKey_eq, hinn_u]
    exact hreg0

/-- **Preprocess keeps the carrier.**  With the hook firing on `col ≤ ekCol`
    alone (item 338 dropped its same-line and `?` exemptions), the register is
    re-read whenever the unwind could have popped its level. -/
lemma preprocess_sound {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess s = .ok (some (s', c))) (h : Sound s) (hm : Mono s) :
    Sound s' := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  split at hok
  · contradiction
  · rename_i s_skip h_skip
    have hind_skip := L4YAML.Proofs.PreprocessIndentStable.skipToContent_preserves_indents s s_skip h_skip
    have hS : Sound s_skip := Sound.of_eq h (skipToContent_preserves_pendingKeys s s_skip h_skip)
      hind_skip (L4YAML.Proofs.ScannerCorrectness.skipToContent_preserves_flowLevel s s_skip h_skip)
      (L4YAML.Proofs.ExplicitKeyCoupling.skipToContent_preserves_explicitKeyLine s s_skip h_skip)
      (L4YAML.Proofs.ExplicitKeyCoupling.skipToContent_preserves_explicitKeyCol s s_skip h_skip)
      (L4YAML.Proofs.ScannerEkStack.skipToContent_preserves_explicitKeyStack s s_skip h_skip)
    have hM : Mono s_skip := hm.of_indents_eq hind_skip
    split at hok
    · simp at hok
    · split at hok
      · rename_i hnic
        have hnf : s_skip.inFlow = false := by
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hnic; exact hnic.1
        split at hok
        · contradiction
        · split at hok
          · simp at hok
          · rename_i cpk hpeek
            simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine hook_after_unwind hS hM hnf _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hpeek
            · rw [saveSimpleKey_preserves_pendingKeys]
            · rw [L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_preserves_indents]
            · rw [L4YAML.Proofs.ScannerCorrectness.saveSimpleKey_preserves_flowLevel]
              exact L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_flowLevel _ _
            · rw [L4YAML.Proofs.ExplicitKeyCoupling.saveSimpleKey_preserves_explicitKeyLine]
              exact L4YAML.Proofs.ExplicitKeyCoupling.unwindIndents_preserves_explicitKeyLine _ _
            · rw [L4YAML.Proofs.ExplicitKeyCoupling.saveSimpleKey_preserves_explicitKeyCol]
              exact L4YAML.Proofs.ExplicitKeyCoupling.unwindIndents_preserves_explicitKeyCol _ _
            · rw [L4YAML.Proofs.ScannerEkStack.saveSimpleKey_preserves_explicitKeyStack]
              exact L4YAML.Proofs.ScannerEkStack.unwindIndents_preserves_explicitKeyStack _ _
            · rw [L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_col]
              exact L4YAML.Proofs.PreprocessIndentStable.unwindIndents_col _ _
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            have hT : Sound (saveSimpleKey s_skip) := Sound.of_eq hS
              (saveSimpleKey_preserves_pendingKeys _)
              (L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_preserves_indents _)
              (L4YAML.Proofs.ScannerCorrectness.saveSimpleKey_preserves_flowLevel _)
              (L4YAML.Proofs.ExplicitKeyCoupling.saveSimpleKey_preserves_explicitKeyLine _)
              (L4YAML.Proofs.ExplicitKeyCoupling.saveSimpleKey_preserves_explicitKeyCol _)
              (L4YAML.Proofs.ScannerEkStack.saveSimpleKey_preserves_explicitKeyStack _)
            exact closeStaleExplicitKey_sound hT

/-- With every marked slot at a non-negative column (`SlotsOk`), a column-0 content landing
    (no indicator under the cursor) closes them all, so nothing is left to re-read. -/
lemma innermost_closeStale_col0 (cols : Array Int) (pks : Array (Option Nat)) {c : Char}
    {next : Option Char}
    (hs : ∀ (i l : Nat), pks[i]? = some (some l) → ∃ m, cols[i]? = some m ∧ 0 ≤ m)
    (hind : PendingKeys.indicatorAt c next = false) :
    (PendingKeys.innermost cols (PendingKeys.closeStale cols pks 0 c next)).1 = none := by
  cases hx : (PendingKeys.innermost cols (PendingKeys.closeStale cols pks 0 c next)).1 with
  | none => rfl
  | some l =>
    exfalso
    obtain ⟨i, -, hi, -⟩ := innermost_some_mem cols _ l _ (Prod.ext hx rfl)
    obtain ⟨m, hm, hm0⟩ := hs i l (closeStale_marked _ _ _ _ _ _ _ hi)
    rw [closeStale_getElem?] at hi
    split at hi
    · simp only [Option.some.injEq] at hi
      rw [hm] at hi
      dsimp only at hi
      split at hi
      · cases hi
      · rename_i hcond
        exact hcond (staleGate_true_of_noInd hm0 hind)
    · cases hi

/-- Outside flow a live register sits at a non-negative column: it is the innermost marked
    slot, and marked slots never sit on the sentinel. -/
lemma reg_col_nonneg {s : ScannerState} (h : Sound s) (h0 : s.flowLevel = 0)
    (hl : s.explicitKeyLine ≠ none) : 0 ≤ s.explicitKeyCol := by
  have hreg := h.reg h0
  cases hekl : s.explicitKeyLine with
  | none => exact absurd hekl hl
  | some l =>
    rw [hekl] at hreg
    obtain ⟨i, -, hi, hc⟩ := innermost_some_mem _ _ l _ hreg.symm
    obtain ⟨m, hm, hm0⟩ := h.slots.2 i l hi
    rw [← hc, hm]; exact hm0

/-- The hook at a column-0 content landing (no `-`/`:` indicator under the cursor): a live
    register has a non-negative column, so the hook fires and `closeStale` empties every level. -/
lemma hook_col0_dead {t : ScannerState} {c : Char} (hs : SlotsOk t) (hnf : t.inFlow = false)
    (hpeek : t.peek? = some c) (hcol : t.col = 0)
    (hekc : t.explicitKeyLine ≠ none → 0 ≤ t.explicitKeyCol)
    (hind : PendingKeys.indicatorAt c (t.peekAt? 1) = false) :
    (closeStaleExplicitKey t).explicitKeyLine = none := by
  have hc0 : ((t.col : Nat) : Int) = 0 := by rw [hcol]; rfl
  unfold closeStaleExplicitKey
  rw [hnf, hpeek]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rcases hekl : t.explicitKeyLine with _ | l
  · simpa using hekl
  · have h0 : 0 ≤ t.explicitKeyCol := hekc (by rw [hekl]; simp)
    dsimp only
    split
    · show (PendingKeys.innermost (t.closeStaleAt c).indentColumns
        (t.closeStaleAt c).pendingKeys).1 = none
      have hpk : (t.closeStaleAt c).pendingKeys =
          PendingKeys.closeStale t.indentColumns t.pendingKeys 0 c (t.peekAt? 1) := by
        rw [← hc0]; rfl
      have hcols : (t.closeStaleAt c).indentColumns = t.indentColumns := rfl
      rw [hpk, hcols]
      exact innermost_closeStale_col0 _ _ hs.2 hind
    · rename_i hcond
      exfalso; apply hcond
      rw [hc0]; exact staleGate_true_of_noInd h0 hind

/-- **A column-0 content landing kills the register** (items 348–349).  Outside flow,
    preprocessing that lands on column 0 under content — no `-`/`:` indicator — leaves
    `explicitKeyLine = none`: the hook closes every marked level. -/
lemma preprocess_col0_dead {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess s = .ok (some (s', c))) (h : Sound s)
    (hnf : s.inFlow = false) (hcol : s'.col = 0)
    (hind : PendingKeys.indicatorAt c (s'.peekAt? 1) = false) :
    s'.explicitKeyLine = none := by
  have h0 : s.flowLevel = 0 := by simp [ScannerState.inFlow] at hnf; omega
  unfold scanNextToken_preprocess at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  split at hok
  · contradiction
  · rename_i s_skip h_skip
    have hind_skip := L4YAML.Proofs.PreprocessIndentStable.skipToContent_preserves_indents s s_skip h_skip
    have hfl_skip := L4YAML.Proofs.ScannerCorrectness.skipToContent_preserves_flowLevel s s_skip h_skip
    have hS : Sound s_skip := Sound.of_eq h (skipToContent_preserves_pendingKeys s s_skip h_skip)
      hind_skip hfl_skip
      (L4YAML.Proofs.ExplicitKeyCoupling.skipToContent_preserves_explicitKeyLine s s_skip h_skip)
      (L4YAML.Proofs.ExplicitKeyCoupling.skipToContent_preserves_explicitKeyCol s s_skip h_skip)
      (L4YAML.Proofs.ScannerEkStack.skipToContent_preserves_explicitKeyStack s s_skip h_skip)
    have h0' : s_skip.flowLevel = 0 := hfl_skip.trans h0
    have hekc_skip : s_skip.explicitKeyLine ≠ none → 0 ≤ s_skip.explicitKeyCol :=
      reg_col_nonneg hS h0'
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · rename_i cpk hpeek
            simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            rw [closeStaleExplicitKey_col] at hcol
            rw [closeStaleExplicitKey_peek] at hpeek
            rw [closeStaleExplicitKey_peekAt?] at hind
            refine hook_col0_dead ?_ ?_ hpeek hcol ?_ hind
            · exact SlotsOk.of_eq (unwindIndents_slots _ _ hS.slots)
                (saveSimpleKey_preserves_pendingKeys _)
                (L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_preserves_indents _)
            · simp [ScannerState.inFlow, L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_flowLevel, h0']
            · intro hl
              simp only [L4YAML.Proofs.ExplicitKeyCoupling.saveSimpleKey_preserves_explicitKeyLine,
                L4YAML.Proofs.ExplicitKeyCoupling.unwindIndents_preserves_explicitKeyLine] at hl
              simp only [L4YAML.Proofs.ExplicitKeyCoupling.saveSimpleKey_preserves_explicitKeyCol,
                L4YAML.Proofs.ExplicitKeyCoupling.unwindIndents_preserves_explicitKeyCol]
              exact hekc_skip hl
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · rename_i cpk hpeek
            simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            rw [closeStaleExplicitKey_col] at hcol
            rw [closeStaleExplicitKey_peek] at hpeek
            rw [closeStaleExplicitKey_peekAt?] at hind
            refine hook_col0_dead ?_ ?_ hpeek hcol ?_ hind
            · exact SlotsOk.of_eq hS.slots (saveSimpleKey_preserves_pendingKeys _)
                (L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_preserves_indents _)
            · simp [ScannerState.inFlow, h0']
            · intro hl
              rw [L4YAML.Proofs.ExplicitKeyCoupling.saveSimpleKey_preserves_explicitKeyLine] at hl
              rw [L4YAML.Proofs.ExplicitKeyCoupling.saveSimpleKey_preserves_explicitKeyCol]
              exact hekc_skip hl

/-! ## §4  The dispatchers -/

/-! ### Directives never touch the register (twins of the `pendingKeys` proofs) -/

lemma skipToEndOfLineLoop_explicitKeyLine (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ _ ih =>
    unfold skipToEndOfLineLoop
    split
    · split
      · rfl
      · rw [ih]; exact L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyLine s
    · rfl

lemma skipToEndOfLine_explicitKeyLine (s : ScannerState) :
    (skipToEndOfLine s).explicitKeyLine = s.explicitKeyLine := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_explicitKeyLine s _

lemma collectDirectiveNameLoop_explicitKeyLine (s : ScannerState) (name : String)
    (fuel : Nat) : (collectDirectiveNameLoop s name fuel).snd.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s name with
  | zero => unfold collectDirectiveNameLoop; rfl
  | succ _ ih =>
    unfold collectDirectiveNameLoop; split
    · split
      · rw [ih]; exact L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyLine s
      · rfl
    · rfl

lemma collectVersionMajorLoop_explicitKeyLine (s : ScannerState) (major : String)
    (fuel : Nat) : (collectVersionMajorLoop s major fuel).snd.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s major with
  | zero => unfold collectVersionMajorLoop; rfl
  | succ _ ih =>
    unfold collectVersionMajorLoop; split
    · exact L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyLine s
    · split
      · rw [ih]; exact L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyLine s
      · rfl
    · rfl

lemma collectVersionMinorLoop_explicitKeyLine (s : ScannerState) (minor : String)
    (fuel : Nat) : (collectVersionMinorLoop s minor fuel).snd.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s minor with
  | zero => unfold collectVersionMinorLoop; rfl
  | succ _ ih =>
    unfold collectVersionMinorLoop; split
    · split
      · rw [ih]; exact L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyLine s
      · rfl
    · rfl

lemma collectTagPrefixLoop_explicitKeyLine (s : ScannerState) (pfx : String)
    (fuel : Nat) : (collectTagPrefixLoop s pfx fuel).snd.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s pfx with
  | zero => unfold collectTagPrefixLoop; rfl
  | succ _ ih =>
    unfold collectTagPrefixLoop; split
    · split
      · rw [ih]; exact L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyLine s
      · rfl
    · rfl

lemma collectTagHandleDirectiveLoop_explicitKeyLine (s : ScannerState) (handle : String)
    (fuel : Nat) : (collectTagHandleDirectiveLoop s handle fuel).snd.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s handle with
  | zero => unfold collectTagHandleDirectiveLoop; rfl
  | succ _ ih =>
    unfold collectTagHandleDirectiveLoop; split
    · split
      · rw [ih]; exact L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyLine s
      · rfl
    · rfl

lemma scanDirective_explicitKeyLine {s s' : ScannerState}
    (h : scanDirective s = .ok s') : s'.explicitKeyLine = s.explicitKeyLine := by
  unfold scanDirective at h
  split at h
  · contradiction
  · simp only [] at h
    split at h
    · split at h
      · rename_i s_inner h_inner
        have h_eq := Except.ok.inj h; subst h_eq
        rw [skipToEndOfLine_explicitKeyLine]
        unfold scanYamlDirective at h_inner
        simp only [bind, Except.bind] at h_inner
        split at h_inner <;> try contradiction
        repeat (any_goals (split at h_inner))
        all_goals (try contradiction)
        all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
        all_goals (try simp [L4YAML.Proofs.ExplicitKeyCoupling.emitAt_preserves_explicitKeyLine, L4YAML.Proofs.ExplicitKeyCoupling.skipWhitespace_preserves_explicitKeyLine,
              collectVersionMinorLoop_explicitKeyLine,
              collectVersionMajorLoop_explicitKeyLine])
        all_goals (rw [collectDirectiveNameLoop_explicitKeyLine,
                       L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyLine])
      · contradiction
    · split at h
      · split at h
        · rename_i s_inner h_inner
          have h_eq := Except.ok.inj h; subst h_eq
          rw [skipToEndOfLine_explicitKeyLine]
          unfold scanTagDirective at h_inner
          dsimp only [] at h_inner
          simp only [bind, Except.bind] at h_inner
          split at h_inner
          · contradiction  -- [89]: a malformed `%TAG` handle is refused
          split at h_inner <;> try (split at h_inner <;> try contradiction)
          all_goals (try contradiction)
          all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
          all_goals simp [L4YAML.Proofs.ExplicitKeyCoupling.emitAt_preserves_explicitKeyLine, collectTagPrefixLoop_explicitKeyLine,
                L4YAML.Proofs.ExplicitKeyCoupling.skipWhitespace_preserves_explicitKeyLine,
                collectTagHandleDirectiveLoop_explicitKeyLine,
                collectDirectiveNameLoop_explicitKeyLine,
                L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyLine]
        · contradiction
      · simp only [Except.ok.injEq] at h; subst h
        simp [skipToEndOfLine_explicitKeyLine, L4YAML.Proofs.ExplicitKeyCoupling.skipWhitespace_preserves_explicitKeyLine,
              collectDirectiveNameLoop_explicitKeyLine,
              L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyLine]

lemma skipToEndOfLineLoop_explicitKeyCol (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).explicitKeyCol = s.explicitKeyCol := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ _ ih =>
    unfold skipToEndOfLineLoop
    split
    · split
      · rfl
      · rw [ih]; exact L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyCol s
    · rfl

lemma skipToEndOfLine_explicitKeyCol (s : ScannerState) :
    (skipToEndOfLine s).explicitKeyCol = s.explicitKeyCol := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_explicitKeyCol s _

lemma collectDirectiveNameLoop_explicitKeyCol (s : ScannerState) (name : String)
    (fuel : Nat) : (collectDirectiveNameLoop s name fuel).snd.explicitKeyCol = s.explicitKeyCol := by
  induction fuel generalizing s name with
  | zero => unfold collectDirectiveNameLoop; rfl
  | succ _ ih =>
    unfold collectDirectiveNameLoop; split
    · split
      · rw [ih]; exact L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyCol s
      · rfl
    · rfl

lemma collectVersionMajorLoop_explicitKeyCol (s : ScannerState) (major : String)
    (fuel : Nat) : (collectVersionMajorLoop s major fuel).snd.explicitKeyCol = s.explicitKeyCol := by
  induction fuel generalizing s major with
  | zero => unfold collectVersionMajorLoop; rfl
  | succ _ ih =>
    unfold collectVersionMajorLoop; split
    · exact L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyCol s
    · split
      · rw [ih]; exact L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyCol s
      · rfl
    · rfl

lemma collectVersionMinorLoop_explicitKeyCol (s : ScannerState) (minor : String)
    (fuel : Nat) : (collectVersionMinorLoop s minor fuel).snd.explicitKeyCol = s.explicitKeyCol := by
  induction fuel generalizing s minor with
  | zero => unfold collectVersionMinorLoop; rfl
  | succ _ ih =>
    unfold collectVersionMinorLoop; split
    · split
      · rw [ih]; exact L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyCol s
      · rfl
    · rfl

lemma collectTagPrefixLoop_explicitKeyCol (s : ScannerState) (pfx : String)
    (fuel : Nat) : (collectTagPrefixLoop s pfx fuel).snd.explicitKeyCol = s.explicitKeyCol := by
  induction fuel generalizing s pfx with
  | zero => unfold collectTagPrefixLoop; rfl
  | succ _ ih =>
    unfold collectTagPrefixLoop; split
    · split
      · rw [ih]; exact L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyCol s
      · rfl
    · rfl

lemma collectTagHandleDirectiveLoop_explicitKeyCol (s : ScannerState) (handle : String)
    (fuel : Nat) : (collectTagHandleDirectiveLoop s handle fuel).snd.explicitKeyCol = s.explicitKeyCol := by
  induction fuel generalizing s handle with
  | zero => unfold collectTagHandleDirectiveLoop; rfl
  | succ _ ih =>
    unfold collectTagHandleDirectiveLoop; split
    · split
      · rw [ih]; exact L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyCol s
      · rfl
    · rfl

lemma scanDirective_explicitKeyCol {s s' : ScannerState}
    (h : scanDirective s = .ok s') : s'.explicitKeyCol = s.explicitKeyCol := by
  unfold scanDirective at h
  split at h
  · contradiction
  · simp only [] at h
    split at h
    · split at h
      · rename_i s_inner h_inner
        have h_eq := Except.ok.inj h; subst h_eq
        rw [skipToEndOfLine_explicitKeyCol]
        unfold scanYamlDirective at h_inner
        simp only [bind, Except.bind] at h_inner
        split at h_inner <;> try contradiction
        repeat (any_goals (split at h_inner))
        all_goals (try contradiction)
        all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
        all_goals (try simp [L4YAML.Proofs.ExplicitKeyCoupling.emitAt_preserves_explicitKeyCol, L4YAML.Proofs.ExplicitKeyCoupling.skipWhitespace_preserves_explicitKeyCol,
              collectVersionMinorLoop_explicitKeyCol,
              collectVersionMajorLoop_explicitKeyCol])
        all_goals (rw [collectDirectiveNameLoop_explicitKeyCol,
                       L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyCol])
      · contradiction
    · split at h
      · split at h
        · rename_i s_inner h_inner
          have h_eq := Except.ok.inj h; subst h_eq
          rw [skipToEndOfLine_explicitKeyCol]
          unfold scanTagDirective at h_inner
          dsimp only [] at h_inner
          simp only [bind, Except.bind] at h_inner
          split at h_inner
          · contradiction  -- [89]: a malformed `%TAG` handle is refused
          split at h_inner <;> try (split at h_inner <;> try contradiction)
          all_goals (try contradiction)
          all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
          all_goals simp [L4YAML.Proofs.ExplicitKeyCoupling.emitAt_preserves_explicitKeyCol, collectTagPrefixLoop_explicitKeyCol,
                L4YAML.Proofs.ExplicitKeyCoupling.skipWhitespace_preserves_explicitKeyCol,
                collectTagHandleDirectiveLoop_explicitKeyCol,
                collectDirectiveNameLoop_explicitKeyCol,
                L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyCol]
        · contradiction
      · simp only [Except.ok.injEq] at h; subst h
        simp [skipToEndOfLine_explicitKeyCol, L4YAML.Proofs.ExplicitKeyCoupling.skipWhitespace_preserves_explicitKeyCol,
              collectDirectiveNameLoop_explicitKeyCol,
              L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyCol]

/-- Content dispatch keeps the slots in both contexts (the `PendingKeysStable`
    twin is stated in flow only; this is the block-and-flow statement, mirroring
    `IndentStackBase.dispatchContent_preserves_indents`). -/
lemma dispatchContent_pendingKeys {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchContent s c = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  split at hok
  · split at hok
    · simp at hok
    generalize h_fn : scanAnchorOrAlias s true = result at hok
    cases result with
    | error e => simp at hok
    | ok s_a =>
      simp only [Except.ok.injEq] at hok; subst hok; dsimp only []
      exact scanAnchorOrAlias_preserves_pendingKeys h_fn
  · split at hok
    · split at hok
      · simp at hok
      split at hok
      · simp at hok
      · replace hok := aliasArm_scan_ok hok
        generalize h_fn : scanAnchorOrAlias s false = result at hok
        cases result with
        | error e => simp at hok
        | ok s_a =>
          simp only [Except.ok.injEq] at hok; subst hok
          exact scanAnchorOrAlias_preserves_pendingKeys h_fn
    · split at hok
      · split at hok
        · simp at hok
        generalize h_fn : scanTag s = result at hok
        cases result with
        | error e => simp at hok
        | ok s_t =>
          simp only [Except.ok.injEq] at hok; subst hok
          exact scanTag_preserves_pendingKeys h_fn
      · repeat (any_goals (split at hok))
        any_goals contradiction
        all_goals (try simp only [Except.ok.injEq] at *)
        all_goals (try contradiction)
        all_goals (try subst_vars)
        all_goals (try dsimp only [])
        all_goals first
          | exact scanBlockScalar_preserves_pendingKeys (by assumption)
          | exact scanDoubleQuoted_preserves_pendingKeys _ _ (by assumption)
          | exact scanSingleQuoted_preserves_pendingKeys (by assumption)
          | exact scanPlainScalar_preserves_pendingKeys (by assumption)
          | (simp_all; done)

lemma flowLevel_pos_of_ne {s : ScannerState} (h : ¬ (s.flowLevel == 0) = true) :
    0 < s.flowLevel := by
  simp at h; omega

lemma dispatchStructural_sound {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchStructural s c = .ok (some s')) (h : Sound s)
    (hm : Mono s) (hbase : SentinelBase s) : Sound s' := by
  unfold scanNextToken_dispatchStructural at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  repeat (any_goals (split at hok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanDocumentStart_sound s h
        (by rcases Nat.eq_zero_or_pos s.flowLevel with h0 | hp
            · exact h0
            · exfalso; simp_all [ScannerState.inFlow]) hm hbase
    | exact scanDocumentEnd_sound (by assumption) h
        (by rcases Nat.eq_zero_or_pos s.flowLevel with h0 | hp
            · exact h0
            · exfalso; simp_all [ScannerState.inFlow]) hm hbase
    | exact Sound.of_eq h (scanDirective_preserves_pendingKeys (by assumption))
        (L4YAML.Proofs.IndentStackBase.scanDirective_preserves_indents (by assumption))
        (L4YAML.Proofs.ScannerCorrectness.scanDirective_preserves_flowLevel _ _ (by assumption))
        (scanDirective_explicitKeyLine (by assumption))
        (scanDirective_explicitKeyCol (by assumption))
        (L4YAML.Proofs.ScannerEkStack.scanDirective_preserves_explicitKeyStack _ _ (by assumption))

lemma dispatchFlowIndicators_sound {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) (h : Sound s) : Sound s' := by
  unfold scanNextToken_dispatchFlowIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (try (simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok))
  all_goals first
    | exact scanFlowSequenceStart_sound s h
    | exact scanFlowMappingStart_sound s h
    | exact scanFlowSequenceEnd_sound s h (flowLevel_pos_of_ne (by assumption))
    | exact scanFlowMappingEnd_sound s h (flowLevel_pos_of_ne (by assumption))
    | exact scanFlowEntry_sound (by assumption) h (flowLevel_pos_of_ne (by assumption))
    | simp_all

/-- The block indicators.  `hcol` is the floor `scanKey` marks its level
    against — item 338's STARVED premise (see `PreprocessFloor`). -/
lemma dispatchBlockIndicators_sound {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) (h : Sound s)
    (hbase : SentinelBase s) (hcol : s.inFlow = false → s.currentIndent ≤ (s.col : Int)) :
    Sound s' := by
  by_cases hf : s.inFlow = true
  · have hpos : 0 < s.flowLevel := by simp [ScannerState.inFlow] at hf; exact hf
    exact Sound.of_eq_inFlow h hpos (dispatchBlockIndicators_preserves_pendingKeys hf hok)
      (L4YAML.Proofs.FlowIndentStable.dispatchBlockIndicators_preserves_indents hf hok)
      (L4YAML.Proofs.ScannerCorrectness.dispatchBlockIndicators_preserves_flowLevel s c s' hok)
      (L4YAML.Proofs.ScannerEkStack.dispatchBlockIndicators_preserves_explicitKeyStack s c s' hok)
  · have hnf : s.inFlow = false := by simpa using hf
    unfold scanNextToken_dispatchBlockIndicators at hok
    simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
    repeat (any_goals (split at hok))
    any_goals contradiction
    all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
    any_goals contradiction
    all_goals (try subst_vars)
    all_goals first
      | exact scanBlockEntry_sound hnf (by assumption) h
      | exact scanKey_sound (by assumption) h.slots h.base h.stack hbase hcol
      | exact scanValue_sound (by assumption) h

lemma dispatchContent_sound {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchContent s c = .ok s') (h : Sound s) : Sound s' :=
  Sound.of_eq h (dispatchContent_pendingKeys hok)
    (L4YAML.Proofs.IndentStackBase.dispatchContent_preserves_indents hok)
    (L4YAML.Proofs.ScannerCorrectness.dispatchContent_preserves_flowLevel s c s' hok)
    (L4YAML.Proofs.ExplicitKeyCoupling.dispatchContent_preserves_explicitKeyLine s c s' hok)
    (L4YAML.Proofs.ExplicitKeyCoupling.dispatchContent_preserves_explicitKeyCol s c s' hok)
    (L4YAML.Proofs.ScannerEkStack.dispatchContent_preserves_explicitKeyStack s c s' hok)

/-! ## §5  The step and the seed -/

/-- **STARVED premise (item 338).**  After preprocess, outside flow, the cursor
    is at or right of the current indent — the floor `scanKey` marks its level
    against when it does not push one.  The unwind supplies it when it runs
    (`IndentStackCover.unwindIndents_top_le`); when no indent check was pending
    it is a fact about the cursor the carrier does not yet hold.  Probe p3 holds
    it after every preprocess on 18 inputs; its carrier (`ColFloor`:
    `inFlow = false → needIndentCheck = false → currentIndent ≤ col`) is the
    follow-up item, and `StreamAccum` cannot thread `Sound` before it lands. -/
def PreprocessFloor (s : ScannerState) : Prop :=
  ∀ (sp : ScannerState) (c : Char), scanNextToken_preprocess s = .ok (some (sp, c)) →
    sp.inFlow = false → sp.currentIndent ≤ (sp.col : Int)

/-- **The step keeps the register honest.** -/
lemma scanNextToken_sound {s s' : ScannerState}
    (hok : scanNextToken s = .ok (some s')) (h : Sound s) (hm : Mono s) (hbase : SentinelBase s)
    (hfloor : PreprocessFloor s) : Sound s' := by
  unfold scanNextToken at hok
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at hok
  split at hok
  · cases hok
  · split at hok
    · simp at hok
    · rename_i sp c h_pre
      have h_ps : Sound sp := preprocess_sound h_pre h hm
      have h_pb : SentinelBase sp := L4YAML.Proofs.IndentStackBase.preprocess_base h_pre hbase
      have h_pm : Mono sp := L4YAML.Proofs.IndentStackMono.preprocess_mono h_pre hm
      have h_pc : sp.inFlow = false → sp.currentIndent ≤ (sp.col : Int) := hfloor sp c h_pre
      split at hok
      · cases hok
      split at hok
      · cases hok
      split at hok
      · cases hok
      · split at hok
        · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
          exact dispatchStructural_sound ‹_› h_ps h_pm h_pb
        · split at hok
          · cases hok
          split at hok
          · cases hok
          · rcases h_ad : sp.allowDirectives with _ | _
            <;> simp only [h_ad, Bool.false_eq_true, ↓reduceIte] at hok
            · generalize h_fi : scanNextToken_dispatchFlowIndicators sp c = fi at hok
              cases fi with
              | error => cases hok
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                  exact dispatchFlowIndicators_sound h_fi h_ps
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact dispatchBlockIndicators_sound h_bi h_ps h_pb h_pc
                    | none =>
                      generalize h_av : scanNextToken_checkAdjacentValue sp c = av at hok
                      cases av with
                      | error => cases hok
                      | ok _ =>
                      generalize h_dc : scanNextToken_dispatchContent sp c = dc at hok
                      cases dc with
                      | error => cases hok
                      | ok s_dc =>
                        simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                        exact dispatchContent_sound h_dc h_ps
            · generalize h_sp2 :
                (({ sp with allowDirectives := false, documentEverStarted := true }
                  : ScannerState)) = sp2 at hok
              have h_ps2 : Sound sp2 := by
                rw [← h_sp2]; exact Sound.of_eq h_ps rfl rfl rfl rfl rfl rfl
              have h_pb2 : SentinelBase sp2 := by rw [← h_sp2]; exact h_pb
              have h_pc2 : sp2.inFlow = false → sp2.currentIndent ≤ (sp2.col : Int) := by
                rw [← h_sp2]; exact h_pc
              generalize h_fi : scanNextToken_dispatchFlowIndicators sp2 c = fi at hok
              cases fi with
              | error => cases hok
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                  exact dispatchFlowIndicators_sound h_fi h_ps2
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp2 c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact dispatchBlockIndicators_sound h_bi h_ps2 h_pb2 h_pc2
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
                        exact dispatchContent_sound h_dc h_ps2

/-! ### The seed -/

lemma mk'_sound (input : String) : Sound (ScannerState.mk' input) := by
  refine ⟨⟨rfl, ?_⟩, ?_, ?_, rfl⟩
  · intro i l hi
    rcases i with _ | i
    · simp [ScannerState.mk'] at hi
    · simp [ScannerState.mk'] at hi
  · intro _
    show ((none : Option Nat), (-1 : Int)) = PendingKeys.innermost _ _
    rw [innermost_eq_go]; rfl
  · intro h; simp [ScannerState.mk'] at h

end L4YAML.Proofs.PendingKeySound

end Blanket
