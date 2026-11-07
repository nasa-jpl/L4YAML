/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.DocStartLive
public import L4YAML.Proofs.Scanner.FlowSync
public import L4YAML.Proofs.Scanner.ColFloor

@[expose] public section Blanket

/-! # The `Shape` loop invariant (capstone 7.7, stream S3, obligation (β2b))

    `DocStartLive` states the scanner target at the list level (`Shape` on the
    raw token list).  This module carries `Shape (vals s)` over `scanNextToken`
    and `scanLoop` with the seven-clause carrier `LiveInv`:

    * `head`  — `vals[0] = .streamStart`;
    * `shape` — `Shape (vals s)`;
    * `deep`  — a non-negative `currentIndent` means the last real token is not a
      boundary (`.streamStart`/`.documentEnd`);
    * `flow`  — an open flow collection means the same;
    * `fresh` — after a boundary the indent is negative and the flow level `0`;
    * `slot`  — a possible simple key sits after a non-boundary, or in block
      context where `rollIndent` will insert `blockMappingStart` before it
      (`currentIndent < key.col`) or where the key is still to be overwritten
      (`simpleKeyAllowed`; after preprocessing this arm is gone: `StrongSlot`);
    * `stack` — a stacked possible key sits after a non-boundary, or is the
      outermost (`j = 0`) with `currentIndent < key.col`.

    Priority 94 (Tests/AdversarialInstantiation.lean) instantiates every clause on
    971 reached states before these proofs; the `simpleKeyAllowed` arm of `slot`
    (36 states, `- a` right after `scanBlockEntry`) and the `j = 0` arm of `stack`
    (222 states, `[a]: b`) are load-bearing there.  `FlowSync` (β2a) supplies the
    flow-stack synchrony the step lemmas need. -/

namespace L4YAML.Proofs.DocStartLiveInv

open L4YAML L4YAML.Scanner
open L4YAML.Proofs.DirectiveRuns
open L4YAML.Proofs.DocStartLive
open L4YAML.Proofs.FlowSync
open L4YAML L4YAML.Scanner
open L4YAML.Proofs.ScannerCorrectness L4YAML.Proofs.ScannerCorrectness.ScanHelpers
open L4YAML.Proofs.FlowAdjacency
open L4YAML.Proofs.ScannerDirectivesPresent L4YAML.Proofs.ScannerAllowDirectives
open L4YAML.Proofs.PreprocessIndentStable L4YAML.Proofs.IndentStackBase
open L4YAML.Proofs.CloseStaleExplicitKey L4YAML.Proofs.EntryBoundaryLayout
open L4YAML.Proofs.IndentStackBase L4YAML.Proofs.ColFloor L4YAML.Proofs.FlowIndentStable
open L4YAML.Proofs.ScannerFlowCollection

/-- The slot condition on a saved simple key (clause `slot`/`stack` body): the token before
    the slot is not a boundary, or (block context) `rollIndent` will insert `blockMappingStart`
    first (`ci < key.col`), or the key is the stale one a `-` leaves behind — `simpleKeyAllowed`
    is still up, so the next preprocessing `saveSimpleKey` overwrites it. -/
def SlotOK (L : List YamlToken) (fl : Nat) (ci : Int) (al : Bool) (k : SimpleKeyState) : Prop :=
  Bnd (lastReal (L.take k.tokenIndex)) = false ∨
    (fl = 0 ∧ (ci < (k.pos.col : Int) ∨ al = true))

/-- No boundary token from index `idx` on. -/
def TailOK (L : List YamlToken) (idx : Nat) : Prop := ∀ t ∈ L.drop idx, Bnd (some t) = false

structure LiveInv (s : ScannerState) : Prop where
  head : (vals s)[0]? = some .streamStart
  shape : Shape (vals s)
  deep : 0 ≤ s.currentIndent → Bnd (lastReal (vals s)) = false
  flow : 0 < s.flowLevel → Bnd (lastReal (vals s)) = false
  fresh : Bnd (lastReal (vals s)) = true → s.currentIndent < 0 ∧ s.flowLevel = 0
  slot : s.simpleKey.possible = true →
    SlotOK (vals s) s.flowLevel s.currentIndent s.simpleKeyAllowed s.simpleKey
  stack : ∀ j (h : j < s.simpleKeyStack.size), s.simpleKeyStack[j].possible = true →
    Bnd (lastReal ((vals s).take s.simpleKeyStack[j].tokenIndex)) = false ∨
      (j = 0 ∧ s.currentIndent < (s.simpleKeyStack[j].pos.col : Int))
  tail : s.simpleKey.possible = true → TailOK (vals s) s.simpleKey.tokenIndex
  stackTail : ∀ j (h : j < s.simpleKeyStack.size), s.simpleKeyStack[j].possible = true →
    TailOK (vals s) s.simpleKeyStack[j].tokenIndex

lemma TailOK_append (L M : List YamlToken) (idx : Nat) (hk : idx ≤ L.length)
    (h : TailOK L idx) (hM : ∀ t ∈ M, Bnd (some t) = false) : TailOK (L ++ M) idx := by
  intro t ht
  rw [List.drop_append_of_le_length hk] at ht
  rcases List.mem_append.1 ht with ht | ht
  · exact h t ht
  · exact hM t ht

/-- Key transport: a still-possible key is the old one. -/
def KeyTr (s s' : ScannerState) : Prop :=
  s'.simpleKey.possible = true → s.simpleKey.possible = true ∧
    s'.simpleKey.tokenIndex = s.simpleKey.tokenIndex ∧ s'.simpleKey.pos = s.simpleKey.pos

lemma KeyTr.ofEq {s s' : ScannerState} (h : s'.simpleKey = s.simpleKey) : KeyTr s s' :=
  fun hp => ⟨by rw [← h]; exact hp, by rw [h], by rw [h]⟩

lemma SlotOK_key_congr (L : List YamlToken) (fl : Nat) (ci : Int) (al : Bool) (k k' : SimpleKeyState)
    (hidx : k'.tokenIndex = k.tokenIndex) (hpos : k'.pos = k.pos) (h : SlotOK L fl ci al k) :
    SlotOK L fl ci al k' := by
  unfold SlotOK at h ⊢; rw [hidx, hpos]; exact h
lemma KeyTr.ofCleared {s s' : ScannerState} (h : s'.simpleKey.possible = false) : KeyTr s s' :=
  fun hp => by rw [h] at hp; cases hp

lemma take_append_of_le' (L M : List YamlToken) (k : Nat) (hk : k ≤ L.length) :
    (L ++ M).take k = L.take k := by
  rw [List.take_append_of_le_length hk]

lemma SlotOK_append (L M : List YamlToken) (fl : Nat) (ci : Int) (al : Bool) (k : SimpleKeyState)
    (hk : k.tokenIndex ≤ L.length) (h : SlotOK L fl ci al k) : SlotOK (L ++ M) fl ci al k := by
  unfold SlotOK at h ⊢
  rw [take_append_of_le' _ _ _ hk]
  exact h

/-- The `al` arm transfers when either the slot is in fact live or the flag stays up. -/
lemma SlotOK_transfer (L : List YamlToken) (fl : Nat) (ci : Int) (al al' : Bool) (k : SimpleKeyState)
    (hal : al = true → fl = 0 → ¬ ci < (k.pos.col : Int) →
      Bnd (lastReal (L.take k.tokenIndex)) = false ∨ al' = true)
    (h : SlotOK L fl ci al k) : SlotOK L fl ci al' k := by
  unfold SlotOK at h ⊢
  rcases h with h | ⟨h1, h2 | h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, Or.inl h2⟩
  · by_cases hlt : ci < (k.pos.col : Int)
    · exact Or.inr ⟨h1, Or.inl hlt⟩
    · rcases hal h2 h1 hlt with h3 | h3
      · exact Or.inl h3
      · exact Or.inr ⟨h1, Or.inr h3⟩

/-- Appending live tokens (and placeholders) with the indent / flow / key state
    untouched keeps the invariant (`simpleKeyAllowed` may only go up). -/
lemma LiveInv.ext (s s' : ScannerState) (hI : LiveInv s) (M : List YamlToken)
    (hv : vals s' = vals s ++ M) (hM : LiveExt M)
    (hind : s'.indents = s.indents) (hfl : s'.flowLevel = s.flowLevel)
    (hal : s'.simpleKey.possible = true → s.simpleKeyAllowed = true → s.flowLevel = 0 →
      ¬ s.currentIndent < (s.simpleKey.pos.col : Int) →
      Bnd (lastReal ((vals s).take s.simpleKey.tokenIndex)) = false ∨ s'.simpleKeyAllowed = true)
    (hMb : s'.simpleKey.possible = true ∨
      (∃ j, ∃ h : j < s'.simpleKeyStack.size, s'.simpleKeyStack[j].possible = true) →
      ∀ t ∈ M, Bnd (some t) = false)
    (hkey : KeyTr s s') (hst : s'.simpleKeyStack = s.simpleKeyStack)
    (hkl : s.simpleKey.possible = true → s.simpleKey.tokenIndex ≤ (vals s).length)
    (hsl : ∀ j (h : j < s.simpleKeyStack.size), s.simpleKeyStack[j].possible = true →
      s.simpleKeyStack[j].tokenIndex ≤ (vals s).length) : LiveInv s' where
  head := by
    rw [hv]
    have hh := hI.head
    have : 0 < (vals s).length := by
      cases h : vals s with
      | nil => rw [h] at hh; simp at hh
      | cons => simp
    rw [List.getElem?_append_left this]; exact hh
  shape := by rw [hv]; exact Shape_append_live _ _ hI.shape hM
  deep := by
    intro hd
    cases hb : Bnd (lastReal (vals s')) with
    | false => rfl
    | true =>
      have hb' : Bnd (lastReal (vals s ++ M)) = true := by rw [← hv]; exact hb
      rw [Bnd_lastReal_append_live _ _ hM hb'] at hb'
      have := hI.deep (by simpa [ScannerState.currentIndent, hind] using hd)
      rw [this] at hb'; cases hb'
  flow := by
    intro hf
    cases hb : Bnd (lastReal (vals s')) with
    | false => rfl
    | true =>
      have hb' : Bnd (lastReal (vals s ++ M)) = true := by rw [← hv]; exact hb
      rw [Bnd_lastReal_append_live _ _ hM hb'] at hb'
      have := hI.flow (by rw [← hfl]; exact hf)
      rw [this] at hb'; cases hb'
  fresh := by
    intro hb
    have hb' : Bnd (lastReal (vals s ++ M)) = true := by rw [← hv]; exact hb
    rw [Bnd_lastReal_append_live _ _ hM hb'] at hb'
    have := hI.fresh hb'
    simpa [ScannerState.currentIndent, hind, hfl] using this
  slot := by
    intro hp
    obtain ⟨hp0, hidx, hpos⟩ := hkey hp
    have hal' := hal hp
    rw [hv, hfl]
    have : s'.currentIndent = s.currentIndent := by simp [ScannerState.currentIndent, hind]
    rw [this]
    refine SlotOK_key_congr _ _ _ _ _ _ hidx hpos
      (SlotOK_transfer _ _ _ _ _ _ ?_ (SlotOK_append _ _ _ _ _ _ (hkl hp0) (hI.slot hp0)))
    intro hb h0 hlt
    rw [take_append_of_le' _ _ _ (hkl hp0)]
    exact hal' hb h0 hlt
  stack := by
    intro j hj hp
    simp only [hst] at hj hp ⊢
    have : s'.currentIndent = s.currentIndent := by simp [ScannerState.currentIndent, hind]
    rw [hv, this, take_append_of_le' _ _ _ (hsl j hj hp)]
    exact hI.stack j hj hp
  tail := by
    intro hp
    obtain ⟨hp0, hidx, _⟩ := hkey hp
    have hM' := hMb (Or.inl hp)
    rw [hv, hidx]
    exact TailOK_append _ _ _ (hkl hp0) (hI.tail hp0) hM'
  stackTail := by
    intro j hj hp
    have hM' := hMb (Or.inr ⟨j, hj, hp⟩)
    simp only [hst] at hj hp ⊢
    rw [hv]
    exact TailOK_append _ _ _ (hsl j hj hp) (hI.stackTail j hj hp) hM'

/-- Field transport: same tokens, indents, flow level and key stack; `simpleKeyAllowed` may
    only go up; the key is unchanged or cleared. -/
lemma LiveInv.ofFields (s t : ScannerState) (ht : t.tokens = s.tokens)
    (hind : t.indents = s.indents) (hfl : t.flowLevel = s.flowLevel)
    (hal : t.simpleKey.possible = true → s.simpleKeyAllowed = true → s.flowLevel = 0 →
      ¬ s.currentIndent < (s.simpleKey.pos.col : Int) →
      Bnd (lastReal ((vals s).take s.simpleKey.tokenIndex)) = false ∨ t.simpleKeyAllowed = true)
    (hkey : KeyTr s t) (hst : t.simpleKeyStack = s.simpleKeyStack) (hI : LiveInv s) : LiveInv t := by
  have hv : vals t = vals s := by simp [vals, ht]
  have hci : t.currentIndent = s.currentIndent := by simp [ScannerState.currentIndent, hind]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv]; exact hI.head
  · rw [hv]; exact hI.shape
  · rw [hv, hci]; exact hI.deep
  · rw [hv, hfl]; exact hI.flow
  · rw [hv, hci, hfl]; exact hI.fresh
  · intro hp
    obtain ⟨hp0, hidx, hpos⟩ := hkey hp
    have hal' := hal hp
    rw [hv, hfl, hci]
    exact SlotOK_key_congr _ _ _ _ _ _ hidx hpos (SlotOK_transfer _ _ _ _ _ _ hal' (hI.slot hp0))
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    rw [hv, hci]
    exact hI.stack j hj hp
  · intro hp
    obtain ⟨hp0, hidx, _⟩ := hkey hp
    rw [hv, hidx]; exact hI.tail hp0
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    rw [hv]; exact hI.stackTail j hj hp

lemma LiveInv_skipToContent (s s1 : ScannerState) (h : skipToContent s = .ok s1)
    (hI : LiveInv s) : LiveInv s1 :=
  LiveInv.ofFields s s1 (skipToContent_preserves_tokens s s1 h)
    (skipToContent_preserves_indents s s1 h) (skipToContent_preserves_flowLevel s s1 h)
    (fun _ hb _ _ => Or.inr (FlowSync.skipToContent_simpleKeyAllowed_mono s s1 hb h))
    (KeyTr.ofEq (skipToContent_preserves_simpleKey s s1 h))
    (skipToContent_preserves_simpleKeyStack s s1 h) hI

lemma LiveInv_needIndentCheck (s : ScannerState) (hI : LiveInv s) :
    LiveInv { s with needIndentCheck := false } :=
  LiveInv.ofFields s _ rfl rfl rfl (fun _ h _ _ => Or.inr h) (KeyTr.ofEq rfl) rfl hI

/-! ### The unwind: `blockEnd`s after a non-boundary -/

lemma lastReal_append_blockEnds (L M : List YamlToken) (hall : ∀ t ∈ M, t = .blockEnd) :
    lastReal (L ++ .blockEnd :: M) = some .blockEnd := by
  induction M generalizing L with
  | nil => simp [lastReal_snoc, nonPh]
  | cons t M ih =>
    have ht : t = .blockEnd := hall t (by simp)
    subst ht
    rw [show L ++ .blockEnd :: .blockEnd :: M = (L ++ [.blockEnd]) ++ .blockEnd :: M by simp]
    exact ih _ (fun u hu => hall u (by simp [hu]))

lemma Shape_append_blockEnds (L M : List YamlToken) (hL : Shape L) (hb : Bnd (lastReal L) = false)
    (hall : ∀ t ∈ M, t = .blockEnd) : Shape (L ++ M) := by
  induction M generalizing L with
  | nil => simpa using hL
  | cons t M ih =>
    have ht : t = .blockEnd := hall t (by simp)
    subst ht
    rw [show L ++ .blockEnd :: M = (L ++ [.blockEnd]) ++ M by simp]
    refine ih _ (Shape_snoc _ _ hL (fun _ _ => hb)) ?_ (fun u hu => hall u (by simp [hu]))
    simp [lastReal_snoc, nonPh, Bnd]

/-- One pop of the unwind. -/
def popStep (s : ScannerState) : ScannerState :=
  { s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop, pendingKeys := (s.emit .blockEnd).pendingKeys.pop }

lemma popStep_indents_size (s : ScannerState) : (popStep s).indents.size = s.indents.size - 1 := by
  simp [popStep, ScannerState.emit]

/-- What one `unwindIndentsLoop` run does, with enough fuel: nothing, or it emits
    `blockEnd`s, popped past the target column (or down to the base). -/
lemma unwindIndentsLoop_result : ∀ (fuel : Nat) (s : ScannerState) (col : Int),
    s.indents.size ≤ fuel →
    (unwindIndentsLoop s col fuel = s ∧ (s.currentIndent ≤ col ∨ s.indents.size ≤ 1)) ∨
    (∃ M, vals (unwindIndentsLoop s col fuel) = vals s ++ (.blockEnd :: M) ∧
      (∀ t ∈ M, t = .blockEnd) ∧ 1 < s.indents.size ∧ col < s.currentIndent ∧
      ((unwindIndentsLoop s col fuel).currentIndent ≤ col ∨
        (unwindIndentsLoop s col fuel).indents.size ≤ 1)) := by
  intro fuel
  induction fuel with
  | zero => intro s col hf; exact Or.inl ⟨by simp [unwindIndentsLoop], Or.inr (by omega)⟩
  | succ f ih =>
    intro s col hf
    unfold unwindIndentsLoop
    split
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      have hsz' : (popStep s).indents.size ≤ f := by rw [popStep_indents_size]; omega
      have key := ih (popStep s) col hsz'
      simp only [popStep] at key
      rcases key with ⟨heq, hfin⟩ | ⟨M, hM, hall, _, _, hfin⟩
      · refine Or.inr ⟨[], ?_, by simp, hcond.2, hcond.1, ?_⟩
        · rw [heq]; simp [vals, toks, ScannerState.emit]
        · rw [heq]; simpa [ScannerState.emit, ScannerState.currentIndent] using hfin
      · refine Or.inr ⟨.blockEnd :: M, ?_, ?_, hcond.2, hcond.1, hfin⟩
        · rw [hM]; simp [vals, toks, ScannerState.emit]
        · intro t ht; simp at ht; rcases ht with rfl | ht; rfl; exact hall t ht
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hcond
      refine Or.inl ⟨rfl, ?_⟩
      by_cases h : col < s.currentIndent
      · exact Or.inr (by have := hcond h; omega)
      · exact Or.inl (by omega)

lemma LiveInv_unwindIndents (s : ScannerState) (col : Int) (hc : -1 ≤ col)
    (hB : SentinelBase s) (hA : AllKeysValid s) (hI : LiveInv s) :
    LiveInv (unwindIndents s col) := by
  unfold unwindIndents
  rcases unwindIndentsLoop_result s.indents.size s col (Nat.le_refl _) with ⟨heq, _⟩ | ⟨M, hM, hall, hsz, hcol, hfin⟩
  · rw [heq]; exact hI
  · generalize hr : unwindIndentsLoop s col s.indents.size = r at hM hfin
    have hlr : lastReal (vals r) = some .blockEnd := by rw [hM]; exact lastReal_append_blockEnds _ _ hall
    have hBr : Bnd (lastReal (vals r)) = false := by rw [hlr]; rfl
    have hfl : r.flowLevel = s.flowLevel := by rw [← hr]; exact unwindIndentsLoop_preserves_flowLevel _ _ _
    have hk : r.simpleKey = s.simpleKey := by rw [← hr]; exact unwindIndentsLoop_preserves_simpleKey _ _ _
    have hst : r.simpleKeyStack = s.simpleKeyStack := by
      rw [← hr]; exact unwindIndentsLoop_preserves_simpleKeyStack _ _ _
    have hBr' : SentinelBase r := by rw [← hr]; exact unwindIndentsLoop_base _ _ _ hB
    have hci : r.currentIndent ≤ col := by
      rcases hfin with h | h
      · exact h
      · rw [hBr'.currentIndent_of_size_le_one h]; omega
    have hall' : ∀ t ∈ (.blockEnd :: M), t = .blockEnd := by
      intro t ht; simp at ht; rcases ht with rfl | ht; rfl; exact hall t ht
    have hMb : ∀ t ∈ (.blockEnd :: M), Bnd (some t) = false := by
      intro t ht; rw [hall' t ht]; rfl
    refine ⟨?_, ?_, fun _ => hBr, fun _ => hBr, (fun h => by rw [hBr] at h; cases h), ?_, ?_, ?_, ?_⟩
    · rw [hM]
      have hh := hI.head
      have : 0 < (vals s).length := by
        cases h : vals s with
        | nil => rw [h] at hh; simp at hh
        | cons => simp
      rw [List.getElem?_append_left this]; exact hh
    · rw [hM]; exact Shape_append_blockEnds _ _ hI.shape (hI.deep (by omega)) hall'
    · intro hp
      rw [hk] at hp ⊢
      have hlen : s.simpleKey.tokenIndex ≤ (vals s).length := by
        have := keyLen_of_AllKeysValid s hA hp; omega
      rcases hI.slot hp with h | ⟨h0, h1⟩
      · left; rw [hM, take_append_of_le' _ _ _ hlen]; exact h
      · right; refine ⟨by rw [hfl]; exact h0, ?_⟩
        rcases h1 with h1 | h1
        · exact Or.inl (by omega)
        · right; rw [← hr]; rw [unwindIndentsLoop_preserves_simpleKeyAllowed]; exact h1
    · intro j hj hp
      simp only [hst] at hj hp ⊢
      rcases hI.stack j hj hp with h | ⟨hj0, hlt⟩
      · left; rw [hM, take_append_of_le' _ _ _ (by have := stackLen_of_AllKeysValid s hA j hj hp; omega)]
        exact h
      · right; exact ⟨hj0, by omega⟩
    · intro hp
      rw [hk] at hp ⊢
      rw [hM]
      exact TailOK_append _ _ _ (by have := keyLen_of_AllKeysValid s hA hp; omega) (hI.tail hp) hMb
    · intro j hj hp
      simp only [hst] at hj hp ⊢
      rw [hM]
      exact TailOK_append _ _ _ (by have := stackLen_of_AllKeysValid s hA j hj hp; omega)
        (hI.stackTail j hj hp) hMb

/-! ### `saveSimpleKey`: the new slot sits after the last real token -/

/-- Two placeholders are pushed and the key is re-saved at the old size; everything the
    invariant reads is otherwise unchanged. -/
lemma LiveInv.ofSave (s t : ScannerState) (ph : Positioned YamlToken) (hph : ph.val = .placeholder)
    (ht : t.tokens = (s.tokens.push ph).push ph)
    (hind : t.indents = s.indents) (hfl : t.flowLevel = s.flowLevel)
    (hst : t.simpleKeyStack = s.simpleKeyStack)
    (hki : t.simpleKey.tokenIndex = s.tokens.size)
    (hA : AllKeysValid s) (hI : LiveInv s) : LiveInv t := by
  have hv : vals t = vals s ++ [.placeholder, .placeholder] := by
    simp [vals, toks, ht, hph]
  have hci : t.currentIndent = s.currentIndent := by simp [ScannerState.currentIndent, hind]
  have hphs : ∀ u ∈ ([.placeholder, .placeholder] : List YamlToken), nonPh u = false := by
    intro u hu; simp at hu; rcases hu with rfl | rfl <;> rfl
  have hlr : lastReal (vals s ++ [.placeholder, .placeholder]) = lastReal (vals s) :=
    lastReal_append_ph _ _ hphs
  have hMb : ∀ u ∈ ([.placeholder, .placeholder] : List YamlToken), Bnd (some u) = false := by
    intro u hu; simp at hu; rcases hu with rfl | rfl <;> rfl
  have hlen : (vals s).length = s.tokens.size := vals_length s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv]
    have hh := hI.head
    have : 0 < (vals s).length := by
      cases h : vals s with
      | nil => rw [h] at hh; simp at hh
      | cons => simp
    rw [List.getElem?_append_left this]; exact hh
  · rw [hv]; exact Shape_append_ph _ _ hI.shape hphs
  · rw [hv, hlr, hci]; exact hI.deep
  · rw [hv, hlr, hfl]; exact hI.flow
  · rw [hv, hlr, hci, hfl]; exact hI.fresh
  · intro _
    unfold SlotOK
    rw [hv, hki, hfl, hci, take_append_of_le' _ _ _ (by omega),
      show (vals s).take s.tokens.size = vals s from List.take_of_length_le (by omega)]
    cases hb : Bnd (lastReal (vals s)) with
    | false => exact Or.inl rfl
    | true =>
      obtain ⟨hci0, hfl0⟩ := hI.fresh hb
      exact Or.inr ⟨hfl0, Or.inl (by omega)⟩
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    rw [hv, hci, take_append_of_le' _ _ _ (by have := stackLen_of_AllKeysValid s hA j hj hp; omega)]
    exact hI.stack j hj hp
  · intro _
    rw [hv, hki]
    intro u hu
    rw [List.drop_append_of_le_length (by omega),
      show (vals s).drop s.tokens.size = [] from List.drop_of_length_le (by omega)] at hu
    exact hMb u hu
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    rw [hv]
    exact TailOK_append _ _ _ (by have := stackLen_of_AllKeysValid s hA j hj hp; omega)
      (hI.stackTail j hj hp) hMb

lemma LiveInv_saveSimpleKey (s : ScannerState) (hA : AllKeysValid s) (hI : LiveInv s) :
    LiveInv (saveSimpleKey s) := by
  unfold saveSimpleKey
  split
  · exact hI
  · split
    · exact LiveInv.ofSave s _ _ rfl rfl rfl rfl rfl rfl hA hI
    · exact hI

lemma LiveInv_closeStaleExplicitKey (s : ScannerState) (hI : LiveInv s) :
    LiveInv (closeStaleExplicitKey s) := by
  rcases closeStaleExplicitKey_cases s with h | ⟨c, _, h⟩
  · rw [h]; exact hI
  · rw [h]
    exact LiveInv.ofFields s _ rfl rfl rfl (fun _ h _ _ => Or.inr h) (KeyTr.ofEq rfl) rfl hI

/-! ### Preprocessing -/

lemma LiveInv_preprocess (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c)))
    (hB : SentinelBase s) (hA : AllKeysValid s) (hI : LiveInv s) : LiveInv s1 := by
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have hI1 := LiveInv_skipToContent s s_skip h_skip hI
    have hA1 := skipToContent_preserves_AllKeysValid s s_skip h_skip hA
    have hB1 : SentinelBase s_skip := hB.of_indents_eq (skipToContent_preserves_indents s s_skip h_skip)
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            have hI2 := LiveInv_needIndentCheck _
              (LiveInv_unwindIndents s_skip s_skip.col (by omega) hB1 hA1 hI1)
            have hA2 : AllKeysValid { unwindIndents s_skip s_skip.col with needIndentCheck := false } :=
              unwindIndents_preserves_AllKeysValid s_skip _ hA1
            exact LiveInv_closeStaleExplicitKey _ (LiveInv_saveSimpleKey _ hA2 hI2)
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            exact LiveInv_closeStaleExplicitKey _ (LiveInv_saveSimpleKey _ hA1 hI1)

/-! ### Document markers -/

lemma scanDocumentStart_indents (s : ScannerState) :
    (scanDocumentStart s).indents = (unwindIndents s (-1)).indents := by
  unfold scanDocumentStart
  simp [L4YAML.Proofs.IndentStackBase.advanceN_preserves_indents,
    L4YAML.Proofs.PreprocessIndentStable.emit_indents]

lemma LiveInv_scanDocumentStart (s : ScannerState) (hB : SentinelBase s) (hA : AllKeysValid s)
    (hI : LiveInv s) : LiveInv (scanDocumentStart s) := by
  obtain ⟨hv, _, _, hk, hst⟩ := scanDocumentStart_fields s
  have hIu := LiveInv_unwindIndents s (-1) (by omega) hB hA hI
  have hAu := unwindIndents_preserves_AllKeysValid s (-1) hA
  have hind := scanDocumentStart_indents s
  refine LiveInv.ext _ _ hIu [.documentStart] hv ?_ hind ?_ ?_ ?_ (KeyTr.ofCleared hk) ?_ ?_ ?_
  · intro t ht _; simp at ht; subst ht; exact ⟨rfl, rfl⟩
  · rw [scanDocumentStart_preserves_flowLevel, unwindIndents_preserves_flowLevel]
  · intro hp; rw [hk] at hp; cases hp
  · intro _ t ht; simp at ht; subst ht; rfl
  · rw [hst, unwindIndents_preserves_simpleKeyStack]
  · intro hp; have := keyLen_of_AllKeysValid _ hAu hp; omega
  · intro j hj hp; have := stackLen_of_AllKeysValid _ hAu j hj hp; omega

lemma LiveInv_scanDocumentEnd (s s' : ScannerState) (h : scanDocumentEnd s = .ok s')
    (hfl0 : s.flowLevel = 0) (hF : FlowSync s) (hB : SentinelBase s) (hA : AllKeysValid s)
    (hI : LiveInv s) : LiveInv s' := by
  obtain ⟨hv, _, _, hind, hk, hst⟩ := scanDocumentEnd_fields s s' h
  have hIu := LiveInv_unwindIndents s (-1) (by omega) hB hA hI
  have hci := scanDocumentEnd_currentIndent_neg h hB
  have hfl : s'.flowLevel = 0 := by rw [scanDocumentEnd_preserves_flowLevel s s' h]; exact hfl0
  have hsz : s'.simpleKeyStack.size = 0 := by
    rw [hst]; have := hF.1; have := hF.2; omega
  refine ⟨?_, ?_, ?_, ?_, fun _ => ⟨hci, hfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [hv]
    have hh := hIu.head
    have : 0 < (vals (unwindIndents s (-1))).length := by
      cases h0 : vals (unwindIndents s (-1)) with
      | nil => rw [h0] at hh; simp at hh
      | cons => simp
    rw [List.getElem?_append_left this]; exact hh
  · rw [hv]; exact Shape_snoc _ _ hIu.shape (fun h _ => absurd h (by decide))
  · intro h0; exfalso; omega
  · intro h0; rw [hfl] at h0; exact absurd h0 (by decide)
  · intro hp; rw [hk] at hp; cases hp
  · intro j hj; exfalso; rw [hsz] at hj; exact absurd hj (by omega)
  · intro hp; rw [hk] at hp; cases hp
  · intro j hj; exfalso; rw [hsz] at hj; exact absurd hj (by omega)

/-! ### Directives and the structural dispatcher -/

lemma scanDirective_allowDirectives_true (s s' : ScannerState) (h : scanDirective s = .ok s') :
    s.allowDirectives = true := by
  unfold scanDirective at h
  split at h
  · contradiction
  · rename_i hn; simpa using hn

lemma LiveInv_scanDirective (s s' : ScannerState) (h : scanDirective s = .ok s')
    (hD : DirInv s) (hB : SentinelBase s) (hA : AllKeysValid s) (hI : LiveInv s) : LiveInv s' := by
  obtain ⟨hv, _, _⟩ := scanDirective_fields s s' h
  have hq : Quiet s := hD.quiet (scanDirective_allowDirectives_true s s' h)
  have hal : s'.simpleKey.possible = true → s.simpleKeyAllowed = true → s.flowLevel = 0 →
      ¬ s.currentIndent < (s.simpleKey.pos.col : Int) →
      Bnd (lastReal ((vals s).take s.simpleKey.tokenIndex)) = false ∨ s'.simpleKeyAllowed = true := by
    intro _ _ _ hnlt
    exfalso
    rcases hq with hq | hq
    · rw [hB.currentIndent_of_size_le_one hq] at hnlt; omega
    · omega
  have hkl : s.simpleKey.possible = true → s.simpleKey.tokenIndex ≤ (vals s).length := by
    intro hp; have := keyLen_of_AllKeysValid s hA hp; omega
  have hsl : ∀ j (hj : j < s.simpleKeyStack.size), s.simpleKeyStack[j].possible = true →
      s.simpleKeyStack[j].tokenIndex ≤ (vals s).length := by
    intro j hj hp; have := stackLen_of_AllKeysValid s hA j hj hp; omega
  rcases hv with hv | ⟨d, hv, hd⟩
  · exact LiveInv.ext s s' hI [] (by rw [hv]; simp) (fun t ht => by simp at ht)
      (scanDirective_preserves_indents h) (scanDirective_preserves_flowLevel s s' h) hal
      (fun _ t ht => by simp at ht) (KeyTr.ofEq (scanDirective_preserves_simpleKey s s' h))
      (scanDirective_preserves_simpleKeyStack s s' h) hkl hsl
  · refine LiveInv.ext s s' hI [d] hv ?_
      (scanDirective_preserves_indents h) (scanDirective_preserves_flowLevel s s' h) hal
      ?_ (KeyTr.ofEq (scanDirective_preserves_simpleKey s s' h))
      (scanDirective_preserves_simpleKeyStack s s' h) hkl hsl
    · intro t ht _
      have htd : t = d := by simpa using ht
      rw [htd]
      cases d <;> simp [isDirTok] at hd <;> exact ⟨rfl, rfl⟩
    · intro _ t ht
      have htd : t = d := by simpa using ht
      rw [htd]
      cases d <;> simp [isDirTok] at hd <;> rfl

lemma flowLevel_zero_of_marker_guard (s : ScannerState)
    (h1 : ¬ (s.col == 0 && s.inFlow && (atDocumentStart s || atDocumentEnd s)) = true)
    (h2 : (s.col == 0 && atDocumentEnd s) = true) : s.flowLevel = 0 := by
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h1 h2
  cases hfl : s.flowLevel with
  | zero => rfl
  | succ n =>
    exfalso
    apply h1
    refine ⟨⟨h2.1, ?_⟩, Or.inr h2.2⟩
    simp [ScannerState.inFlow, hfl]

lemma LiveInv_dispatchStructural (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s'))
    (hD : DirInv s) (hF : FlowSync s) (hB : SentinelBase s) (hA : AllKeysValid s)
    (hI : LiveInv s) : LiveInv s' := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact LiveInv_scanDocumentStart s hB hA hI
    | exact LiveInv_scanDocumentEnd _ _ (by assumption)
        (flowLevel_zero_of_marker_guard s (by assumption) (by assumption)) hF hB hA hI
    | exact LiveInv_scanDirective _ _ (by assumption) hD hB hA hI

/-! ### After preprocessing the slot is in strong form (no stale arm) -/

/-- The slot condition without the stale arm. -/
def StrongSlot (s : ScannerState) : Prop :=
  s.simpleKey.possible = true →
    SlotOK (vals s) s.flowLevel s.currentIndent false s.simpleKey

lemma StrongSlot.of_al_false (s : ScannerState) (hI : LiveInv s)
    (hb : s.simpleKeyAllowed = false) : StrongSlot s := by
  intro hp
  have := hI.slot hp
  rwa [hb] at this

/-- After preprocessing the `al` arm is never needed. -/
lemma hal_of_StrongSlot {s s' : ScannerState} (hkey : KeyTr s s') (hS : StrongSlot s) :
    s'.simpleKey.possible = true → s.simpleKeyAllowed = true → s.flowLevel = 0 →
      ¬ s.currentIndent < (s.simpleKey.pos.col : Int) →
      Bnd (lastReal ((vals s).take s.simpleKey.tokenIndex)) = false ∨ s'.simpleKeyAllowed = true := by
  intro hp _ _ hnlt
  obtain ⟨hp0, _, _⟩ := hkey hp
  rcases hS hp0 with h | ⟨_, h | h⟩
  · exact Or.inl h
  · exact absurd h hnlt
  · cases h

lemma StrongSlot_saveSimpleKey (s : ScannerState) (hI : LiveInv s) : StrongSlot (saveSimpleKey s) := by
  unfold saveSimpleKey
  split
  · rename_i hin
    simp only [Bool.and_eq_true] at hin
    intro hp
    have hfl : 0 < s.flowLevel := by
      have := hin.1; unfold ScannerState.inFlow at this; simpa using this
    rcases hI.slot hp with h | ⟨h0, _⟩
    · exact Or.inl h
    · omega
  · split
    · generalize hph0 : (⟨s.currentPos, .placeholder, s.currentPos⟩ : Positioned YamlToken) = ph
      intro _
      unfold SlotOK
      have hv : vals ({ s with tokens := (s.tokens.push ph).push ph } : ScannerState) = vals s ++ [.placeholder, .placeholder] := by
        simp [vals, toks, ← hph0]
      have hlen : (vals s).length = s.tokens.size := vals_length s
      show Bnd (lastReal ((vals { s with tokens := (s.tokens.push ph).push ph }).take s.tokens.size)) = false ∨
        (s.flowLevel = 0 ∧ (s.currentIndent < (s.currentPos.col : Int) ∨ false = true))
      rw [hv, take_append_of_le' _ _ _ (by omega),
        show (vals s).take s.tokens.size = vals s from List.take_of_length_le (by omega)]
      cases hb : Bnd (lastReal (vals s)) with
      | false => exact Or.inl rfl
      | true =>
        obtain ⟨hci0, hfl0⟩ := hI.fresh hb
        exact Or.inr ⟨hfl0, Or.inl (by omega)⟩
    · rename_i hal
      exact StrongSlot.of_al_false s hI (by simpa using hal)

lemma StrongSlot_closeStaleExplicitKey (s : ScannerState) (hS : StrongSlot s) :
    StrongSlot (closeStaleExplicitKey s) := by
  rcases closeStaleExplicitKey_cases s with h | ⟨c, _, h⟩
  · rw [h]; exact hS
  · rw [h]; exact fun hp => hS hp

lemma StrongSlot_preprocess (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c)))
    (hB : SentinelBase s) (hA : AllKeysValid s) (hI : LiveInv s) : StrongSlot s1 := by
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have hI1 := LiveInv_skipToContent s s_skip h_skip hI
    have hA1 := skipToContent_preserves_AllKeysValid s s_skip h_skip hA
    have hB1 : SentinelBase s_skip := hB.of_indents_eq (skipToContent_preserves_indents s s_skip h_skip)
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            have hI2 := LiveInv_needIndentCheck _
              (LiveInv_unwindIndents s_skip s_skip.col (by omega) hB1 hA1 hI1)
            exact StrongSlot_closeStaleExplicitKey _ (StrongSlot_saveSimpleKey _ hI2)
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            exact StrongSlot_closeStaleExplicitKey _ (StrongSlot_saveSimpleKey _ hI1)

/-! ### Flow indicators -/

lemma head_append {s : ScannerState} (hI : LiveInv s) (M : List YamlToken) :
    (vals s ++ M)[0]? = some .streamStart := by
  have hh := hI.head
  have : 0 < (vals s).length := by
    cases h : vals s with
    | nil => rw [h] at hh; simp at hh
    | cons => simp
  rw [List.getElem?_append_left this]; exact hh

/-- A live, non-boundary token is appended, the key cleared and pushed. -/
lemma LiveInv.flowStart (s s' : ScannerState) (t : YamlToken) (hlive : liveTok t = true)
    (hnp : nonPh t = true) (hbnd : Bnd (some t) = false)
    (hv : vals s' = vals s ++ [t]) (hk : s'.simpleKey.possible = false)
    (hst : s'.simpleKeyStack = s.simpleKeyStack.push s.simpleKey) (hind : s'.indents = s.indents)
    (hF : FlowSync s) (hS : StrongSlot s) (hA : AllKeysValid s) (hI : LiveInv s) : LiveInv s' := by
  have hci : s'.currentIndent = s.currentIndent := by simp [ScannerState.currentIndent, hind]
  have hlr : lastReal (vals s') = some t := by rw [hv, lastReal_snoc, hnp]; rfl
  have hBr : Bnd (lastReal (vals s')) = false := by rw [hlr]; exact hbnd
  have hMb : ∀ u ∈ [t], Bnd (some u) = false := by
    intro u hu; simp at hu; subst hu; exact hbnd
  refine ⟨by rw [hv]; exact head_append hI _, ?_, fun _ => hBr, fun _ => hBr,
    (fun h => by rw [hBr] at h; cases h), (fun hp => by rw [hk] at hp; cases hp), ?_,
    (fun hp => by rw [hk] at hp; cases hp), ?_⟩
  · rw [hv]; exact Shape_snoc _ _ hI.shape (fun h => by rw [hlive] at h; cases h)
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    rw [hv, hci]
    by_cases hlt : j < s.simpleKeyStack.size
    · simp only [Array.getElem_push, hlt, dite_true] at hp ⊢
      rw [take_append_of_le' _ _ _ (by have := stackLen_of_AllKeysValid s hA j hlt hp; omega)]
      exact hI.stack j hlt hp
    · simp only [Array.getElem_push, hlt, dite_false] at hp ⊢
      rw [take_append_of_le' _ _ _ (by have := keyLen_of_AllKeysValid s hA hp; omega)]
      rcases hS hp with h | ⟨h0, h1 | h1⟩
      · exact Or.inl h
      · right
        refine ⟨?_, h1⟩
        have := hF.1; have := hF.2
        simp at hj; omega
      · cases h1
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    rw [hv]
    by_cases hlt : j < s.simpleKeyStack.size
    · simp only [Array.getElem_push, hlt, dite_true] at hp ⊢
      exact TailOK_append _ _ _ (by have := stackLen_of_AllKeysValid s hA j hlt hp; omega)
        (hI.stackTail j hlt hp) hMb
    · simp only [Array.getElem_push, hlt, dite_false] at hp ⊢
      exact TailOK_append _ _ _ (by have := keyLen_of_AllKeysValid s hA hp; omega) (hI.tail hp) hMb

/-- A non-boundary token is appended after a non-boundary, the key popped back. -/
lemma LiveInv.flowEnd (s s' : ScannerState) (t : YamlToken)
    (hnp : nonPh t = true) (hbnd : Bnd (some t) = false)
    (hv : vals s' = vals s ++ [t]) (hpos : 0 < s.flowLevel) (hfl : s'.flowLevel = s.flowLevel - 1)
    (hk : s'.simpleKey = s.simpleKeyStack.back?.getD {})
    (hst : s'.simpleKeyStack = s.simpleKeyStack.pop) (hind : s'.indents = s.indents)
    (hF : FlowSync s) (hA : AllKeysValid s) (hI : LiveInv s) : LiveInv s' := by
  have hci : s'.currentIndent = s.currentIndent := by simp [ScannerState.currentIndent, hind]
  have hlr : lastReal (vals s') = some t := by rw [hv, lastReal_snoc, hnp]; rfl
  have hBr : Bnd (lastReal (vals s')) = false := by rw [hlr]; exact hbnd
  have hMb : ∀ u ∈ [t], Bnd (some u) = false := by
    intro u hu; simp at hu; subst hu; exact hbnd
  have hsz : s.simpleKeyStack.size = s.flowLevel := by have := hF.1; have := hF.2; omega
  refine ⟨by rw [hv]; exact head_append hI _, ?_, fun _ => hBr, fun _ => hBr,
    (fun h => by rw [hBr] at h; cases h), ?_, ?_, ?_, ?_⟩
  · rw [hv]; exact Shape_snoc _ _ hI.shape (fun _ _ => hI.flow hpos)
  · intro hp
    rw [hk] at hp ⊢
    cases hb : s.simpleKeyStack.back? with
    | none => rw [hb] at hp; simp at hp
    | some k =>
      rw [hb] at hp
      simp only [Option.getD_some] at hp ⊢
      simp only [Array.back?, Array.getElem?_eq_some_iff] at hb
      obtain ⟨hlt, hk'⟩ := hb
      rw [← hk'] at hp ⊢
      unfold SlotOK
      rw [hv, hci, hfl, take_append_of_le' _ _ _ (by have := stackLen_of_AllKeysValid s hA _ hlt hp; omega)]
      rcases hI.stack _ hlt hp with h | ⟨h0, h1⟩
      · exact Or.inl h
      · right; refine ⟨by omega, Or.inl h1⟩
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    have hj' : j < s.simpleKeyStack.size := by simp at hj; omega
    simp only [Array.getElem_pop] at hp ⊢
    rw [hv, hci, take_append_of_le' _ _ _ (by have := stackLen_of_AllKeysValid s hA j hj' hp; omega)]
    exact hI.stack j hj' hp
  · intro hp
    rw [hk] at hp ⊢
    cases hb : s.simpleKeyStack.back? with
    | none => rw [hb] at hp; simp at hp
    | some k =>
      rw [hb] at hp
      simp only [Option.getD_some] at hp ⊢
      simp only [Array.back?, Array.getElem?_eq_some_iff] at hb
      obtain ⟨hlt, hk'⟩ := hb
      rw [← hk'] at hp ⊢
      rw [hv]
      exact TailOK_append _ _ _ (by have := stackLen_of_AllKeysValid s hA _ hlt hp; omega)
        (hI.stackTail _ hlt hp) hMb
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    have hj' : j < s.simpleKeyStack.size := by simp at hj; omega
    simp only [Array.getElem_pop] at hp ⊢
    rw [hv]
    exact TailOK_append _ _ _ (by have := stackLen_of_AllKeysValid s hA j hj' hp; omega)
      (hI.stackTail j hj' hp) hMb

/-- A non-boundary token appended after a non-boundary with the key cleared and the
    rest untouched. -/
lemma LiveInv.deadSnoc (s s' : ScannerState) (t : YamlToken)
    (hnp : nonPh t = true) (hbnd : Bnd (some t) = false)
    (hv : vals s' = vals s ++ [t]) (hlast : Bnd (lastReal (vals s)) = false)
    (hk : s'.simpleKey.possible = false) (hst : s'.simpleKeyStack = s.simpleKeyStack)
    (hind : s'.indents = s.indents) (hA : AllKeysValid s) (hI : LiveInv s) : LiveInv s' := by
  have hci : s'.currentIndent = s.currentIndent := by simp [ScannerState.currentIndent, hind]
  have hlr : lastReal (vals s') = some t := by rw [hv, lastReal_snoc, hnp]; rfl
  have hBr : Bnd (lastReal (vals s')) = false := by rw [hlr]; exact hbnd
  have hMb : ∀ u ∈ [t], Bnd (some u) = false := by
    intro u hu; simp at hu; subst hu; exact hbnd
  refine ⟨by rw [hv]; exact head_append hI _, ?_, fun _ => hBr, fun _ => hBr,
    (fun h => by rw [hBr] at h; cases h), (fun hp => by rw [hk] at hp; cases hp), ?_,
    (fun hp => by rw [hk] at hp; cases hp), ?_⟩
  · rw [hv]; exact Shape_snoc _ _ hI.shape (fun _ _ => hlast)
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    rw [hv, hci, take_append_of_le' _ _ _ (by have := stackLen_of_AllKeysValid s hA j hj hp; omega)]
    exact hI.stack j hj hp
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    rw [hv]
    exact TailOK_append _ _ _ (by have := stackLen_of_AllKeysValid s hA j hj hp; omega)
      (hI.stackTail j hj hp) hMb

lemma scanFlowEntry_vals (s s' : ScannerState) (h : scanFlowEntry s = .ok s') :
    vals s' = vals s ++ [.flowEntry] := by
  unfold scanFlowEntry at h
  simp only [bind, Except.bind] at h
  repeat' (split at h)
  all_goals (first
    | contradiction
    | (injection h with h_eq; subst h_eq
       simp [vals, toks, advance_preserves_tokens, ScannerState.emit]))

lemma LiveInv_dispatchFlow (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s'))
    (hF : FlowSync s) (hS : StrongSlot s) (hA : AllKeysValid s) (hI : LiveInv s) : LiveInv s' := by
  have hind := dispatchFlowIndicators_preserves_indents h
  unfold scanNextToken_dispatchFlowIndicators at h
  replace h := peel_flowAdj h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact LiveInv.flowStart s _ _ rfl rfl rfl (scanFlowSequenceStart_vals s)
      (scanFlowSequenceStart_simpleKey_cleared s) (scanFlowSequenceStart_stack_pushed s) hind hF hS hA hI
  · split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
            have hpos : 0 < s.flowLevel := by
              cases hz : s.flowLevel with
              | zero => simp_all
              | succ n => omega
            exact LiveInv.flowEnd s _ _ rfl rfl (scanFlowSequenceEnd_vals s) hpos
              (scanFlowSequenceEnd_flowLevel_pos s hpos)
              (scanFlowSequenceEnd_simpleKey_restored s) (scanFlowSequenceEnd_stack_popped s) hind hF hA hI
    · split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact LiveInv.flowStart s _ _ rfl rfl rfl (scanFlowMappingStart_vals s)
          (scanFlowMappingStart_simpleKey_cleared s) (scanFlowMappingStart_stack_pushed s) hind hF hS hA hI
      · split at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                have hpos : 0 < s.flowLevel := by
                  cases hz : s.flowLevel with
                  | zero => simp_all
                  | succ n => omega
                exact LiveInv.flowEnd s _ _ rfl rfl (scanFlowMappingEnd_vals s) hpos
                  (scanFlowMappingEnd_flowLevel_pos s hpos)
                  (scanFlowMappingEnd_simpleKey_restored s) (scanFlowMappingEnd_stack_popped s) hind hF hA hI
        · split at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · rename_i _ _ _ h_entry
                simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                have hpos : 0 < s.flowLevel := by
                  cases hz : s.flowLevel with
                  | zero => simp_all
                  | succ n => omega
                exact LiveInv.deadSnoc s _ _ rfl rfl (scanFlowEntry_vals s _ h_entry) (hI.flow hpos)
                  (scanFlowEntry_clears_simpleKey s _ h_entry)
                  (scanFlowEntry_preserves_simpleKeyStack s _ h_entry) hind hA hI
          · simp at h

/-! ### Rewriting a slot: `set` with a real non-boundary token -/

lemma snoc_ind' {P : List YamlToken → Prop} (h0 : P []) (h1 : ∀ L t, P L → P (L ++ [t])) :
    ∀ L, P L := by
  intro L
  induction h : L.length generalizing L with
  | zero => cases L with
    | nil => exact h0
    | cons => simp at h
  | succ n ih =>
    rcases List.eq_nil_or_concat L with rfl | ⟨L', t, rfl⟩
    · simp at h
    · rw [List.concat_eq_append] at h ⊢
      simp at h; exact h1 _ _ (ih _ h)

lemma lastReal_append_real (L M : List YamlToken) (hex : ∃ u ∈ M, nonPh u = true) :
    ∃ t ∈ M, nonPh t = true ∧ lastReal (L ++ M) = some t := by
  induction M using snoc_ind' generalizing L with
  | h0 => obtain ⟨u, hu, _⟩ := hex; simp at hu
  | h1 M t ih =>
    rw [← List.append_assoc, lastReal_snoc]
    cases hnt : nonPh t with
    | true => exact ⟨t, by simp, hnt, rfl⟩
    | false =>
      obtain ⟨u, hu, hnu⟩ := hex
      have hu' : u ∈ M := by
        rcases List.mem_append.1 hu with hu | hu
        · exact hu
        · simp at hu; subst hu; rw [hnt] at hnu; cases hnu
      obtain ⟨v, hv, hnv, hlv⟩ := ih L ⟨u, hu', hnu⟩
      exact ⟨v, List.mem_append_left _ hv, hnv, hlv⟩

lemma Bnd_lastReal_of_tail (L : List YamlToken) (idx : Nat) (h : TailOK L idx)
    (hex : ∃ u ∈ L.drop idx, nonPh u = true) : Bnd (lastReal L) = false := by
  obtain ⟨t, ht, _, hl⟩ := lastReal_append_real (L.take idx) (L.drop idx) hex
  rw [List.take_append_drop] at hl
  rw [hl]; exact h t ht

lemma TailOK_set (L : List YamlToken) (idx j : Nat) (t : YamlToken) (ht : Bnd (some t) = false)
    (h : TailOK L idx) : TailOK (L.set j t) idx := by
  intro u hu
  rw [List.drop_set] at hu
  split at hu
  · exact h u hu
  · rcases List.mem_or_eq_of_mem_set hu with hu | rfl
    · exact h u hu
    · exact ht

lemma Bnd_lastReal_set_false (L : List YamlToken) (j : Nat) (t : YamlToken) (hnp : nonPh t = true)
    (ht : Bnd (some t) = false) (h : Bnd (lastReal L) = false) :
    Bnd (lastReal (L.set j t)) = false := by
  induction L using snoc_ind' generalizing j with
  | h0 => simpa using h
  | h1 L a ih =>
    rw [List.set_append]
    split
    · rw [lastReal_snoc] at h ⊢
      cases hna : nonPh a with
      | true => rw [hna] at h; simpa using h
      | false => rw [hna] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢; exact ih j h
    · rename_i hge
      by_cases hj : j - L.length = 0
      · rw [hj]; simp only [List.set_cons_zero]; rw [lastReal_snoc, hnp]; simpa using ht
      · rw [List.set_eq_of_length_le (by simp; omega)]; exact h

lemma Shape_set (L : List YamlToken) (j : Nat) (t : YamlToken) (hnp : nonPh t = true)
    (ht : Bnd (some t) = false) (hL : Shape L)
    (hj : liveTok t = false → Bnd (lastReal (L.take j)) = false) : Shape (L.set j t) := by
  intro m u hm hu hdead hnpu
  rw [List.take_set]
  by_cases hmj : m = j
  · subst hmj
    rw [List.getElem?_set] at hu
    simp only [↓reduceIte] at hu
    split at hu
    · simp only [Option.some.injEq] at hu; subst hu
      rw [List.set_eq_of_length_le (by rw [List.length_take]; omega)]
      exact hj hdead
    · cases hu
  · rw [List.getElem?_set_ne (Ne.symm hmj)] at hu
    exact Bnd_lastReal_set_false _ _ _ hnp ht (hL m u hm hu hdead hnpu)

/-! ### Block indicators -/

lemma toks_setIfInBounds (a : Array (Positioned YamlToken)) (i : Nat) (x : Positioned YamlToken) :
    toks (a.setIfInBounds i x) = (toks a).set i x.val := by
  simp [toks, Array.toList_setIfInBounds, List.map_set]

/-- The invariant from its pieces when the key ends up cleared: the shape and the last real
    token are supplied, the stack clauses transported by two monotone maps. -/
lemma LiveInv.ofPieces (s s' : ScannerState) (hhead : (vals s')[0]? = some .streamStart)
    (hshape : Shape (vals s')) (hlast : Bnd (lastReal (vals s')) = false)
    (hk : s'.simpleKey.possible = false) (hst : s'.simpleKeyStack = s.simpleKeyStack)
    (hci : 0 < s.simpleKeyStack.size → s'.currentIndent = s.currentIndent)
    (hstk : ∀ j (hj : j < s.simpleKeyStack.size), s.simpleKeyStack[j].possible = true →
      Bnd (lastReal ((vals s).take s.simpleKeyStack[j].tokenIndex)) = false →
      Bnd (lastReal ((vals s').take s.simpleKeyStack[j].tokenIndex)) = false)
    (hstt : ∀ j (hj : j < s.simpleKeyStack.size), s.simpleKeyStack[j].possible = true →
      TailOK (vals s) s.simpleKeyStack[j].tokenIndex → TailOK (vals s') s.simpleKeyStack[j].tokenIndex)
    (hI : LiveInv s) : LiveInv s' := by
  refine ⟨hhead, hshape, fun _ => hlast, fun _ => hlast, (fun h => by rw [hlast] at h; cases h),
    (fun hp => by rw [hk] at hp; cases hp), ?_, (fun hp => by rw [hk] at hp; cases hp), ?_⟩
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    rcases hI.stack j hj hp with h | ⟨hj0, hlt⟩
    · exact Or.inl (hstk j hj hp h)
    · right; refine ⟨hj0, ?_⟩; rw [hci (by omega)]; exact hlt
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    exact hstt j hj hp (hI.stackTail j hj hp)

/-- Tokens appended, key cleared. -/
lemma LiveInv.clearedAppend (s s' : ScannerState) (M : List YamlToken)
    (hv : vals s' = vals s ++ M) (hMb : ∀ t ∈ M, Bnd (some t) = false)
    (hshape : Shape (vals s')) (hlast : Bnd (lastReal (vals s')) = false)
    (hk : s'.simpleKey.possible = false) (hst : s'.simpleKeyStack = s.simpleKeyStack)
    (hci : 0 < s.simpleKeyStack.size → s'.currentIndent = s.currentIndent)
    (hA : AllKeysValid s) (hI : LiveInv s) : LiveInv s' := by
  refine LiveInv.ofPieces s s' (by rw [hv]; exact head_append hI _) hshape hlast hk hst hci ?_ ?_ hI
  · intro j hj hp h
    rw [hv, take_append_of_le' _ _ _ (by have := stackLen_of_AllKeysValid s hA j hj hp; omega)]
    exact h
  · intro j hj hp h
    rw [hv]
    exact TailOK_append _ _ _ (by have := stackLen_of_AllKeysValid s hA j hj hp; omega) h hMb

lemma pushSequenceIndent_vals (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col = s) ∨
    vals (pushSequenceIndent s col) = vals s ++ [.blockSequenceStart] := by
  unfold pushSequenceIndent
  split
  · right; simp [vals, toks, ScannerState.emit]
  · left; rfl

lemma pushMappingIndent_vals (s : ScannerState) (col : Int) :
    (pushMappingIndent s col = s ∧ col ≤ s.currentIndent) ∨
    vals (pushMappingIndent s col) = vals s ++ [.blockMappingStart] := by
  unfold pushMappingIndent
  split
  · right; simp [vals, toks, ScannerState.emit]
  · left; exact ⟨rfl, by omega⟩

lemma LiveInv_scanBlockEntry (s s' : ScannerState) (h : scanBlockEntry s = .ok s')
    (hnf : s.inFlow = false) (hF : FlowSync s) (hA : AllKeysValid s) (hI : LiveInv s) : LiveInv s' := by
  have hfl0 : s.flowLevel = 0 := by
    unfold ScannerState.inFlow at hnf; simpa using hnf
  have hsz : s.simpleKeyStack.size = 0 := by have := hF.1; have := hF.2; omega
  have hv0 : vals s' = vals (pushSequenceIndent s s.col) ++ [.blockEntry] := by
    rw [← vals_emit]; show toks s'.tokens = toks _; rw [scanBlockEntry_tokens s s' h]; simp [hnf]
  have hM : ∃ M, vals s' = vals s ++ M ∧ LiveExt M ∧ ∀ t ∈ M, Bnd (some t) = false := by
    rcases pushSequenceIndent_vals s s.col with hp | hp
    · refine ⟨[.blockEntry], by rw [hv0, hp], ?_, ?_⟩
      · intro t ht _; simp at ht; subst ht; exact ⟨rfl, rfl⟩
      · intro t ht; simp at ht; subst ht; rfl
    · refine ⟨[.blockSequenceStart, .blockEntry], by rw [hv0, hp, List.append_assoc]; rfl, ?_, ?_⟩
      · intro t ht _; simp at ht; rcases ht with rfl | rfl <;> exact ⟨rfl, rfl⟩
      · intro t ht; simp at ht; rcases ht with rfl | rfl <;> rfl
  obtain ⟨M, hv, hM, hMb⟩ := hM
  have hlr : lastReal (vals s') = some .blockEntry := by rw [hv0, lastReal_snoc]; rfl
  have hBr : Bnd (lastReal (vals s')) = false := by rw [hlr]; rfl
  have hk := scanBlockEntry_preserves_simpleKey s s' h
  have hst := scanBlockEntry_preserves_simpleKeyStack s s' h
  have hfl' : s'.flowLevel = 0 := by rw [scanBlockEntry_preserves_flowLevel s s' h]; exact hfl0
  have hal' : s'.simpleKeyAllowed = true := scanBlockEntry_simpleKeyAllowed h
  refine ⟨by rw [hv]; exact head_append hI _, by rw [hv]; exact Shape_append_live _ _ hI.shape hM,
    fun _ => hBr, fun _ => hBr, (fun h => by rw [hBr] at h; cases h), ?_, ?_, ?_, ?_⟩
  · intro _; exact Or.inr ⟨hfl', Or.inr hal'⟩
  · intro j hj; exfalso; rw [hst, hsz] at hj; exact absurd hj (by omega)
  · intro hp
    rw [hk] at hp ⊢
    rw [hv]
    exact TailOK_append _ _ _ (by have := keyLen_of_AllKeysValid s hA hp; omega) (hI.tail hp) hMb
  · intro j hj; exfalso; rw [hst, hsz] at hj; exact absurd hj (by omega)

lemma LiveInv_scanKey (s s' : ScannerState) (h : scanKey s = .ok s')
    (hF : FlowSync s) (hA : AllKeysValid s) (hI : LiveInv s) : LiveInv s' := by
  have hv0 : vals s' = vals (if !s.inFlow then pushMappingIndent s s.col else s) ++ [.key] := by
    rw [← vals_emit]; show toks s'.tokens = toks _; rw [scanKey_tokens s s' h]
  have hk := scanKey_clears_simpleKey s s' h
  have hst := scanKey_preserves_simpleKeyStack s s' h
  have hsz : s.simpleKeyStack.size = s.flowLevel := by have := hF.1; have := hF.2; omega
  -- the token before the `.key` is not a boundary
  have hpre : ∃ M, vals s' = vals s ++ M ++ [.key] ∧ LiveExt M ∧ (∀ t ∈ M, Bnd (some t) = false) ∧
      Bnd (lastReal (vals s ++ M)) = false := by
    cases hin : s.inFlow with
    | true =>
      refine ⟨[], by rw [hv0]; simp [hin], fun t ht => by simp at ht, fun t ht => by simp at ht, ?_⟩
      simp only [List.append_nil]
      exact hI.flow (by unfold ScannerState.inFlow at hin; simpa using hin)
    | false =>
      rcases pushMappingIndent_vals s s.col with ⟨hp, hle⟩ | hp
      · refine ⟨[], by rw [hv0]; simp [hin, hp], fun t ht => by simp at ht, fun t ht => by simp at ht, ?_⟩
        simp only [List.append_nil]
        exact hI.deep (by omega)
      · refine ⟨[.blockMappingStart], by rw [hv0]; simp [hin, hp], ?_, ?_, ?_⟩
        · intro t ht _; simp at ht; subst ht; exact ⟨rfl, rfl⟩
        · intro t ht; simp at ht; subst ht; rfl
        · rw [lastReal_snoc]; rfl
  obtain ⟨M, hv, hM, hMb, hpre⟩ := hpre
  have hlr : lastReal (vals s') = some .key := by rw [hv, lastReal_snoc]; rfl
  refine LiveInv.clearedAppend s s' (M ++ [.key]) (by rw [hv, List.append_assoc]) ?_ ?_
    (by rw [hlr]; rfl) hk hst ?_ hA hI
  · intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · exact hMb t ht
    · simp at ht; subst ht; rfl
  · rw [hv]
    exact Shape_snoc _ _ (Shape_append_live _ _ hI.shape hM) (fun _ _ => hpre)
  · intro hpos
    have hin : s.inFlow = true := by
      unfold ScannerState.inFlow; simp; omega
    simp [ScannerState.currentIndent, scanKey_indents_of_inFlow hin h]

/-! ### `scanValue`: the retroactive key insertion -/

lemma Bnd_lastReal_take_succ (L : List YamlToken) (idx : Nat) (hT : TailOK L idx)
    (hprev : Bnd (lastReal (L.take idx)) = false ∨ ∃ u, L[idx]? = some u ∧ nonPh u = true) :
    Bnd (lastReal (L.take (idx + 1))) = false := by
  rw [List.take_add_one]
  cases hu : L[idx]? with
  | none =>
    simp only [Option.toList_none, List.append_nil]
    rcases hprev with h | ⟨u, hu', _⟩
    · exact h
    · rw [hu] at hu'; cases hu'
  | some u =>
    simp only [Option.toList_some]
    rw [lastReal_snoc]
    cases hnu : nonPh u with
    | true =>
      simp only [↓reduceIte]
      have hmem : u ∈ L.drop idx := by
        rw [List.mem_iff_getElem?]
        exact ⟨0, by rw [List.getElem?_drop]; simpa using hu⟩
      exact hT u hmem
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases hprev with h | ⟨u', hu', hnu'⟩
      · exact h
      · rw [hu] at hu'; simp only [Option.some.injEq] at hu'; subst hu'; rw [hnu] at hnu'; cases hnu'

lemma head_append' (L M : List YamlToken) (h : L[0]? = some .streamStart) :
    (L ++ M)[0]? = some .streamStart := by
  have : 0 < L.length := by
    cases hL : L with
    | nil => rw [hL] at h; simp at h
    | cons => simp
  rw [List.getElem?_append_left this]; exact h

lemma scanValueClearKey_simpleKeyAllowed (s : ScannerState) :
    (scanValueClearKey s).simpleKeyAllowed = s.simpleKeyAllowed := by
  unfold scanValueClearKey
  split <;> (try split) <;> (try split) <;> rfl

lemma scanValue_unfold (s s' : ScannerState) (h : scanValue s = .ok s') :
    scanValueValidate (scanValueClearKey s) = .ok () ∧
    vals s' = vals (scanValuePrepare (scanValueClearKey s)) ++ [.value] ∧
    s'.indents = (scanValuePrepare (scanValueClearKey s)).indents := by
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i u hval
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Except.ok.injEq] at h; subst h
  refine ⟨by cases u; exact hval, ?_, ?_⟩
  · simp [vals, toks, advance_preserves_tokens, ScannerState.emit]
  · simp [
      L4YAML.Proofs.PreprocessIndentStable.emit_indents, ScannerLoopInvariant.advance_indents]

lemma StrongSlot_of_eq {s t : ScannerState} (hS : StrongSlot s) (hv : vals t = vals s)
    (hfl : t.flowLevel = s.flowLevel) (hci : t.currentIndent = s.currentIndent)
    (hk : t.simpleKey = s.simpleKey ∨ t.simpleKey.possible = false) : StrongSlot t := by
  intro hp
  rcases hk with hk | hk
  · rw [hk] at hp ⊢; unfold SlotOK; rw [hv, hfl, hci]; exact hS hp
  · rw [hk] at hp; cases hp

/-- One rewrite of the slot pair at `idx + 1` with `.key`. -/
lemma key_set_pieces (L : List YamlToken) (idx : Nat) (hT : TailOK L idx) (hSh : Shape L)
    (hh : L[0]? = some .streamStart) (hlt : idx + 1 < L.length) (_hidx0 : idx ≠ 0)
    (hprev : Bnd (lastReal (L.take idx)) = false ∨ ∃ u, L[idx]? = some u ∧ nonPh u = true) :
    Shape (L.set (idx + 1) .key) ∧ Bnd (lastReal (L.set (idx + 1) .key)) = false ∧
    (L.set (idx + 1) .key)[0]? = some .streamStart := by
  refine ⟨Shape_set _ _ _ rfl rfl hSh (fun _ => Bnd_lastReal_take_succ _ _ hT hprev), ?_, ?_⟩
  · refine Bnd_lastReal_of_tail _ _ (TailOK_set _ _ _ _ rfl hT) ⟨.key, ?_, rfl⟩
    rw [List.mem_iff_getElem?]
    exact ⟨1, by rw [List.getElem?_drop, List.getElem?_set_self (by omega)]⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hh

/-- What `scanValuePrepare` does to the token list, for the invariant. -/
lemma prepare_pieces (s1 : ScannerState) (hval : scanValueValidate s1 = .ok ())
    (hA1 : AllKeysValid s1) (hS1 : StrongSlot s1) (hI1 : LiveInv s1) :
    Shape (vals (scanValuePrepare s1)) ∧ Bnd (lastReal (vals (scanValuePrepare s1))) = false ∧
    (vals (scanValuePrepare s1))[0]? = some .streamStart ∧
    (∀ j (hj : j < s1.simpleKeyStack.size), s1.simpleKeyStack[j].possible = true →
      Bnd (lastReal ((vals s1).take s1.simpleKeyStack[j].tokenIndex)) = false →
      Bnd (lastReal ((vals (scanValuePrepare s1)).take s1.simpleKeyStack[j].tokenIndex)) = false) ∧
    (∀ j (hj : j < s1.simpleKeyStack.size), s1.simpleKeyStack[j].possible = true →
      TailOK (vals s1) s1.simpleKeyStack[j].tokenIndex →
      TailOK (vals (scanValuePrepare s1)) s1.simpleKeyStack[j].tokenIndex) := by
  have hshape := hI1.shape
  have hhead := hI1.head
  unfold scanValuePrepare
  split
  · rename_i hp
    have hT := hI1.tail hp
    have hlt : s1.simpleKey.tokenIndex + 1 < (vals s1).length := by
      rw [vals_length]; exact (hA1.1 hp).2.1
    have hidx0 : s1.simpleKey.tokenIndex ≠ 0 := by
      intro h0
      have hmem : YamlToken.streamStart ∈ (vals s1).drop s1.simpleKey.tokenIndex := by
        rw [h0, List.drop_zero]; exact List.mem_of_getElem? hhead
      have := hT _ hmem; cases this
    split
    · split
      · -- block, the key is deeper than the current indent: `blockMappingStart` first
        rename_i hgt
        dsimp only
        simp only [vals, toks_setIfInBounds]
        have h1 : TailOK ((vals s1).set s1.simpleKey.tokenIndex .blockMappingStart) s1.simpleKey.tokenIndex :=
          TailOK_set _ _ _ _ rfl hT
        have h2 : Shape ((vals s1).set s1.simpleKey.tokenIndex .blockMappingStart) :=
          Shape_set _ _ _ rfl rfl hshape (fun h => absurd h (by decide))
        have h3 : ((vals s1).set s1.simpleKey.tokenIndex .blockMappingStart)[0]? = some .streamStart := by
          rw [List.getElem?_set_ne hidx0]; exact hhead
        have h4 : s1.simpleKey.tokenIndex + 1 < ((vals s1).set s1.simpleKey.tokenIndex .blockMappingStart).length := by
          rw [List.length_set]; exact hlt
        obtain ⟨hs2, hl2, hh2⟩ := key_set_pieces _ _ h1 h2 h3 h4 hidx0
          (Or.inr ⟨.blockMappingStart, List.getElem?_set_self (by omega), rfl⟩)
        refine ⟨hs2, hl2, hh2, ?_, ?_⟩
        · intro j hj hpj h
          rw [List.take_set, List.take_set]
          exact Bnd_lastReal_set_false _ _ _ rfl rfl (Bnd_lastReal_set_false _ _ _ rfl rfl h)
        · intro j hj hpj h
          exact TailOK_set _ _ _ _ rfl (TailOK_set _ _ _ _ rfl h)
      · -- block, the key is at or above the current indent: the slot itself is live
        rename_i hnlt
        dsimp only
        simp only [vals, toks_setIfInBounds]
        have hprev : Bnd (lastReal ((vals s1).take s1.simpleKey.tokenIndex)) = false := by
          rcases hS1 hp with h | ⟨_, h | h⟩
          · exact h
          · exact absurd h (by omega)
          · cases h
        obtain ⟨hs2, hl2, hh2⟩ := key_set_pieces _ _ hT hshape hhead hlt hidx0 (Or.inl hprev)
        refine ⟨hs2, hl2, hh2, ?_, ?_⟩
        · intro j hj hpj h
          rw [List.take_set]
          exact Bnd_lastReal_set_false _ _ _ rfl rfl h
        · intro j hj hpj h
          exact TailOK_set _ _ _ _ rfl h
    · -- flow: the slot is live
      rename_i hin
      dsimp only
      simp only [vals, toks_setIfInBounds]
      have hfl : 0 < s1.flowLevel := by
        unfold ScannerState.inFlow at hin; simp at hin; omega
      have hprev : Bnd (lastReal ((vals s1).take s1.simpleKey.tokenIndex)) = false := by
        rcases hS1 hp with h | ⟨h0, _⟩
        · exact h
        · omega
      obtain ⟨hs2, hl2, hh2⟩ := key_set_pieces _ _ hT hshape hhead hlt hidx0 (Or.inl hprev)
      refine ⟨hs2, hl2, hh2, ?_, ?_⟩
      · intro j hj hpj h
        rw [List.take_set]
        exact Bnd_lastReal_set_false _ _ _ rfl rfl h
      · intro j hj hpj h
        exact TailOK_set _ _ _ _ rfl h
  · rename_i hnp
    have hnp' : s1.simpleKey.possible = false := by simpa using hnp
    split
    · -- explicit value: the `:` sits at the mapping's indent
      rename_i hek
      refine ⟨hshape, ?_, hhead, fun _ _ _ h => h, fun _ _ _ h => h⟩
      cases hin : s1.inFlow with
      | true => exact hI1.flow (by unfold ScannerState.inFlow at hin; simpa using hin)
      | false =>
        have hcol := scanValueValidate_explicit_col hnp' hin hek hval
        exact hI1.deep (by omega)
    · split
      · rename_i hin
        have hin' : s1.inFlow = false := by simpa using hin
        rcases pushMappingIndent_vals s1 s1.col with ⟨hp, hle⟩ | hp
        · rw [hp]; exact ⟨hshape, hI1.deep (by omega), hhead, fun _ _ _ h => h, fun _ _ _ h => h⟩
        · rw [hp]
          refine ⟨Shape_append_live _ _ hshape ?_, by rw [lastReal_snoc]; rfl, head_append' _ _ hhead, ?_, ?_⟩
          · intro t ht _; simp at ht; subst ht; exact ⟨rfl, rfl⟩
          · intro j hj hpj h
            rw [take_append_of_le' _ _ _ (by have := stackLen_of_AllKeysValid s1 hA1 j hj hpj; omega)]
            exact h
          · intro j hj hpj h
            exact TailOK_append _ _ _ (by have := stackLen_of_AllKeysValid s1 hA1 j hj hpj; omega) h
              (fun t ht => by simp at ht; subst ht; rfl)
      · rename_i hin
        have hfl : 0 < s1.flowLevel := by
          unfold ScannerState.inFlow at hin; simp at hin; omega
        exact ⟨hshape, hI1.flow hfl, hhead, fun _ _ _ h => h, fun _ _ _ h => h⟩

lemma LiveInv_scanValue (s s' : ScannerState) (h : scanValue s = .ok s')
    (hF : FlowSync s) (hS : StrongSlot s) (hA : AllKeysValid s) (hI : LiveInv s) : LiveInv s' := by
  obtain ⟨hval, hv, hind⟩ := scanValue_unfold s s' h
  have ht1 := scanValueClearKey_preserves_tokens s
  have hc1 := L4YAML.Proofs.PendingKeySound.scanValueClearKey_core s
  have hst1 := scanValueClearKey_preserves_simpleKeyStack s
  have hk1 := scanValueClearKey_simpleKey s
  have hal1 := scanValueClearKey_simpleKeyAllowed s
  have hv1 : vals (scanValueClearKey s) = vals s := by simp [vals, ht1]
  have hci1 : (scanValueClearKey s).currentIndent = s.currentIndent := by
    simp [ScannerState.currentIndent, hc1.1]
  have hI1 : LiveInv (scanValueClearKey s) :=
    LiveInv.ofFields s _ ht1 hc1.1 hc1.2.2.1 (fun _ h _ _ => Or.inr (by rw [hal1]; exact h))
      (fun hp => by
        rcases hk1 with hk1 | hk1
        · exact KeyTr.ofEq hk1 hp
        · rw [hk1] at hp; cases hp) hst1 hI
  have hA1 : AllKeysValid (scanValueClearKey s) := by
    rcases scanValueClearKey_identity_or_clear s with e | ⟨hk, ht⟩
    · rw [e]; exact hA
    · exact AllKeysValid_of_clear s _ ht hst1 hk hA
  have hS1 : StrongSlot (scanValueClearKey s) := StrongSlot_of_eq hS hv1 hc1.2.2.1 hci1 hk1
  have hsz1 : (scanValueClearKey s).simpleKeyStack.size = (scanValueClearKey s).flowLevel := by
    rw [hst1, hc1.2.2.1]; have := hF.1; have := hF.2; omega
  have hst' : s'.simpleKeyStack = (scanValueClearKey s).simpleKeyStack := by
    rw [scanValue_preserves_simpleKeyStack s s' h, hst1]
  have hk' := scanValue_clears_simpleKey s s' h
  generalize scanValueClearKey s = s1 at *
  obtain ⟨hsh, hlast, hhd, hstk, hstt⟩ := prepare_pieces s1 hval hA1 hS1 hI1
  have hlr : lastReal (vals s') = some .value := by rw [hv, lastReal_snoc]; rfl
  refine LiveInv.ofPieces s1 s' (by rw [hv]; exact head_append' _ _ hhd) ?_ (by rw [hlr]; rfl) hk' hst' ?_ ?_ ?_ hI1
  · rw [hv]; exact Shape_snoc _ _ hsh (fun _ _ => hlast)
  · intro hpos
    have hin : s1.inFlow = true := by unfold ScannerState.inFlow; simp; omega
    simp [ScannerState.currentIndent, hind, scanValuePrepare_indents_of_inFlow hin]
  · intro j hj hp hb
    rw [hv, take_append_of_le' _ _ _ ?_]
    · exact hstk j hj hp hb
    · have := stackLen_of_AllKeysValid s1 hA1 j hj hp
      have hmono : (vals s1).length ≤ (vals (scanValuePrepare s1)).length := by
        simp only [vals, toks_length]
        exact scanValuePrepare_tokens_monotonic s1
      omega
  · intro j hj hp ht
    rw [hv]
    refine TailOK_append _ _ _ ?_ (hstt j hj hp ht) (fun t ht => by simp at ht; subst ht; rfl)
    have := stackLen_of_AllKeysValid s1 hA1 j hj hp
    have hmono : (vals s1).length ≤ (vals (scanValuePrepare s1)).length := by
      simp only [vals, toks_length]
      exact scanValuePrepare_tokens_monotonic s1
    omega

lemma LiveInv_dispatchBlock (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (hF : FlowSync s) (hS : StrongSlot s) (hA : AllKeysValid s) (hI : LiveInv s) : LiveInv s' := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact LiveInv_scanBlockEntry s _ (by assumption) (by simp_all) hF hA hI
    | exact LiveInv_scanKey s _ (by assumption) hF hA hI
    | exact LiveInv_scanValue s _ (by assumption) hF hS hA hI

/-! ### Content: one live, non-boundary token -/

/-- `s'` is `s` plus exactly one live, non-boundary token. -/
def PushLive (s s' : ScannerState) : Prop :=
  ∃ t, vals s' = vals s ++ [t] ∧ liveTok t = true ∧ Bnd (some t) = false

lemma PushLive.emitAt (s s0 : ScannerState) (p : YamlPos) (t : YamlToken)
    (h0 : s0.tokens = s.tokens) (ht : liveTok t = true ∧ Bnd (some t) = false) :
    PushLive s (s0.emitAt p t) :=
  ⟨t, by rw [vals_emitAt]; simp [vals, h0], ht.1, ht.2⟩

lemma PushLive.ofEq {s s1 s' : ScannerState} (h : PushLive s1 s') (h1 : s1.tokens = s.tokens) :
    PushLive s s' := by
  obtain ⟨t, hv, ht⟩ := h
  exact ⟨t, by rw [hv]; simp [vals, h1], ht⟩

lemma PushLive.congr {s s' s'' : ScannerState} (h : PushLive s s') (h2 : s''.tokens = s'.tokens) :
    PushLive s s'' := by
  obtain ⟨t, hv, ht⟩ := h
  exact ⟨t, by rw [← hv]; simp [vals, h2], ht⟩

lemma scanAnchorOrAlias_pushLive (s : ScannerState) (isAnchor : Bool) (s' : ScannerState)
    (hok : scanAnchorOrAlias s isAnchor = .ok s') : PushLive s s' := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; try dsimp only []
    have h_collect :=
      collectAnchorNameLoop_preserves_tokens s.advance "" (s.inputEnd - s.advance.offset)
    have h_adv := advance_preserves_tokens s
    apply PushLive.emitAt _ _ _ _ (h_collect.trans h_adv)
    first | exact ⟨rfl, rfl⟩ | (cases isAnchor <;> exact ⟨rfl, rfl⟩)


lemma scanVerbatimTag_pushLive (s : ScannerState) (pos : YamlPos) (s' : ScannerState)
    (hok : scanVerbatimTag s pos = .ok s') : PushLive s s' := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      exact PushLive.emitAt _ _ _ _
        (by simp only [collectVerbatimTagLoop_preserves_tokens, advance_preserves_tokens]) ⟨rfl, rfl⟩


lemma scanSecondaryTag_pushLive (s : ScannerState) (pos : YamlPos) :
    PushLive s (scanSecondaryTag s pos) := by
  unfold scanSecondaryTag
  exact PushLive.emitAt _ _ _ _
    (by simp only [collectTagSuffixLoop_preserves_tokens, advance_preserves_tokens]) ⟨rfl, rfl⟩


lemma scanNamedTag_pushLive (s : ScannerState) (pos : YamlPos) (inputEnd : Nat) :
    PushLive s (scanNamedTag s pos inputEnd) := by
  unfold scanNamedTag; simp only []
  have h_handle := collectTagHandleLoop_preserves_tokens s "" (inputEnd - s.offset)
  split
  · exact PushLive.emitAt _ _ _ _ (by rw [collectTagSuffixLoop_preserves_tokens, h_handle]) ⟨rfl, rfl⟩
  · exact PushLive.emitAt _ _ _ _ (by rw [collectTagSuffixLoop_preserves_tokens, h_handle]) ⟨rfl, rfl⟩


lemma scanTag_pushLive (s s' : ScannerState) (hok : scanTag s = .ok s') : PushLive s s' := by
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok
      have h := Except.ok.inj hok; subst h; try dsimp only []
      exact (scanVerbatimTag_pushLive _ _ _ hv).ofEq (advance_preserves_tokens s)
  · have h := Except.ok.inj hok; subst h; try dsimp only []
    exact (scanSecondaryTag_pushLive _ _).ofEq (advance_preserves_tokens s)
  · have h := Except.ok.inj hok; subst h; try dsimp only []
    exact (scanNamedTag_pushLive _ _ _).ofEq (advance_preserves_tokens s)


lemma scanBlockScalarBody_pushLive (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos)
    (s' : ScannerState) (h_tok : s_nl.tokens = s_orig.tokens)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    PushLive s_orig s' := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; try dsimp only [])
  all_goals exact (PushLive.emitAt _ _ _ _
    (by rw [collectBlockScalarLoop_preserves_tokens, h_tok]) ⟨rfl, rfl⟩).congr rfl


lemma scanBlockScalar_pushLive (s s' : ScannerState) (h : scanBlockScalar s = .ok s') :
    PushLive s s' := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_pushLive s _ _ _ _ _ s'
      (by rw [scanBlockScalarConsumeNewline_preserves_tokens _ _ (by assumption),
              scanBlockScalarSkipComment_preserves_tokens,
              skipWhitespace_preserves_tokens,
              parseBlockHeaderLoop_preserves_tokens,
              advance_preserves_tokens]) h


lemma scanPlainScalar_pushLive (s s' : ScannerState) (h : scanPlainScalar s = .ok s') :
    PushLive s s' := by
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i heq
  have h_collect := collectPlainScalarLoop_preserves_tokens s "" "" _ _ _ _ _ heq
  injection h with h_eq; subst h_eq
  exact PushLive.emitAt _ _ _ _ h_collect ⟨rfl, rfl⟩


lemma scanDoubleQuoted_pushLive (s s' : ScannerState) (h : scanDoubleQuoted s = .ok s') :
    PushLive s s' := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i heq
  have h_collect := collectDoubleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens s
  split at h
  · split at h <;> try contradiction
    injection h with h_eq; subst h_eq
    exact PushLive.emitAt _ _ _ _ (h_collect.trans h_adv) ⟨rfl, rfl⟩
  · injection h with h_eq; subst h_eq
    exact PushLive.emitAt _ _ _ _ (h_collect.trans h_adv) ⟨rfl, rfl⟩


lemma scanSingleQuoted_pushLive (s s' : ScannerState) (h : scanSingleQuoted s = .ok s') :
    PushLive s s' := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i heq
  have h_collect := collectSingleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens s
  split at h
  · split at h <;> try contradiction
    injection h with h_eq; subst h_eq
    exact PushLive.emitAt _ _ _ _ (h_collect.trans h_adv) ⟨rfl, rfl⟩
  · injection h with h_eq; subst h_eq
    exact PushLive.emitAt _ _ _ _ (h_collect.trans h_adv) ⟨rfl, rfl⟩


lemma dispatchContent_live (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s') :
    PushLive s s' ∧ KeyTr s s' := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · split at h
    · simp at h
    generalize h_fn : scanAnchorOrAlias s true = result at h
    cases result with
    | error e => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h
      exact ⟨scanAnchorOrAlias_pushLive s true s_a h_fn,
        KeyTr.ofEq (scanAnchorOrAlias_preserves_simpleKey s true s_a h_fn)⟩
  · split at h
    · split at h
      · simp at h
      split at h
      · simp at h
      · exact ⟨scanAnchorOrAlias_pushLive s false _ (aliasArm_scan_ok h),
          KeyTr.ofEq (scanAnchorOrAlias_preserves_simpleKey s false _ (aliasArm_scan_ok h))⟩
    · split at h
      · split at h
        · simp at h
        generalize h_fn : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact ⟨scanTag_pushLive s s_t h_fn,
            KeyTr.ofEq (scanTag_preserves_simpleKey s s_t h_fn)⟩
      · repeat (any_goals (split at h))
        any_goals contradiction
        all_goals (try simp only [Except.ok.injEq] at *)
        all_goals (try contradiction)
        all_goals (try subst_vars)
        all_goals first
          | exact ⟨scanBlockScalar_pushLive _ _ (by assumption),
              KeyTr.ofCleared (scanBlockScalar_clears_simpleKey _ _ (by assumption))⟩
          | exact ⟨scanPlainScalar_pushLive _ _ (by assumption),
              KeyTr.ofEq (scanPlainScalar_preserves_simpleKey _ _ (by assumption))⟩
          | exact ⟨scanDoubleQuoted_pushLive _ _ (by assumption),
              KeyTr.ofEq (scanDoubleQuoted_preserves_simpleKey _ _ (by assumption))⟩
          | exact ⟨scanSingleQuoted_pushLive _ _ (by assumption),
              KeyTr.ofEq (scanSingleQuoted_preserves_simpleKey _ _ (by assumption))⟩
          | exact ⟨(scanDoubleQuoted_pushLive _ _ (by assumption)).congr (by rfl),
              (fun _ => by
                have hk := scanDoubleQuoted_preserves_simpleKey _ _ (by assumption)
                refine ⟨?_, ?_, ?_⟩ <;> simp_all)⟩
          | exact ⟨(scanSingleQuoted_pushLive _ _ (by assumption)).congr (by rfl),
              (fun _ => by
                have hk := scanSingleQuoted_preserves_simpleKey _ _ (by assumption)
                refine ⟨?_, ?_, ?_⟩ <;> simp_all)⟩
          | (simp_all; done)


lemma LiveInv_dispatchContent (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s')
    (hS : StrongSlot s) (hA : AllKeysValid s) (hI : LiveInv s) : LiveInv s' := by
  obtain ⟨⟨t, hv, hlive, hbnd⟩, hkey⟩ := dispatchContent_live s c s' h
  refine LiveInv.ext s s' hI [t] hv (fun u hu _ => by simp at hu; subst hu; exact ⟨hlive, hbnd⟩)
    (L4YAML.Proofs.IndentStackBase.dispatchContent_preserves_indents h) ?_ (hal_of_StrongSlot hkey hS)
    (fun _ u hu => by simp at hu; subst hu; exact hbnd) hkey ?_
    (fun hp => by have := keyLen_of_AllKeysValid s hA hp; omega)
    (fun j hj hp => by have := stackLen_of_AllKeysValid s hA j hj hp; omega)
  · first
      | exact dispatchContent_preserves_flowLevel h
      | exact dispatchContent_preserves_flowLevel _ _ _ h
      | exact dispatchContent_preserves_flowLevel s c s' h
  · first
      | exact dispatchContent_preserves_simpleKeyStack h
      | exact dispatchContent_preserves_simpleKeyStack _ _ _ h
      | exact dispatchContent_preserves_simpleKeyStack s c s' h

/-! ### One step, the loop, the initial state -/

lemma LiveInv_scanNextToken (s s' : ScannerState) (hA : AllKeysValid s) (hD : DirInv s)
    (hB : SentinelBase s) (hF : FlowSync s) (hI : LiveInv s)
    (h : scanNextToken s = .ok (some s')) : LiveInv s' := by
  unfold scanNextToken at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  rename_i s2 c h_pre
  have hA2 := preprocess_preserves_AllKeysValid s s2 c h_pre hA
  have hD2 := DirInv_preprocess s s2 c h_pre hA hD
  have hB2 := preprocess_base h_pre hB
  have hF2 := FlowSync_preprocess s s2 c h_pre hF
  have hI2 := LiveInv_preprocess s s2 c h_pre hB hA hI
  have hS2 := StrongSlot_preprocess s s2 c h_pre hB hA hI
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact LiveInv_dispatchStructural s2 c _ (by assumption) hD2 hF2 hB2 hA2 hI2
  · split at h <;> (try (simp at h; done))
    split at h <;> (try (simp at h; done))
    have hA3 := allowDir_ite_preserves_AllKeysValid s2 hA2
    have hI3 : LiveInv (if s2.allowDirectives = true then
        { s2 with allowDirectives := false, documentEverStarted := true } else s2) := by
      split
      · exact LiveInv.ofFields s2 _ rfl rfl rfl (fun _ h _ _ => Or.inr h) (KeyTr.ofEq rfl) rfl hI2
      · exact hI2
    have hS3 : StrongSlot (if s2.allowDirectives = true then
        { s2 with allowDirectives := false, documentEverStarted := true } else s2) := by
      split
      · exact StrongSlot_of_eq hS2 rfl rfl rfl (Or.inl rfl)
      · exact hS2
    have hF3 : FlowSync (if s2.allowDirectives = true then
        { s2 with allowDirectives := false, documentEverStarted := true } else s2) := by
      split
      · exact ⟨hF2.1, hF2.2⟩
      · exact hF2
    split at h <;> (try (simp at h; done))
    split at h
    · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
      exact LiveInv_dispatchFlow _ c _ (by assumption) hF3 hS3 hA3 hI3
    · split at h <;> (try (simp at h; done))
      split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact LiveInv_dispatchBlock _ c _ (by assumption) hF3 hS3 hA3 hI3
      · split at h <;> (try (simp at h; done))
        split at h <;> (try (simp at h; done))
        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact LiveInv_dispatchContent _ c _ (by assumption) hS3 hA3 hI3

lemma LiveInv_scanLoop : ∀ (fuel : Nat) (s : ScannerState) (ts : Array (Positioned YamlToken)),
    AllKeysValid s → DirInv s → SentinelBase s → FlowSync s → LiveInv s →
    scanLoop s fuel = .ok ts → Shape (toks ts) ∧ (toks ts)[0]? = some .streamStart := by
  intro fuel
  induction fuel with
  | zero => intro s ts _ _ _ _ _ h; simp [scanLoop] at h
  | succ n ih =>
    intro s ts hA hD hB hF hI h
    unfold scanLoop at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · split at h
          · contradiction
          · split at h
            · contradiction
            · simp only [Except.ok.injEq] at h; subst h
              have hI' := LiveInv_unwindIndents s (-1) (Int.le_refl _) hB hA hI
              show Shape (vals ((unwindIndents s (-1)).emit .streamEnd)) ∧
                (vals ((unwindIndents s (-1)).emit .streamEnd))[0]? = some .streamStart
              rw [vals_emit]
              exact ⟨Shape_append_live _ _ hI'.shape
                  (fun t ht _ => by simp at ht; subst ht; exact ⟨rfl, rfl⟩),
                head_append' _ _ hI'.head⟩
    · rename_i s' hs'
      exact ih s' ts (scanNextToken_preserves_AllKeysValid s s' hA hs')
        (DirInv_scanNextToken s s' hA hD hs') (scanNextToken_base hs' hB)
        (FlowSync_scanNextToken s s' hF hs') (LiveInv_scanNextToken s s' hA hD hB hF hI hs') h

lemma LiveInv_init (input : String) : LiveInv ((ScannerState.mk' input).emit .streamStart) where
  head := by simp [vals, toks, ScannerState.mk', ScannerState.emit]
  shape := by
    intro j t hj hjt
    have hv : vals ((ScannerState.mk' input).emit .streamStart) = [.streamStart] := by
      simp [vals, toks, ScannerState.mk', ScannerState.emit]
    rw [hv] at hjt
    cases j with
    | zero => omega
    | succ k => simp at hjt
  deep := by intro h; simp [ScannerState.currentIndent, ScannerState.mk', ScannerState.emit] at h
  flow := by intro h; simp [ScannerState.mk', ScannerState.emit] at h
  fresh := by intro _; exact ⟨by simp [ScannerState.currentIndent, ScannerState.mk', ScannerState.emit], rfl⟩
  slot := by intro h; simp [ScannerState.mk', ScannerState.emit] at h
  stack := by intro j hj; simp [ScannerState.mk', ScannerState.emit] at hj
  tail := by intro h; simp [ScannerState.mk', ScannerState.emit] at h
  stackTail := by intro j hj; simp [ScannerState.mk', ScannerState.emit] at hj

lemma SentinelBase_init (input : String) : SentinelBase ((ScannerState.mk' input).emit .streamStart) := by
  simp [SentinelBase, ScannerState.mk', ScannerState.emit]

lemma FlowSync_init (input : String) : FlowSync ((ScannerState.mk' input).emit .streamStart) :=
  ⟨(FlowSync_mk' input).1, (FlowSync_mk' input).2⟩

lemma LiveInv_consumeBOM (s : ScannerState) (hI : LiveInv s) : LiveInv s.consumeBOM :=
  LiveInv.ofFields s _ (consumeBOM_preserves_tokens s) (consumeBOM_indents s)
    (consumeBOM_preserves_flowLevel s)
    (fun _ h _ _ => Or.inr (by
      show s.advance.simpleKeyAllowed = true
      rw [advance_preserves_simpleKeyAllowed]; exact h))
    (KeyTr.ofEq (consumeBOM_preserves_simpleKey s)) (consumeBOM_preserves_simpleKeyStack s) hI

lemma SentinelBase_consumeBOM (s : ScannerState) (hB : SentinelBase s) : SentinelBase s.consumeBOM := by
  unfold SentinelBase; rw [consumeBOM_indents]; exact hB

lemma FlowSync_consumeBOM (s : ScannerState) (hF : FlowSync s) : FlowSync s.consumeBOM := by
  unfold FlowSync
  rw [consumeBOM_preserves_flowLevel, consumeBOM_preserves_flowStack, consumeBOM_preserves_simpleKeyStack]
  exact hF

/-- Raw scanner output (placeholders included) is `Shape`d and starts with `.streamStart`. -/
lemma scan_shape (input : String) (ts : Array (Positioned YamlToken)) (h : scan input = .ok ts) :
    Shape (toks ts) ∧ (toks ts)[0]? = some .streamStart := by
  unfold scan at h
  have hA0 := AllKeysValid_init input
  have hD0 := DirInv_init input
  have hB0 := SentinelBase_init input
  have hF0 := FlowSync_init input
  have hI0 := LiveInv_init input
  dsimp only at h
  split at h
  · have h_tok := consumeBOM_preserves_tokens ((ScannerState.mk' input).emit .streamStart)
    exact LiveInv_scanLoop _ _ ts
      (AllKeysValid_mono _ _ hA0 (consumeBOM_preserves_simpleKey _)
        (consumeBOM_preserves_simpleKeyStack _) (by simp [h_tok]) (fun i hi => by simp [h_tok]))
      (DirInv_consumeBOM _ hA0 hD0) (SentinelBase_consumeBOM _ hB0) (FlowSync_consumeBOM _ hF0)
      (LiveInv_consumeBOM _ hI0) h
  · exact LiveInv_scanLoop _ _ ts hA0 hD0 hB0 hF0 hI0 h

/-- Filtered scanner output: every dead token after index 0 follows a non-boundary token, and the
    list starts with `.streamStart`. -/
lemma scanFiltered_liveF (input : String) (ts : Array (Positioned YamlToken))
    (h : scanFiltered input = .ok ts) :
    LiveF (toks ts) ∧ (toks ts)[0]? = some .streamStart := by
  unfold scanFiltered at h
  split at h
  · rename_i ts0 h0
    simp only [Except.ok.injEq] at h; subst h
    rw [toks_filter]
    obtain ⟨hsh, hhd⟩ := scan_shape input ts0 h0
    refine ⟨LiveF_of_Shape _ hsh, ?_⟩
    cases hL : toks ts0 with
    | nil => rw [hL] at hhd; simp at hhd
    | cons a L' =>
      rw [hL] at hhd; simp at hhd; subst hhd
      simp [nonPh]
  · contradiction

end L4YAML.Proofs.DocStartLiveInv

end Blanket
