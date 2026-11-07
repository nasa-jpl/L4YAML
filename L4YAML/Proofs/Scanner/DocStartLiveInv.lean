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
      (`simpleKeyAllowed`);
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
    first (`ci < key.col`), or the key is the stale one a `-` leaves behind (`stale`), which
    `scanValueValidate` refuses. -/
def SlotOK (L : List YamlToken) (fl : Nat) (ci : Int) (stale : Bool) (k : SimpleKeyState) : Prop :=
  Bnd (lastReal (L.take k.tokenIndex)) = false ∨
    (fl = 0 ∧ (ci < (k.pos.col : Int) ∨ stale = true))

/-- The indent top is the sequence entry at the key's column. -/
def seqTop (s : ScannerState) (k : SimpleKeyState) : Bool :=
  match s.indents.back? with
  | some top => top.isSequence && top.column == (k.pos.col : Int)
  | none => false

/-- No boundary token from index `idx` on. -/
def TailOK (L : List YamlToken) (idx : Nat) : Prop := ∀ t ∈ L.drop idx, Bnd (some t) = false

structure LiveInv (s : ScannerState) : Prop where
  head : (vals s)[0]? = some .streamStart
  shape : Shape (vals s)
  deep : 0 ≤ s.currentIndent → Bnd (lastReal (vals s)) = false
  flow : 0 < s.flowLevel → Bnd (lastReal (vals s)) = false
  fresh : Bnd (lastReal (vals s)) = true → s.currentIndent < 0 ∧ s.flowLevel = 0
  slot : s.simpleKey.possible = true →
    SlotOK (vals s) s.flowLevel s.currentIndent (s.simpleKeyAllowed && seqTop s s.simpleKey)
      s.simpleKey
  stack : ∀ j (h : j < s.simpleKeyStack.size), s.simpleKeyStack[j].possible = true →
    Bnd (lastReal ((vals s).take s.simpleKeyStack[j].tokenIndex)) = false ∨
      (j = 0 ∧ s.currentIndent < (s.simpleKeyStack[j].pos.col : Int))
  tail : s.simpleKey.possible = true → TailOK (vals s) s.simpleKey.tokenIndex
  stackTail : ∀ j (h : j < s.simpleKeyStack.size), s.simpleKeyStack[j].possible = true →
    TailOK (vals s) s.simpleKeyStack[j].tokenIndex

lemma seqTop_indents {s s' : ScannerState} (h : s'.indents = s.indents) (k : SimpleKeyState) :
    seqTop s' k = seqTop s k := by simp [seqTop, h]

lemma TailOK_append (L M : List YamlToken) (idx : Nat) (hk : idx ≤ L.length)
    (h : TailOK L idx) (hM : ∀ t ∈ M, Bnd (some t) = false) : TailOK (L ++ M) idx := by
  intro t ht
  rw [List.drop_append_of_le_length hk] at ht
  rcases List.mem_append.1 ht with ht | ht
  · exact h t ht
  · exact hM t ht

/-- Key transport: a still-possible key is the old one. -/
def KeyTr (s s' : ScannerState) : Prop :=
  s'.simpleKey.possible = true → s'.simpleKey = s.simpleKey

lemma KeyTr.ofEq {s s' : ScannerState} (h : s'.simpleKey = s.simpleKey) : KeyTr s s' := fun _ => h
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

lemma SlotOK_al_mono (L : List YamlToken) (fl : Nat) (ci : Int) (al al' : Bool) (k : SimpleKeyState)
    (hal : al = true → al' = true) (h : SlotOK L fl ci al k) : SlotOK L fl ci al' k := by
  unfold SlotOK at h ⊢
  rcases h with h | ⟨h1, h2 | h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, Or.inl h2⟩
  · exact Or.inr ⟨h1, Or.inr (hal h2)⟩

/-- Appending live tokens (and placeholders) with the indent / flow / key state
    untouched keeps the invariant (`simpleKeyAllowed` may only go up). -/
lemma LiveInv.ext (s s' : ScannerState) (hI : LiveInv s) (M : List YamlToken)
    (hv : vals s' = vals s ++ M) (hM : LiveExt M)
    (hind : s'.indents = s.indents) (hfl : s'.flowLevel = s.flowLevel)
    (hal : s'.simpleKey.possible = true → (s.simpleKeyAllowed && seqTop s s.simpleKey) = true →
      (s'.simpleKeyAllowed && seqTop s' s'.simpleKey) = true)
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
    have heq := hkey hp
    have hal' := hal hp
    rw [heq] at hp ⊢
    rw [hv, hfl]
    have : s'.currentIndent = s.currentIndent := by simp [ScannerState.currentIndent, hind]
    rw [this]
    refine SlotOK_al_mono _ _ _ _ _ _ ?_ (SlotOK_append _ _ _ _ _ _ (hkl hp) (hI.slot hp))
    intro hb
    have := hal' hb
    rwa [heq] at this
  stack := by
    intro j hj hp
    simp only [hst] at hj hp ⊢
    have : s'.currentIndent = s.currentIndent := by simp [ScannerState.currentIndent, hind]
    rw [hv, this, take_append_of_le' _ _ _ (hsl j hj hp)]
    exact hI.stack j hj hp
  tail := by
    intro hp
    have heq := hkey hp
    have hM' := hMb (Or.inl hp)
    rw [heq] at hp ⊢
    rw [hv]
    exact TailOK_append _ _ _ (hkl hp) (hI.tail hp) hM'
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
    (hal : t.simpleKey.possible = true → (s.simpleKeyAllowed && seqTop s s.simpleKey) = true →
      (t.simpleKeyAllowed && seqTop t t.simpleKey) = true)
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
    have heq := hkey hp
    have hal' := hal hp
    rw [heq] at hp ⊢
    rw [hv, hfl, hci]
    refine SlotOK_al_mono _ _ _ _ _ _ ?_ (hI.slot hp)
    intro hb
    have := hal' hb
    rwa [heq] at this
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    rw [hv, hci]
    exact hI.stack j hj hp
  · intro hp
    have heq := hkey hp
    rw [heq] at hp ⊢
    rw [hv]; exact hI.tail hp
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    rw [hv]; exact hI.stackTail j hj hp

lemma LiveInv_skipToContent (s s1 : ScannerState) (h : skipToContent s = .ok s1)
    (hI : LiveInv s) : LiveInv s1 :=
  LiveInv.ofFields s s1 (skipToContent_preserves_tokens s s1 h)
    (skipToContent_preserves_indents s s1 h) (skipToContent_preserves_flowLevel s s1 h)
    (fun _ hb => by
      rw [Bool.and_eq_true] at hb ⊢
      exact ⟨FlowSync.skipToContent_simpleKeyAllowed_mono s s1 hb.1 h,
        by rw [skipToContent_preserves_simpleKey s s1 h,
          seqTop_indents (skipToContent_preserves_indents s s1 h)]; exact hb.2⟩)
    (KeyTr.ofEq (skipToContent_preserves_simpleKey s s1 h))
    (skipToContent_preserves_simpleKeyStack s s1 h) hI

lemma LiveInv_needIndentCheck (s : ScannerState) (hI : LiveInv s) :
    LiveInv { s with needIndentCheck := false } :=
  LiveInv.ofFields s _ rfl rfl rfl (fun _ => id) (KeyTr.ofEq rfl) rfl hI

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

lemma seqTop_col {s : ScannerState} {k : SimpleKeyState} (h : seqTop s k = true) :
    s.currentIndent = (k.pos.col : Int) := by
  unfold seqTop at h
  split at h
  · rename_i top htop
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    simp [ScannerState.currentIndent, htop, h.2]
  · cases h

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
      · right; refine ⟨by rw [hfl]; exact h0, Or.inl ?_⟩
        rcases h1 with h1 | h1
        · omega
        · rw [Bool.and_eq_true] at h1
          have := seqTop_col h1.2; omega
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
    exact LiveInv.ofFields s _ rfl rfl rfl (fun _ => id) (KeyTr.ofEq rfl) rfl hI

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
  have hal : s'.simpleKey.possible = true → (s.simpleKeyAllowed && seqTop s s.simpleKey) = true →
      (s'.simpleKeyAllowed && seqTop s' s'.simpleKey) = true := by
    intro _ hb
    exfalso
    rw [Bool.and_eq_true] at hb
    have hc := seqTop_col hb.2
    rcases hq with hq | hq
    · rw [hB.currentIndent_of_size_le_one hq] at hc; omega
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
    (hb : (s.simpleKeyAllowed && seqTop s s.simpleKey) = false) : StrongSlot s := by
  intro hp
  have := hI.slot hp
  rwa [hb] at this

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
      exact StrongSlot.of_al_false s hI (by simp at hal; simp [hal])

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

end L4YAML.Proofs.DocStartLiveInv

end Blanket
