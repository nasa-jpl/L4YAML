/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.DocStartLive
public import L4YAML.Proofs.Scanner.FlowSync

@[expose] public section Blanket

/-! # The `Shape` loop invariant (capstone 7.7, stream S3, obligation (β2b))

    `DocStartLive` states the scanner target at the list level (`Shape` on the
    raw token list).  This module carries `Shape (vals s)` over `scanNextToken`
    and `scanLoop` with the seven-clause carrier `LiveInv`:

    * `head`  — `vals[0] = .streamStart`;
    * `shape` — `Shape (vals s)`;
    * `deep`  — an open block indent (or a non-negative `currentIndent`) means the
      last real token is not a boundary (`.streamStart`/`.documentEnd`);
    * `flow`  — an open flow collection means the same;
    * `fresh` — after a boundary the indent is `-1` and the flow level `0`;
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
open L4YAML.Proofs.IndentStackBase

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
  deep : 1 < s.indents.size ∨ 0 ≤ s.currentIndent → Bnd (lastReal (vals s)) = false
  flow : 0 < s.flowLevel → Bnd (lastReal (vals s)) = false
  fresh : Bnd (lastReal (vals s)) = true → s.currentIndent = -1 ∧ s.flowLevel = 0
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
    (hal : s.simpleKeyAllowed = true → s'.simpleKeyAllowed = true)
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
    rw [heq] at hp ⊢
    rw [hv, hfl]
    have : s'.currentIndent = s.currentIndent := by simp [ScannerState.currentIndent, hind]
    rw [this]
    rw [seqTop_indents hind]
    refine SlotOK_al_mono _ _ _ _ _ _ ?_ (SlotOK_append _ _ _ _ _ _ (hkl hp) (hI.slot hp))
    intro hb
    rw [Bool.and_eq_true] at hb ⊢
    exact ⟨hal hb.1, hb.2⟩
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
    (hal : s.simpleKeyAllowed = true → t.simpleKeyAllowed = true)
    (hkey : KeyTr s t) (hst : t.simpleKeyStack = s.simpleKeyStack) (hI : LiveInv s) : LiveInv t := by
  have hv : vals t = vals s := by simp [vals, ht]
  have hci : t.currentIndent = s.currentIndent := by simp [ScannerState.currentIndent, hind]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv]; exact hI.head
  · rw [hv]; exact hI.shape
  · rw [hv, hind, hci]; exact hI.deep
  · rw [hv, hfl]; exact hI.flow
  · rw [hv, hci, hfl]; exact hI.fresh
  · intro hp
    have heq := hkey hp
    rw [heq] at hp ⊢
    rw [hv, hfl, hci, seqTop_indents hind]
    refine SlotOK_al_mono _ _ _ _ _ _ ?_ (hI.slot hp)
    intro hb
    rw [Bool.and_eq_true] at hb ⊢
    exact ⟨hal hb.1, hb.2⟩
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
    (fun ha => FlowSync.skipToContent_simpleKeyAllowed_mono s s1 ha h)
    (KeyTr.ofEq (skipToContent_preserves_simpleKey s s1 h))
    (skipToContent_preserves_simpleKeyStack s s1 h) hI

lemma LiveInv_needIndentCheck (s : ScannerState) (hI : LiveInv s) :
    LiveInv { s with needIndentCheck := false } :=
  LiveInv.ofFields s _ rfl rfl rfl id (KeyTr.ofEq rfl) rfl hI

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

lemma LiveInv_unwindIndents (s : ScannerState) (col : Int) (hc : 0 ≤ col)
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
    · rw [hM]; exact Shape_append_blockEnds _ _ hI.shape (hI.deep (Or.inl hsz)) hall'
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

end L4YAML.Proofs.DocStartLiveInv

end Blanket
