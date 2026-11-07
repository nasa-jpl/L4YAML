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
open L4YAML.Proofs.CloseStaleExplicitKey

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
    (fun ha => skipToContent_simpleKeyAllowed_mono s s1 ha h)
    (KeyTr.ofEq (skipToContent_preserves_simpleKey s s1 h))
    (skipToContent_preserves_simpleKeyStack s s1 h) hI

lemma LiveInv_needIndentCheck (s : ScannerState) (hI : LiveInv s) :
    LiveInv { s with needIndentCheck := false } :=
  LiveInv.ofFields s _ rfl rfl rfl id (KeyTr.ofEq rfl) rfl hI

end L4YAML.Proofs.DocStartLiveInv

end Blanket
