module

public import L4YAML.Proofs.Scanner.DocStartLiveInv

/-!
# Structural depth of scanner output — (γ1), capstone 7.7 `parse_iff_grammar`

`depth` folds +1 over the four collection openers and −1 over the three closers.  `Bal L` says
every structural *dead* token (`.key`, `.value`, `.blockEnd`, `.flowEntry`, `.flowSequenceEnd`,
`.flowMappingEnd` — exactly the kinds `StreamState.validNextToken .afterDocument` still admits
after items 449/451) sits at positive depth, i.e. inside some open collection.

The carrier `DInv` is proven over every `scanNextToken` arm and `scanLoop`, landing
`scanFiltered_bal : scanFiltered input = .ok ts → Bal (toks ts)`.  Priority 97
(Tests/AdversarialInstantiation.lean) instantiates the statement and every clause before the
proofs; the plain slot-neutrality prediction was refuted there on `- a` and the slot clause takes
`SlotOK`'s shape instead.
-/
namespace L4YAML.Proofs.StructDepth

open L4YAML L4YAML.Scanner
open L4YAML.Proofs.DirectiveRuns
open L4YAML.Proofs.DocStartLive
open L4YAML.Proofs.DocStartLiveInv
open L4YAML.Proofs.FlowSync
open L4YAML.Proofs.ScannerCorrectness L4YAML.Proofs.ScannerCorrectness.ScanHelpers
open L4YAML.Proofs.FlowAdjacency
open L4YAML.Proofs.ScannerDirectivesPresent L4YAML.Proofs.ScannerAllowDirectives
open L4YAML.Proofs.PreprocessIndentStable L4YAML.Proofs.IndentStackBase
open L4YAML.Proofs.CloseStaleExplicitKey L4YAML.Proofs.EntryBoundaryLayout
open L4YAML.Proofs.ColFloor L4YAML.Proofs.FlowIndentStable
open L4YAML.Proofs.ScannerFlowCollection

/-! ### The list-level statement -/

def depthStep : YamlToken → Int
  | .blockSequenceStart | .blockMappingStart | .flowSequenceStart | .flowMappingStart => 1
  | .blockEnd | .flowSequenceEnd | .flowMappingEnd => -1
  | _ => 0

def depth (L : List YamlToken) : Int := L.foldl (fun d t => d + depthStep t) 0

def structDead : YamlToken → Bool
  | .key | .value | .blockEnd | .flowEntry | .flowSequenceEnd | .flowMappingEnd => true
  | _ => false

def Bal (L : List YamlToken) : Prop :=
  ∀ i t, L[i]? = some t → structDead t = true → 0 < depth (L.take i)

lemma foldl_depth (L : List YamlToken) (d : Int) :
    L.foldl (fun d t => d + depthStep t) d = d + depth L := by
  induction L generalizing d with
  | nil => simp [depth]
  | cons t L ih =>
    simp only [List.foldl_cons, depth]
    rw [ih, ih (0 + depthStep t)]; omega

@[simp] lemma depth_nil : depth [] = 0 := rfl

lemma depth_append (L M : List YamlToken) : depth (L ++ M) = depth L + depth M := by
  unfold depth; rw [List.foldl_append, foldl_depth]; rfl

@[simp] lemma depth_singleton (t : YamlToken) : depth [t] = depthStep t := by simp [depth]

lemma depth_cons (t : YamlToken) (L : List YamlToken) : depth (t :: L) = depthStep t + depth L := by
  rw [show t :: L = [t] ++ L from rfl, depth_append, depth_singleton]

lemma Bal_nil : Bal [] := fun _ _ h => by simp at h

lemma Bal_append (L M : List YamlToken) (hL : Bal L)
    (hM : ∀ i t, M[i]? = some t → structDead t = true → 0 < depth L + depth (M.take i)) :
    Bal (L ++ M) := by
  intro i t hi hd
  by_cases h : i < L.length
  · rw [List.getElem?_append_left h] at hi
    rw [List.take_append_of_le_length (Nat.le_of_lt h)]
    exact hL i t hi hd
  · rw [List.getElem?_append_right (Nat.le_of_not_lt h)] at hi
    rw [List.take_append, List.take_of_length_le (Nat.le_of_not_lt h), depth_append]
    exact hM _ t hi hd

/-- Appending tokens none of which is structural-dead keeps `Bal`. -/
lemma Bal_append_live (L M : List YamlToken) (hL : Bal L) (hall : ∀ t ∈ M, structDead t = false) :
    Bal (L ++ M) :=
  Bal_append L M hL (fun i t hi hd => by
    have := hall t (List.mem_of_getElem? hi); simp [this] at hd)

lemma Bal_snoc_live (L : List YamlToken) (t : YamlToken) (hL : Bal L) (ht : structDead t = false) :
    Bal (L ++ [t]) :=
  Bal_append_live L [t] hL (fun u hu => by simp at hu; subst hu; exact ht)

/-- Appending one token (dead or not) at positive depth keeps `Bal`. -/
lemma Bal_snoc_deep (L : List YamlToken) (t : YamlToken) (hL : Bal L) (hd : 0 < depth L) :
    Bal (L ++ [t]) :=
  Bal_append L [t] hL (fun i u hi _ => by
    cases i with
    | zero => simpa using hd
    | succ i => simp at hi)

/-! ### Overwriting a placeholder slot -/

lemma depth_set (L : List YamlToken) (i : Nat) (u : YamlToken) (hi : L[i]? = some .placeholder) :
    depth (L.set i u) = depth L + depthStep u := by
  induction L generalizing i with
  | nil => simp at hi
  | cons a L ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
      rw [List.set_cons_zero, depth_cons, depth_cons]
      have h0 : depthStep YamlToken.placeholder = 0 := rfl
      rw [h0]; omega
    | succ k =>
      simp only [List.getElem?_cons_succ] at hi
      rw [List.set_cons_succ, depth_cons, depth_cons, ih k hi]; omega

lemma take_set_of_le (L : List YamlToken) (i j : Nat) (u : YamlToken) (hj : j ≤ i) :
    (L.set i u).take j = L.take j := by
  induction L generalizing i j with
  | nil => simp
  | cons a L ih =>
    cases j with
    | zero => simp
    | succ j =>
      cases i with
      | zero => omega
      | succ i => simp only [List.set_cons_succ, List.take_succ_cons]; rw [ih i j (by omega)]

lemma take_set_of_lt (L : List YamlToken) (i j : Nat) (u : YamlToken) (hij : i < j) :
    (L.set i u).take j = (L.take j).set i u := by
  induction L generalizing i j with
  | nil => simp
  | cons a L ih =>
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero => simp
      | succ i => simp only [List.set_cons_succ, List.take_succ_cons]; rw [ih i j (by omega)]

/-- Overwriting a placeholder with a non-closing token: prefixes before the slot are unchanged
    and prefixes past it can only get deeper, so `Bal` is kept once the new token itself sits at
    positive depth (when it is dead). -/
lemma Bal_set (L : List YamlToken) (i : Nat) (u : YamlToken) (hL : Bal L)
    (hi : L[i]? = some .placeholder) (hu : 0 ≤ depthStep u)
    (hd : structDead u = true → 0 < depth (L.take i)) : Bal (L.set i u) := by
  intro j t hj ht
  by_cases hji : j ≤ i
  · rw [take_set_of_le _ _ _ _ hji]
    rcases Nat.lt_or_eq_of_le hji with hlt | rfl
    · rw [List.getElem?_set_ne (by omega)] at hj
      exact hL j t hj ht
    · have hlen : j < L.length := (List.getElem?_eq_some_iff.mp hi).1
      rw [List.getElem?_set_self hlen] at hj
      simp only [Option.some.injEq] at hj; subst hj
      exact hd ht
  · have hij : i < j := by omega
    rw [take_set_of_lt _ _ _ _ hij]
    have hi' : (L.take j)[i]? = some .placeholder := by
      rw [List.getElem?_take_of_lt hij]; exact hi
    rw [depth_set _ _ _ hi']
    rw [List.getElem?_set_ne (by omega)] at hj
    have := hL j t hj ht
    omega


/-- Every prefix of a `Bal` list has non-negative depth: closers sit at positive depth. -/
lemma Bal_nonneg (L : List YamlToken) (hL : Bal L) : ∀ i, 0 ≤ depth (L.take i) := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    by_cases hi : i < L.length
    · rw [List.take_succ_eq_append_getElem hi, depth_append, depth_singleton]
      have hs : L[i]? = some L[i] := List.getElem?_eq_getElem hi
      cases ht : L[i] with
      | blockEnd | flowSequenceEnd | flowMappingEnd =>
        have := hL i _ (by rw [hs, ht]) rfl
        simp only [depthStep]; omega
      | _ => simp only [depthStep]; omega
    · rw [List.take_of_length_le (by omega)] at ih ⊢
      exact ih

lemma Bal_depth_nonneg (L : List YamlToken) (hL : Bal L) : 0 ≤ depth L := by
  have := Bal_nonneg L hL L.length
  rwa [List.take_length] at this

/-! ### The carrier -/

/-- The slot condition on a saved simple key: the prefix through its first placeholder is at
    positive depth, or (block context) the key is stale-but-harmless — its `:` will push a fresh
    mapping (`ci < col`) or the slot will be re-saved first (`al`).  Mirrors `SlotOK`. -/
def DSlot (L : List YamlToken) (fl : Nat) (ci : Int) (al : Bool) (k : SimpleKeyState) : Prop :=
  0 < depth (L.take (k.tokenIndex + 1)) ∨ (fl = 0 ∧ (ci < (k.pos.col : Int) ∨ al = true))

/-- The two slot positions of a saved key hold placeholders. -/
def PhAt (L : List YamlToken) (i : Nat) : Prop :=
  L[i]? = some .placeholder ∧ L[i + 1]? = some .placeholder

structure DInv (s : ScannerState) : Prop where
  bound : ((s.indents.size : Int) - 1) + (s.flowLevel : Int) ≤ depth (vals s)
  bal : Bal (vals s)
  slot : s.simpleKey.possible = true →
    DSlot (vals s) s.flowLevel s.currentIndent s.simpleKeyAllowed s.simpleKey
  stack : ∀ (j : Nat) (k : SimpleKeyState), s.simpleKeyStack[j]? = some k → k.possible = true →
    0 < depth ((vals s).take (k.tokenIndex + 1)) ∨ (j = 0 ∧ s.currentIndent < (k.pos.col : Int))
  ph : s.simpleKey.possible = true → PhAt (vals s) s.simpleKey.tokenIndex
  stackPh : ∀ (j : Nat) (k : SimpleKeyState), s.simpleKeyStack[j]? = some k → k.possible = true →
    PhAt (vals s) k.tokenIndex
  ordCur : s.simpleKey.possible = true → ∀ (j : Nat) (k : SimpleKeyState), s.simpleKeyStack[j]? = some k →
    k.possible = true → k.tokenIndex + 2 ≤ s.simpleKey.tokenIndex
  ordStk : ∀ (j j' : Nat) (k k' : SimpleKeyState), s.simpleKeyStack[j]? = some k →
    s.simpleKeyStack[j']? = some k' → j < j' →
    k.possible = true → k'.possible = true → k.tokenIndex + 2 ≤ k'.tokenIndex

/-- The slot condition without the stale arm (what preprocessing establishes). -/
def StrongDSlot (s : ScannerState) : Prop :=
  s.simpleKey.possible = true → DSlot (vals s) s.flowLevel s.currentIndent false s.simpleKey

lemma StrongDSlot.weaken {s : ScannerState} (hS : StrongDSlot s) (al : Bool) :
    s.simpleKey.possible = true → DSlot (vals s) s.flowLevel s.currentIndent al s.simpleKey := by
  intro hp
  rcases hS hp with h | ⟨h0, h | h⟩
  · exact Or.inl h
  · exact Or.inr ⟨h0, Or.inl h⟩
  · cases h

lemma PhAt_append (L M : List YamlToken) (i : Nat) (hlt : i + 1 < L.length) (h : PhAt L i) :
    PhAt (L ++ M) i := by
  obtain ⟨h0, h1⟩ := h
  exact ⟨by rw [List.getElem?_append_left (by omega)]; exact h0,
    by rw [List.getElem?_append_left hlt]; exact h1⟩

lemma PhAt_set_lt (L : List YamlToken) (i j : Nat) (u : YamlToken) (hij : i + 1 < j)
    (h : PhAt L i) : PhAt (L.set j u) i := by
  obtain ⟨h0, h1⟩ := h
  exact ⟨by rw [List.getElem?_set_ne (by omega)]; exact h0,
    by rw [List.getElem?_set_ne (by omega)]; exact h1⟩

lemma DSlot_append (L M : List YamlToken) (fl : Nat) (ci : Int) (al : Bool) (k : SimpleKeyState)
    (hk : k.tokenIndex + 1 ≤ L.length) (h : DSlot L fl ci al k) : DSlot (L ++ M) fl ci al k := by
  unfold DSlot at h ⊢
  rwa [take_append_of_le' _ _ _ hk]

/-- Monotonicity of the slot condition in the state fields it mentions. -/
lemma DSlot_mono (L : List YamlToken) (fl : Nat) (ci ci' : Int) (al al' : Bool) (k : SimpleKeyState)
    (hci : ci' ≤ ci ∨ al' = true) (hal : al = true → al' = true) (h : DSlot L fl ci al k) :
    DSlot L fl ci' al' k := by
  rcases h with h | ⟨h0, h | h⟩
  · exact Or.inl h
  · rcases hci with hci | hci
    · exact Or.inr ⟨h0, Or.inl (by omega)⟩
    · exact Or.inr ⟨h0, Or.inr hci⟩
  · exact Or.inr ⟨h0, Or.inr (hal h)⟩

/-- Index facts `AllKeysValid` gives on the token list. -/
lemma keyLen (s : ScannerState) (hA : AllKeysValid s) (hp : s.simpleKey.possible = true) :
    s.simpleKey.tokenIndex + 1 < (vals s).length := by
  rw [vals_length]; exact (hA.1 hp).2.1

lemma stackLen (s : ScannerState) (hA : AllKeysValid s) (j : Nat) (k : SimpleKeyState)
    (hk : s.simpleKeyStack[j]? = some k) (hp : k.possible = true) :
    k.tokenIndex + 1 < (vals s).length := by
  obtain ⟨hj, rfl⟩ := Array.getElem?_eq_some_iff.mp hk
  rw [vals_length]; exact (hA.2 j hj hp).2.1

/-- Appending tokens with the key/stack carried over (same index and position when kept). -/
lemma DInv.ext (s s' : ScannerState) (hI : DInv s) (hA : AllKeysValid s) (M : List YamlToken)
    (hv : vals s' = vals s ++ M)
    (hbnd : ((s'.indents.size : Int) - 1) + (s'.flowLevel : Int) ≤ depth (vals s'))
    (hbal : Bal (vals s'))
    (hfl : s'.flowLevel = s.flowLevel)
    (hci : s'.currentIndent ≤ s.currentIndent ∨
      (s'.simpleKeyAllowed = true ∧ s.simpleKeyStack.size = 0))
    (hal : s.simpleKeyAllowed = true → s'.simpleKeyAllowed = true)
    (hkey : KeyTr s s') (hst : s'.simpleKeyStack = s.simpleKeyStack) : DInv s' where
  bound := hbnd
  bal := hbal
  slot := by
    intro hp
    obtain ⟨hp0, hidx, hpos⟩ := hkey hp
    have h := hI.slot hp0
    have h' : DSlot (vals s') s'.flowLevel s.currentIndent s.simpleKeyAllowed s.simpleKey := by
      rw [hv, hfl]; exact DSlot_append _ _ _ _ _ _ (by have := keyLen s hA hp0; omega) h
    have h'' := DSlot_mono _ _ _ s'.currentIndent _ s'.simpleKeyAllowed _
      (by rcases hci with h | ⟨h, _⟩; exact Or.inl h; exact Or.inr h) hal h'
    unfold DSlot at h'' ⊢; rw [hidx, hpos]; exact h''
  stack := by
    intro j k hk hp
    rw [hst] at hk
    have := stackLen s hA j k hk hp
    rw [hv, take_append_of_le' _ _ _ (by omega)]
    rcases hI.stack j k hk hp with h | ⟨h0, h⟩
    · exact Or.inl h
    · rcases hci with hci | ⟨_, hz⟩
      · exact Or.inr ⟨h0, by omega⟩
      · exfalso
        have := (Array.getElem?_eq_some_iff.mp hk).1
        omega
  ph := by
    intro hp
    obtain ⟨hp0, hidx, _⟩ := hkey hp
    rw [hv, hidx]; exact PhAt_append _ _ _ (keyLen s hA hp0) (hI.ph hp0)
  stackPh := by
    intro j k hk hp
    rw [hst] at hk
    rw [hv]; exact PhAt_append _ _ _ (stackLen s hA j k hk hp) (hI.stackPh j k hk hp)
  ordCur := by
    intro hp j k hk hpj
    obtain ⟨hp0, hidx, _⟩ := hkey hp
    rw [hst] at hk; rw [hidx]; exact hI.ordCur hp0 j k hk hpj
  ordStk := by
    intro j j' k k' hk hk' hlt hpj hpj'
    rw [hst] at hk hk'; exact hI.ordStk j j' k k' hk hk' hlt hpj hpj'

/-- `DInv.ext` from the strong slot form: no `simpleKeyAllowed` relation needed. -/
lemma DInv.extStrong (s s' : ScannerState) (hI : DInv s) (hS : StrongDSlot s) (hA : AllKeysValid s)
    (M : List YamlToken)
    (hv : vals s' = vals s ++ M)
    (hbnd : ((s'.indents.size : Int) - 1) + (s'.flowLevel : Int) ≤ depth (vals s'))
    (hbal : Bal (vals s'))
    (hfl : s'.flowLevel = s.flowLevel)
    (hci : s'.currentIndent ≤ s.currentIndent ∨
      (s'.simpleKeyAllowed = true ∧ s.simpleKeyStack.size = 0))
    (hkey : KeyTr s s') (hst : s'.simpleKeyStack = s.simpleKeyStack) : DInv s' where
  bound := hbnd
  bal := hbal
  slot := by
    intro hp
    obtain ⟨hp0, hidx, hpos⟩ := hkey hp
    have h := hS hp0
    have h' : DSlot (vals s') s'.flowLevel s.currentIndent false s.simpleKey := by
      rw [hv, hfl]; exact DSlot_append _ _ _ _ _ _ (by have := keyLen s hA hp0; omega) h
    have h'' := DSlot_mono _ _ _ s'.currentIndent _ s'.simpleKeyAllowed _
      (by rcases hci with h | ⟨h, _⟩; exact Or.inl h; exact Or.inr h) (fun h => by cases h) h'
    unfold DSlot at h'' ⊢; rw [hidx, hpos]; exact h''
  stack := by
    intro j k hk hp
    rw [hst] at hk
    have := stackLen s hA j k hk hp
    rw [hv, take_append_of_le' _ _ _ (by omega)]
    rcases hI.stack j k hk hp with h | ⟨h0, h⟩
    · exact Or.inl h
    · rcases hci with hci | ⟨_, hz⟩
      · exact Or.inr ⟨h0, by omega⟩
      · exfalso
        have := (Array.getElem?_eq_some_iff.mp hk).1
        omega
  ph := by
    intro hp
    obtain ⟨hp0, hidx, _⟩ := hkey hp
    rw [hv, hidx]; exact PhAt_append _ _ _ (keyLen s hA hp0) (hI.ph hp0)
  stackPh := by
    intro j k hk hp
    rw [hst] at hk
    rw [hv]; exact PhAt_append _ _ _ (stackLen s hA j k hk hp) (hI.stackPh j k hk hp)
  ordCur := by
    intro hp j k hk hpj
    obtain ⟨hp0, hidx, _⟩ := hkey hp
    rw [hst] at hk; rw [hidx]; exact hI.ordCur hp0 j k hk hpj
  ordStk := by
    intro j j' k k' hk hk' hlt hpj hpj'
    rw [hst] at hk hk'; exact hI.ordStk j j' k k' hk hk' hlt hpj hpj'

/-- No token change: the carrier follows from the field relations alone. -/
lemma DInv.ofFields (s t : ScannerState) (hI : DInv s) (hA : AllKeysValid s)
    (ht : t.tokens = s.tokens) (hind : t.indents = s.indents) (hfl : t.flowLevel = s.flowLevel)
    (hal : s.simpleKeyAllowed = true → t.simpleKeyAllowed = true)
    (hkey : KeyTr s t) (hst : t.simpleKeyStack = s.simpleKeyStack) : DInv t :=
  have hv : vals t = vals s := by simp [vals, ht]
  DInv.ext s t hI hA [] (by simp [hv]) (by rw [hind, hfl, hv]; exact hI.bound)
    (by rw [hv]; exact hI.bal) hfl (Or.inl (by simp [ScannerState.currentIndent, hind])) hal hkey hst

lemma DInv_skipToContent (s s1 : ScannerState) (h : skipToContent s = .ok s1)
    (hA : AllKeysValid s) (hI : DInv s) : DInv s1 :=
  DInv.ofFields s s1 hI hA (skipToContent_preserves_tokens s s1 h)
    (skipToContent_preserves_indents s s1 h) (skipToContent_preserves_flowLevel s s1 h)
    (fun hb => FlowSync.skipToContent_simpleKeyAllowed_mono s s1 hb h)
    (KeyTr.ofEq (skipToContent_preserves_simpleKey s s1 h))
    (skipToContent_preserves_simpleKeyStack s s1 h)

lemma DInv_needIndentCheck (s : ScannerState) (hA : AllKeysValid s) (hI : DInv s) :
    DInv { s with needIndentCheck := false } :=
  DInv.ofFields s _ hI hA rfl rfl rfl (fun h => h) (KeyTr.ofEq rfl) rfl


/-! ### The unwind: each popped indent emits a `blockEnd` at positive depth -/

/-- Depth accounting over `unwindIndentsLoop`: the bound and `Bal` survive every pop. -/
lemma unwindLoop_depth : ∀ (fuel : Nat) (s : ScannerState) (col : Int),
    ((s.indents.size : Int) - 1) + (s.flowLevel : Int) ≤ depth (vals s) → Bal (vals s) →
    ((((unwindIndentsLoop s col fuel).indents.size : Int) - 1) +
        ((unwindIndentsLoop s col fuel).flowLevel : Int) ≤ depth (vals (unwindIndentsLoop s col fuel))) ∧
      Bal (vals (unwindIndentsLoop s col fuel)) := by
  intro fuel
  induction fuel with
  | zero => intro s col hb hB; simpa [unwindIndentsLoop] using ⟨hb, hB⟩
  | succ f ih =>
    intro s col hb hB
    unfold unwindIndentsLoop
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have hv : vals (popStep s) = vals s ++ [.blockEnd] := by simp [popStep, vals, toks, ScannerState.emit]
      have hfl : (popStep s).flowLevel = s.flowLevel := by simp [popStep, ScannerState.emit]
      have key := ih (popStep s) col ?_ ?_
      · simpa only [popStep] using key
      · rw [hv, depth_append, depth_singleton, popStep_indents_size, hfl]
        show ((s.indents.size - 1 : Nat) : Int) - 1 + (s.flowLevel : Int) ≤ depth (vals s) + (-1)
        omega
      · rw [hv]; exact Bal_snoc_deep _ _ hB (by omega)
    · exact ⟨hb, hB⟩

lemma DInv_unwindIndents (s : ScannerState) (col : Int) (hc : -1 ≤ col)
    (hB : SentinelBase s) (hA : AllKeysValid s) (hI : DInv s) : DInv (unwindIndents s col) := by
  have hd := unwindLoop_depth s.indents.size s col hI.bound hI.bal
  unfold unwindIndents at hd ⊢
  rcases unwindIndentsLoop_result s.indents.size s col (Nat.le_refl _) with ⟨heq, _⟩ | ⟨M, hM, _, _, hcol, hfin⟩
  · rw [heq]; exact hI
  · generalize hr : unwindIndentsLoop s col s.indents.size = r at hM hfin hd
    have hfl : r.flowLevel = s.flowLevel := by rw [← hr]; exact unwindIndentsLoop_preserves_flowLevel _ _ _
    have hk : r.simpleKey = s.simpleKey := by rw [← hr]; exact unwindIndentsLoop_preserves_simpleKey _ _ _
    have hst : r.simpleKeyStack = s.simpleKeyStack := by
      rw [← hr]; exact unwindIndentsLoop_preserves_simpleKeyStack _ _ _
    have hal : r.simpleKeyAllowed = s.simpleKeyAllowed := by
      rw [← hr]; exact unwindIndentsLoop_preserves_simpleKeyAllowed _ _ _
    have hBr : SentinelBase r := by rw [← hr]; exact unwindIndentsLoop_base _ _ _ hB
    have hci : r.currentIndent ≤ col := by
      rcases hfin with h | h
      · exact h
      · rw [hBr.currentIndent_of_size_le_one h]; omega
    exact DInv.ext s r hI hA _ hM hd.1 hd.2 hfl (Or.inl (by omega)) (by rw [hal]; exact id)
      (KeyTr.ofEq hk) hst

/-! ### `saveSimpleKey`: a fresh slot of two placeholders -/

lemma DInv_saveSimpleKey (s : ScannerState) (hB : SentinelBase s) (hA : AllKeysValid s)
    (hI : DInv s) : DInv (saveSimpleKey s) ∧ StrongDSlot (saveSimpleKey s) := by
  unfold saveSimpleKey
  split
  · rename_i hin
    simp only [Bool.and_eq_true] at hin
    have hfl : 0 < s.flowLevel := by
      have := hin.1; unfold ScannerState.inFlow at this; simpa using this
    refine ⟨hI, fun hp => ?_⟩
    rcases hI.slot hp with h | ⟨h0, _⟩
    · exact Or.inl h
    · omega
  · split
    · generalize hph0 : (⟨s.currentPos, .placeholder, s.currentPos⟩ : Positioned YamlToken) = ph
      have hphv : ph.val = .placeholder := by rw [← hph0]
      have hv : vals ({ s with tokens := (s.tokens.push ph).push ph } : ScannerState) =
          vals s ++ [.placeholder, .placeholder] := by
        simp [vals, toks, hphv]
      have hlen : (vals s).length = s.tokens.size := vals_length s
      have hdep : depth (vals s ++ [.placeholder, .placeholder]) = depth (vals s) := by
        rw [depth_append]; simp [depth, depthStep]
      have hslot : DSlot (vals s ++ [.placeholder, .placeholder]) s.flowLevel s.currentIndent false
          { possible := true, tokenIndex := s.tokens.size, pos := s.currentPos, endLine := s.line } := by
        unfold DSlot
        simp only
        rw [List.take_append, List.take_of_length_le (by omega),
          show s.tokens.size + 1 - (vals s).length = 1 by omega]
        simp only [List.take_succ_cons, List.take_zero, depth_append, depth_singleton, depthStep,
          Int.add_zero]
        by_cases hpos : 0 < depth (vals s)
        · exact Or.inl hpos
        · right
          have hb := hI.bound
          have hsp := hB.size_pos
          have hsz : s.indents.size ≤ 1 := by omega
          refine ⟨by omega, Or.inl ?_⟩
          rw [hB.currentIndent_of_size_le_one hsz]; omega
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · show ((s.indents.size : Int) - 1) + (s.flowLevel : Int) ≤ depth (vals { s with tokens := (s.tokens.push ph).push ph })
        rw [hv, hdep]; exact hI.bound
      · show Bal (vals { s with tokens := (s.tokens.push ph).push ph })
        rw [hv]; exact Bal_append_live _ _ hI.bal (fun t ht => by simp at ht; rcases ht with rfl | rfl <;> rfl)
      · intro _
        show DSlot (vals { s with tokens := (s.tokens.push ph).push ph }) s.flowLevel s.currentIndent
          s.simpleKeyAllowed _
        rw [hv]
        exact DSlot_mono _ _ _ _ _ _ _ (Or.inl (Int.le_refl _)) (fun h => by cases h) hslot
      · intro j k hk hp
        show 0 < depth ((vals { s with tokens := (s.tokens.push ph).push ph }).take (k.tokenIndex + 1)) ∨
          (j = 0 ∧ s.currentIndent < (k.pos.col : Int))
        rw [hv, take_append_of_le' _ _ _ (by have := stackLen s hA j k hk hp; omega)]
        exact hI.stack j k hk hp
      · intro _
        show PhAt (vals { s with tokens := (s.tokens.push ph).push ph }) s.tokens.size
        rw [hv]
        refine ⟨?_, ?_⟩
        · rw [List.getElem?_append_right (by omega), show s.tokens.size - (vals s).length = 0 by omega]; rfl
        · rw [List.getElem?_append_right (by omega), show s.tokens.size + 1 - (vals s).length = 1 by omega]; rfl
      · intro j k hk hp
        show PhAt (vals { s with tokens := (s.tokens.push ph).push ph }) k.tokenIndex
        rw [hv]; exact PhAt_append _ _ _ (stackLen s hA j k hk hp) (hI.stackPh j k hk hp)
      · intro _ j k hk hp
        show k.tokenIndex + 2 ≤ s.tokens.size
        have := stackLen s hA j k hk hp; omega
      · intro j j' k k' hk hk' hlt hp hp'
        exact hI.ordStk j j' k k' hk hk' hlt hp hp'
      · intro _
        show DSlot (vals { s with tokens := (s.tokens.push ph).push ph }) s.flowLevel s.currentIndent false _
        rw [hv]; exact hslot
    · rename_i hal
      have hal' : s.simpleKeyAllowed = false := by simpa using hal
      refine ⟨hI, fun hp => ?_⟩
      exact DSlot_mono _ _ _ _ _ _ _ (Or.inl (Int.le_refl _)) (fun h => by rw [hal'] at h; cases h)
        (hI.slot hp)

lemma DInv_closeStaleExplicitKey (s : ScannerState) (hA : AllKeysValid s) (hI : DInv s)
    (hS : StrongDSlot s) : DInv (closeStaleExplicitKey s) ∧ StrongDSlot (closeStaleExplicitKey s) := by
  rcases closeStaleExplicitKey_cases s with h | ⟨c, _, h⟩
  · rw [h]; exact ⟨hI, hS⟩
  · rw [h]
    exact ⟨DInv.ofFields s _ hI hA rfl rfl rfl (fun h => h) (KeyTr.ofEq rfl) rfl, fun hp => hS hp⟩

/-! ### Preprocessing -/

lemma DInv_preprocess (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c)))
    (hB : SentinelBase s) (hA : AllKeysValid s) (hI : DInv s) : DInv s1 ∧ StrongDSlot s1 := by
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have hI1 := DInv_skipToContent s s_skip h_skip hA hI
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
            have hAu : AllKeysValid (unwindIndents s_skip s_skip.col) :=
              unwindIndents_preserves_AllKeysValid s_skip _ hA1
            have hI2 := DInv_needIndentCheck _ hAu (DInv_unwindIndents s_skip s_skip.col (by omega) hB1 hA1 hI1)
            have hA2 : AllKeysValid { unwindIndents s_skip s_skip.col with needIndentCheck := false } :=
              unwindIndents_preserves_AllKeysValid s_skip _ hA1
            have hB2 : SentinelBase { unwindIndents s_skip s_skip.col with needIndentCheck := false } :=
              (unwindIndents_base s_skip _ hB1).of_indents_eq rfl
            obtain ⟨hI3, hS3⟩ := DInv_saveSimpleKey _ hB2 hA2 hI2
            exact DInv_closeStaleExplicitKey _ (saveSimpleKey_preserves_AllKeysValid _ hA2) hI3 hS3
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            obtain ⟨hI3, hS3⟩ := DInv_saveSimpleKey _ hB1 hA1 hI1
            exact DInv_closeStaleExplicitKey _ (saveSimpleKey_preserves_AllKeysValid _ hA1) hI3 hS3


/-! ### Generic transports for the dispatch arms -/

/-- Appending with the key cleared and the stack unchanged: only the stack clauses transport. -/
lemma DInv.clearedAppend (s s' : ScannerState) (M : List YamlToken) (hv : vals s' = vals s ++ M)
    (hbnd : ((s'.indents.size : Int) - 1) + (s'.flowLevel : Int) ≤ depth (vals s'))
    (hbal : Bal (vals s')) (hk : s'.simpleKey.possible = false)
    (hst : s'.simpleKeyStack = s.simpleKeyStack)
    (hci : s'.currentIndent ≤ s.currentIndent ∨ s.simpleKeyStack.size = 0)
    (hlen : ∀ (j : Nat) (k : SimpleKeyState), s.simpleKeyStack[j]? = some k → k.possible = true →
      k.tokenIndex + 1 < (vals s).length)
    (hI : DInv s) : DInv s' where
  bound := hbnd
  bal := hbal
  slot := fun hp => by rw [hk] at hp; cases hp
  stack := by
    intro j k hk' hp
    rw [hst] at hk'
    have := hlen j k hk' hp
    rw [hv, take_append_of_le' _ _ _ (by omega)]
    rcases hI.stack j k hk' hp with h | ⟨h0, h⟩
    · exact Or.inl h
    · rcases hci with hci | hz
      · exact Or.inr ⟨h0, by omega⟩
      · exfalso; have := (Array.getElem?_eq_some_iff.mp hk').1; omega
  ph := fun hp => by rw [hk] at hp; cases hp
  stackPh := by
    intro j k hk' hp
    rw [hst] at hk'
    rw [hv]; exact PhAt_append _ _ _ (hlen j k hk' hp) (hI.stackPh j k hk' hp)
  ordCur := fun hp => by rw [hk] at hp; cases hp
  ordStk := by
    intro j j' k k' hk hk' hlt hpj hpj'
    rw [hst] at hk hk'; exact hI.ordStk j j' k k' hk hk' hlt hpj hpj'

lemma of_cleared {P : Prop} {b : Bool} (hk : b = false) : b = true → P :=
  fun hp => by rw [hk] at hp; cases hp

/-- Positive depth from the bound once the stack has its sentinel and the flow level is positive. -/
lemma depth_pos_of_flow (s : ScannerState) (hB : SentinelBase s) (hI : DInv s) (hpos : 0 < s.flowLevel) :
    0 < depth (vals s) := by
  have := hI.bound; have := hB.size_pos; omega

/-- Positive depth from the bound once more than the sentinel is on the indent stack. -/
lemma depth_pos_of_indents (s : ScannerState) (hI : DInv s) (hsz : 1 < s.indents.size) :
    0 < depth (vals s) := by
  have := hI.bound; omega

/-! ### Flow indicators -/

/-- Opening a flow collection: one opener appended, the current key pushed on the stack. -/
lemma DInv.flowStart (s s' : ScannerState) (t : YamlToken) (hstep : depthStep t = 1)
    (hlive : structDead t = false) (hv : vals s' = vals s ++ [t])
    (hfl : s'.flowLevel = s.flowLevel + 1) (hk : s'.simpleKey.possible = false)
    (hst : s'.simpleKeyStack = s.simpleKeyStack.push s.simpleKey) (hind : s'.indents = s.indents)
    (hF : FlowSync s) (hS : StrongDSlot s) (hA : AllKeysValid s) (hI : DInv s) : DInv s' := by
  have hci : s'.currentIndent = s.currentIndent := by simp [ScannerState.currentIndent, hind]
  have hsz : s.simpleKeyStack.size = s.flowLevel := by have := hF.1; have := hF.2; omega
  refine ⟨?_, ?_, of_cleared hk, ?_, of_cleared hk, ?_, of_cleared hk, ?_⟩
  · rw [hv, depth_append, depth_singleton, hstep, hind, hfl]; have := hI.bound; push_cast; omega
  · rw [hv]; exact Bal_snoc_live _ _ hI.bal hlive
  · intro j k hk' hp
    rw [hst] at hk'
    rw [hv, hci]
    by_cases hj : j = s.simpleKeyStack.size
    · subst hj
      rw [Array.getElem?_push_size] at hk'
      simp only [Option.some.injEq] at hk'; subst hk'
      rw [take_append_of_le' _ _ _ (by have := keyLen s hA hp; omega)]
      rcases hS hp with h | ⟨h0, h | h⟩
      · exact Or.inl h
      · exact Or.inr ⟨by omega, h⟩
      · cases h
    · have hlt : j < s.simpleKeyStack.size := by
        have := (Array.getElem?_eq_some_iff.mp hk').1; rw [Array.size_push] at this; omega
      rw [Array.getElem?_push_lt hlt] at hk'
      replace hk' : s.simpleKeyStack[j]? = some k := by rw [Array.getElem?_eq_getElem hlt]; exact hk'
      rw [take_append_of_le' _ _ _ (by have := stackLen s hA j k hk' hp; omega)]
      exact hI.stack j k hk' hp
  · intro j k hk' hp
    rw [hst] at hk'
    rw [hv]
    by_cases hj : j = s.simpleKeyStack.size
    · subst hj
      rw [Array.getElem?_push_size] at hk'
      simp only [Option.some.injEq] at hk'; subst hk'
      exact PhAt_append _ _ _ (keyLen s hA hp) (hI.ph hp)
    · have hlt : j < s.simpleKeyStack.size := by
        have := (Array.getElem?_eq_some_iff.mp hk').1; rw [Array.size_push] at this; omega
      rw [Array.getElem?_push_lt hlt] at hk'
      replace hk' : s.simpleKeyStack[j]? = some k := by rw [Array.getElem?_eq_getElem hlt]; exact hk'
      exact PhAt_append _ _ _ (stackLen s hA j k hk' hp) (hI.stackPh j k hk' hp)
  · intro j j' k k' hk hk' hlt hpj hpj'
    rw [hst] at hk hk'
    have hj'le : j' < s.simpleKeyStack.size + 1 := by
      have := (Array.getElem?_eq_some_iff.mp hk').1; rwa [Array.size_push] at this
    have hjlt : j < s.simpleKeyStack.size := by omega
    rw [Array.getElem?_push_lt hjlt] at hk
    replace hk : s.simpleKeyStack[j]? = some k := by rw [Array.getElem?_eq_getElem hjlt]; exact hk
    by_cases hj : j' = s.simpleKeyStack.size
    · subst hj
      rw [Array.getElem?_push_size] at hk'
      simp only [Option.some.injEq] at hk'; subst hk'
      exact hI.ordCur hpj' j k hk hpj
    · have hj'lt : j' < s.simpleKeyStack.size := by omega
      rw [Array.getElem?_push_lt hj'lt] at hk'
      replace hk' : s.simpleKeyStack[j']? = some k' := by rw [Array.getElem?_eq_getElem hj'lt]; exact hk'
      exact hI.ordStk j j' k k' hk hk' hlt hpj hpj'

/-- Closing a flow collection: one closer appended at positive depth, the saved key restored. -/
lemma DInv.flowEnd (s s' : ScannerState) (t : YamlToken) (hstep : depthStep t = -1)
    (hv : vals s' = vals s ++ [t]) (hpos : 0 < s.flowLevel) (hfl : s'.flowLevel = s.flowLevel - 1)
    (hk : s'.simpleKey = s.simpleKeyStack.back?.getD {})
    (hst : s'.simpleKeyStack = s.simpleKeyStack.pop) (hind : s'.indents = s.indents)
    (hB : SentinelBase s) (hF : FlowSync s) (hA : AllKeysValid s) (hI : DInv s) : DInv s' := by
  have hci : s'.currentIndent = s.currentIndent := by simp [ScannerState.currentIndent, hind]
  have hsz : s.simpleKeyStack.size = s.flowLevel := by have := hF.1; have := hF.2; omega
  have hback : s.simpleKeyStack.back? = s.simpleKeyStack[s.simpleKeyStack.size - 1]? := rfl
  have hcur : s'.simpleKey.possible = true →
      s.simpleKeyStack[s.simpleKeyStack.size - 1]? = some s'.simpleKey := by
    intro hp
    rw [hk, hback] at hp ⊢
    cases hb : s.simpleKeyStack[s.simpleKeyStack.size - 1]? with
    | none => rw [hb] at hp; cases hp
    | some k => rfl
  have hpopLt : ∀ j (k : SimpleKeyState), s.simpleKeyStack.pop[j]? = some k →
      j < s.simpleKeyStack.size - 1 ∧ s.simpleKeyStack[j]? = some k := by
    intro j k hk'
    have hj := (Array.getElem?_eq_some_iff.mp hk').1
    rw [Array.size_pop] at hj
    refine ⟨hj, ?_⟩
    rw [Array.getElem?_pop] at hk'
    simpa [hj] using hk'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv, depth_append, depth_singleton, hstep, hind, hfl]; have := hI.bound; omega
  · rw [hv]; exact Bal_snoc_deep _ _ hI.bal (depth_pos_of_flow s hB hI hpos)
  · intro hp
    have hk' := hcur hp
    unfold DSlot
    rw [hv, hci, hfl]
    rw [take_append_of_le' _ _ _ (by have := stackLen s hA _ _ hk' hp; omega)]
    rcases hI.stack _ _ hk' hp with h | ⟨h0, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, Or.inl h⟩
  · intro j k hk' hp
    rw [hst] at hk'
    obtain ⟨_, hk'⟩ := hpopLt j k hk'
    rw [hv, hci, take_append_of_le' _ _ _ (by have := stackLen s hA j k hk' hp; omega)]
    exact hI.stack j k hk' hp
  · intro hp
    have hk' := hcur hp
    rw [hv]; exact PhAt_append _ _ _ (stackLen s hA _ _ hk' hp) (hI.stackPh _ _ hk' hp)
  · intro j k hk' hp
    rw [hst] at hk'
    obtain ⟨_, hk'⟩ := hpopLt j k hk'
    rw [hv]; exact PhAt_append _ _ _ (stackLen s hA j k hk' hp) (hI.stackPh j k hk' hp)
  · intro hp j k hk' hpj
    have hc := hcur hp
    rw [hst] at hk'
    obtain ⟨hj, hk'⟩ := hpopLt j k hk'
    exact hI.ordStk j _ k _ hk' hc hj hpj hp
  · intro j j' k k' hk hk' hlt hpj hpj'
    rw [hst] at hk hk'
    obtain ⟨_, hk⟩ := hpopLt j k hk
    obtain ⟨_, hk'⟩ := hpopLt j' k' hk'
    exact hI.ordStk j j' k k' hk hk' hlt hpj hpj'

lemma DInv_dispatchFlow (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s'))
    (hB : SentinelBase s) (hF : FlowSync s) (hS : StrongDSlot s) (hA : AllKeysValid s) (hI : DInv s) :
    DInv s' := by
  have hind := dispatchFlowIndicators_preserves_indents h
  unfold scanNextToken_dispatchFlowIndicators at h
  replace h := peel_flowAdj h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact DInv.flowStart s _ _ rfl rfl (scanFlowSequenceStart_vals s) (L4YAML.Proofs.ScannerContracts.scanFlowSequenceStart_flowLevel s)
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
            exact DInv.flowEnd s _ _ rfl (scanFlowSequenceEnd_vals s) hpos
              (scanFlowSequenceEnd_flowLevel_pos s hpos)
              (scanFlowSequenceEnd_simpleKey_restored s) (scanFlowSequenceEnd_stack_popped s) hind hB hF hA hI
    · split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact DInv.flowStart s _ _ rfl rfl (scanFlowMappingStart_vals s) (L4YAML.Proofs.ScannerContracts.scanFlowMappingStart_flowLevel s)
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
                exact DInv.flowEnd s _ _ rfl (scanFlowMappingEnd_vals s) hpos
                  (scanFlowMappingEnd_flowLevel_pos s hpos)
                  (scanFlowMappingEnd_simpleKey_restored s) (scanFlowMappingEnd_stack_popped s) hind hB hF hA hI
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
                have hv := scanFlowEntry_vals s _ h_entry
                refine DInv.clearedAppend s _ [.flowEntry] hv ?_ ?_
                  (scanFlowEntry_clears_simpleKey s _ h_entry)
                  (scanFlowEntry_preserves_simpleKeyStack s _ h_entry) (Or.inl (by simp [ScannerState.currentIndent, hind]))
                  (stackLen s hA) hI
                · rw [hv, depth_append, depth_singleton, hind,
                    ScannerFlowCollection.scanFlowEntry_preserves_flowLevel s _ h_entry]
                  have := hI.bound; simp only [depthStep]; omega
                · rw [hv]; exact Bal_snoc_deep _ _ hI.bal (depth_pos_of_flow s hB hI hpos)
          · simp at h


/-! ### Structural tokens -/

lemma StrongDSlot_of_eq {s t : ScannerState} (hS : StrongDSlot s) (hv : vals t = vals s)
    (hfl : t.flowLevel = s.flowLevel) (hci : t.currentIndent = s.currentIndent)
    (hk : t.simpleKey = s.simpleKey ∨ t.simpleKey.possible = false) : StrongDSlot t := by
  intro hp
  rcases hk with hk | hk
  · rw [hv, hfl, hci, hk]; exact hS (by rw [← hk]; exact hp)
  · rw [hk] at hp; cases hp

lemma DInv_scanDocumentStart (s : ScannerState) (hB : SentinelBase s) (hA : AllKeysValid s)
    (hI : DInv s) : DInv (scanDocumentStart s) := by
  obtain ⟨hv, _, _, hk, hst⟩ := scanDocumentStart_fields s
  have hIu := DInv_unwindIndents s (-1) (Int.le_refl _) hB hA hI
  have hAu := unwindIndents_preserves_AllKeysValid s (-1) hA
  have hind := scanDocumentStart_indents s
  have hfl : (scanDocumentStart s).flowLevel = (unwindIndents s (-1)).flowLevel := by
    rw [scanDocumentStart_preserves_flowLevel, unwindIndents_preserves_flowLevel]
  refine DInv.clearedAppend _ _ [.documentStart] hv ?_ ?_ hk
    (by rw [hst, unwindIndents_preserves_simpleKeyStack]) (Or.inl (by simp [ScannerState.currentIndent, hind]))
    (stackLen _ hAu) hIu
  · rw [hv, depth_append, depth_singleton, hind, hfl]; have := hIu.bound; simp only [depthStep]; omega
  · rw [hv]; exact Bal_snoc_live _ _ hIu.bal rfl

lemma DInv_scanDocumentEnd (s s' : ScannerState) (h : scanDocumentEnd s = .ok s')
    (hB : SentinelBase s) (hA : AllKeysValid s) (hI : DInv s) : DInv s' := by
  obtain ⟨hv, _, _, hind, hk, hst⟩ := scanDocumentEnd_fields s s' h
  have hIu := DInv_unwindIndents s (-1) (Int.le_refl _) hB hA hI
  have hAu := unwindIndents_preserves_AllKeysValid s (-1) hA
  have hfl : s'.flowLevel = (unwindIndents s (-1)).flowLevel := by
    rw [scanDocumentEnd_preserves_flowLevel s s' h, unwindIndents_preserves_flowLevel]
  refine DInv.clearedAppend _ _ [.documentEnd] hv ?_ ?_ hk
    (by rw [hst, unwindIndents_preserves_simpleKeyStack]) (Or.inl (by simp [ScannerState.currentIndent, hind]))
    (stackLen _ hAu) hIu
  · rw [hv, depth_append, depth_singleton, hind, hfl]; have := hIu.bound; simp only [depthStep]; omega
  · rw [hv]; exact Bal_snoc_live _ _ hIu.bal rfl

lemma DInv_scanDirective (s s' : ScannerState) (h : scanDirective s = .ok s')
    (hS : StrongDSlot s) (hA : AllKeysValid s) (hI : DInv s) : DInv s' := by
  obtain ⟨hv, _, _⟩ := scanDirective_fields s s' h
  have hind := scanDirective_preserves_indents h
  have hfl := scanDirective_preserves_flowLevel s s' h
  have hci : s'.currentIndent = s.currentIndent := by simp [ScannerState.currentIndent, hind]
  rcases hv with hv | ⟨d, hv, hd⟩
  · exact DInv.extStrong s s' hI hS hA [] (by rw [hv]; simp) (by rw [hv, hind, hfl]; exact hI.bound)
      (by rw [hv]; exact hI.bal) hfl (Or.inl (Int.le_of_eq hci))
      (KeyTr.ofEq (scanDirective_preserves_simpleKey s s' h)) (scanDirective_preserves_simpleKeyStack s s' h)
  · have hd0 : depthStep d = 0 ∧ structDead d = false := by
      cases d <;> simp [isDirTok] at hd <;> exact ⟨rfl, rfl⟩
    exact DInv.extStrong s s' hI hS hA [d] hv
      (by rw [hv, depth_append, depth_singleton, hd0.1, hind, hfl]; have := hI.bound; omega)
      (by rw [hv]; exact Bal_snoc_live _ _ hI.bal hd0.2) hfl (Or.inl (Int.le_of_eq hci))
      (KeyTr.ofEq (scanDirective_preserves_simpleKey s s' h)) (scanDirective_preserves_simpleKeyStack s s' h)

lemma DInv_dispatchStructural (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s'))
    (hS : StrongDSlot s) (hB : SentinelBase s) (hA : AllKeysValid s) (hI : DInv s) : DInv s' := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact DInv_scanDocumentStart s hB hA hI
    | exact DInv_scanDocumentEnd _ _ (by assumption) hB hA hI
    | exact DInv_scanDirective _ _ (by assumption) hS hA hI

/-! ### Block indicators -/

lemma pushMappingIndent_simpleKey (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).simpleKey = s.simpleKey := by
  unfold pushMappingIndent; split <;> rfl

lemma pushSequenceIndent_cases (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col = s ∧ col ≤ s.currentIndent) ∨
    (vals (pushSequenceIndent s col) = vals s ++ [.blockSequenceStart] ∧
      (pushSequenceIndent s col).indents.size = s.indents.size + 1 ∧ s.currentIndent < col) := by
  unfold pushSequenceIndent
  split
  · right; refine ⟨by simp [vals, toks, ScannerState.emit], by simp [ScannerState.emit], by omega⟩
  · left; exact ⟨rfl, by omega⟩

lemma pushMappingIndent_cases (s : ScannerState) (col : Int) :
    (pushMappingIndent s col = s ∧ col ≤ s.currentIndent) ∨
    (vals (pushMappingIndent s col) = vals s ++ [.blockMappingStart] ∧
      (pushMappingIndent s col).indents.size = s.indents.size + 1 ∧ s.currentIndent < col) := by
  unfold pushMappingIndent
  split
  · right; refine ⟨by simp [vals, toks, ScannerState.emit], by simp [ScannerState.emit], by omega⟩
  · left; exact ⟨rfl, by omega⟩

/-- More than the sentinel is on the stack once the indent is non-negative. -/
lemma indents_gt_one_of_ci (s : ScannerState) (hB : SentinelBase s) (hci : 0 ≤ s.currentIndent) :
    1 < s.indents.size := by
  rcases Nat.lt_or_ge 1 s.indents.size with h | h
  · exact h
  · exfalso; have := hB.currentIndent_of_size_le_one h; omega

lemma DInv_scanBlockEntry (s s' : ScannerState) (h : scanBlockEntry s = .ok s')
    (hnf : s.inFlow = false) (hF : FlowSync s) (hS : StrongDSlot s) (hA : AllKeysValid s)
    (hI : DInv s) : DInv s' := by
  have hfl0 : s.flowLevel = 0 := by
    unfold ScannerState.inFlow at hnf; simpa using hnf
  have hsz : s.simpleKeyStack.size = 0 := by have := hF.1; have := hF.2; omega
  have hv0 : vals s' = vals (pushSequenceIndent s s.col) ++ [.blockEntry] := by
    rw [← vals_emit]; show toks s'.tokens = toks _; rw [scanBlockEntry_tokens s s' h]; simp [hnf]
  have hind := scanBlockEntry_indents hnf h
  have hfl' := scanBlockEntry_preserves_flowLevel s s' h
  have hk := scanBlockEntry_preserves_simpleKey s s' h
  have hst := scanBlockEntry_preserves_simpleKeyStack s s' h
  have hal' : s'.simpleKeyAllowed = true := scanBlockEntry_simpleKeyAllowed h
  have hnn := Bal_depth_nonneg _ hI.bal
  rcases pushSequenceIndent_cases s s.col with ⟨hp, _⟩ | ⟨hp, hsz', _⟩
  · rw [hp] at hv0 hind
    exact DInv.extStrong s s' hI hS hA [.blockEntry] hv0
      (by rw [hv0, depth_append, depth_singleton, hind, hfl']; have := hI.bound; simp only [depthStep]; omega)
      (by rw [hv0]; exact Bal_snoc_live _ _ hI.bal rfl) hfl' (Or.inr ⟨hal', hsz⟩) (KeyTr.ofEq hk) hst
  · have hv : vals s' = vals s ++ [.blockSequenceStart, .blockEntry] := by
      rw [hv0, hp, List.append_assoc]; rfl
    have hd2 : depth [YamlToken.blockSequenceStart, .blockEntry] = 1 := by decide
    exact DInv.extStrong s s' hI hS hA _ hv
      (by rw [hv, depth_append, hind, hsz', hfl', hd2]; have := hI.bound; push_cast; omega)
      (by rw [hv]; exact Bal_append_live _ _ hI.bal (fun t ht => by simp at ht; rcases ht with rfl | rfl <;> rfl))
      hfl' (Or.inr ⟨hal', hsz⟩) (KeyTr.ofEq hk) hst

lemma DInv_scanKey (s s' : ScannerState) (h : scanKey s = .ok s')
    (hB : SentinelBase s) (hF : FlowSync s) (hA : AllKeysValid s) (hI : DInv s) : DInv s' := by
  have hv0 : vals s' = vals (if !s.inFlow then pushMappingIndent s s.col else s) ++ [.key] := by
    rw [← vals_emit]; show toks s'.tokens = toks _; rw [scanKey_tokens s s' h]
  have hk := scanKey_clears_simpleKey s s' h
  have hst := scanKey_preserves_simpleKeyStack s s' h
  have hfl' := scanKey_preserves_flowLevel s s' h
  have hnn := Bal_depth_nonneg _ hI.bal
  cases hin : s.inFlow with
  | true =>
    have hpos : 0 < s.flowLevel := by unfold ScannerState.inFlow at hin; simpa using hin
    have hind := scanKey_indents_of_inFlow hin h
    simp only [hin, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hv0
    refine DInv.clearedAppend s s' [.key] hv0 ?_ ?_ hk hst (Or.inl (by simp [ScannerState.currentIndent, hind]))
      (stackLen s hA) hI
    · rw [hv0, depth_append, depth_singleton, hind, hfl']; have := hI.bound; simp only [depthStep]; omega
    · rw [hv0]; exact Bal_snoc_deep _ _ hI.bal (depth_pos_of_flow s hB hI hpos)
  | false =>
    have hfl0 : s.flowLevel = 0 := by unfold ScannerState.inFlow at hin; simpa using hin
    have hsz : s.simpleKeyStack.size = 0 := by have := hF.1; have := hF.2; omega
    have hind := scanKey_indents hin h
    simp only [hin, Bool.not_false, ↓reduceIte] at hv0
    rcases pushMappingIndent_cases s s.col with ⟨hp, hle⟩ | ⟨hp, hsz', _⟩
    · rw [hp] at hv0 hind
      have hgt : 1 < s.indents.size := indents_gt_one_of_ci s hB (by omega)
      refine DInv.clearedAppend s s' [.key] hv0 ?_ ?_ hk hst (Or.inr hsz) (stackLen s hA) hI
      · rw [hv0, depth_append, depth_singleton, hind, hfl']; have := hI.bound; simp only [depthStep]; omega
      · rw [hv0]; exact Bal_snoc_deep _ _ hI.bal (depth_pos_of_indents s hI hgt)
    · have hv : vals s' = vals s ++ [.blockMappingStart, .key] := by
        rw [hv0, hp, List.append_assoc]; rfl
      have hd2 : depth [YamlToken.blockMappingStart, .key] = 1 := by decide
      refine DInv.clearedAppend s s' _ hv ?_ ?_ hk hst (Or.inr hsz) (stackLen s hA) hI
      · rw [hv, depth_append, hind, hsz', hfl', hd2]; have := hI.bound; push_cast; omega
      · rw [hv, ← List.singleton_append, ← List.append_assoc]
        exact Bal_snoc_deep _ _ (Bal_snoc_live _ _ hI.bal rfl)
          (by rw [depth_append, depth_singleton]; simp only [depthStep]; omega)


/-! ### `scanValue`: the retroactive key insertion -/

lemma getElem?_take_lt (L : List YamlToken) (i n : Nat) (h : i < n) : (L.take n)[i]? = L[i]? := by
  rw [List.getElem?_take]; simp [h]

/-- `scanValuePrepare` keeps the carrier, clears the key, and leaves the output at positive depth
    (the `.value` that follows is dead). -/
lemma DInv_prepare (s1 : ScannerState) (hval : scanValueValidate s1 = .ok ())
    (hB : SentinelBase s1) (hsz : s1.simpleKeyStack.size = s1.flowLevel) (hS : StrongDSlot s1)
    (hA : AllKeysValid s1) (hI : DInv s1) :
    DInv (scanValuePrepare s1) ∧ 0 < depth (vals (scanValuePrepare s1)) ∧
    (scanValuePrepare s1).simpleKey.possible = false ∧
    (vals s1).length ≤ (vals (scanValuePrepare s1)).length := by
  have hnn := Bal_nonneg _ hI.bal
  have hnn0 := Bal_depth_nonneg _ hI.bal
  have hstEmpty : s1.flowLevel = 0 → ∀ (j : Nat) (k : SimpleKeyState) {P : Prop},
      s1.simpleKeyStack[j]? = some k → P := by
    intro h0 j k P hk
    exfalso; have := (Array.getElem?_eq_some_iff.mp hk).1; omega
  unfold scanValuePrepare
  split
  · rename_i hp
    have hph := hI.ph hp
    have hlt := keyLen s1 hA hp
    have hkey0 : depthStep YamlToken.key = 0 := rfl
    have hbms1 : depthStep YamlToken.blockMappingStart = 1 := rfl
    split
    · rename_i hnf
      have hfl0 : s1.flowLevel = 0 := by
        have := hnf; simp [ScannerState.inFlow] at this; omega
      split
      · rename_i hgt
        -- Case A: `blockMappingStart` and `key` written into the slot, a mapping indent pushed
        have hv : vals ({ s1 with
            tokens := (s1.tokens.setIfInBounds s1.simpleKey.tokenIndex
                ⟨s1.simpleKey.pos, .blockMappingStart, s1.simpleKey.pos⟩).setIfInBounds
                (s1.simpleKey.tokenIndex + 1) ⟨s1.simpleKey.pos, .key, s1.simpleKey.pos⟩,
            indents := s1.indents.push { column := (s1.simpleKey.pos.col : Int), isSequence := false },
            pendingKeys := s1.pendingKeys.push none, simpleKey := { possible := false } } : ScannerState) =
            ((vals s1).set s1.simpleKey.tokenIndex .blockMappingStart).set (s1.simpleKey.tokenIndex + 1) .key := by
          simp only [vals, DirectiveRuns.toks_setIfInBounds]
        have hph1 : ((vals s1).set s1.simpleKey.tokenIndex .blockMappingStart)[s1.simpleKey.tokenIndex + 1]? =
            some .placeholder := by
          rw [List.getElem?_set_ne (by omega)]; exact hph.2
        have hdep : depth (((vals s1).set s1.simpleKey.tokenIndex .blockMappingStart).set
            (s1.simpleKey.tokenIndex + 1) .key) = depth (vals s1) + 1 := by
          rw [depth_set _ _ _ hph1, depth_set _ _ _ hph.1, hkey0, hbms1]; omega
        have hbal : Bal (((vals s1).set s1.simpleKey.tokenIndex .blockMappingStart).set
            (s1.simpleKey.tokenIndex + 1) .key) := by
          have h1 : depth (((vals s1).set s1.simpleKey.tokenIndex .blockMappingStart).take
              (s1.simpleKey.tokenIndex + 1)) = depth ((vals s1).take (s1.simpleKey.tokenIndex + 1)) + 1 := by
            rw [take_set_of_lt _ _ _ _ (Nat.lt_succ_self _), depth_set _ _ _ (by
              rw [getElem?_take_lt _ _ _ (Nat.lt_succ_self _)]; exact hph.1), hbms1]
          refine Bal_set _ _ _ (Bal_set _ _ _ hI.bal hph.1 (by rw [hbms1]; decide) (fun h => by cases h))
            hph1 (by rw [hkey0]; exact Int.le_refl _) (fun _ => ?_)
          rw [h1]; have := hnn (s1.simpleKey.tokenIndex + 1); omega
        refine ⟨⟨?_, ?_, fun h => absurd h Bool.false_ne_true, fun j k hk => hstEmpty hfl0 j k hk,
          fun h => absurd h Bool.false_ne_true, fun j k hk => hstEmpty hfl0 j k hk,
          fun h => absurd h Bool.false_ne_true, fun j _ k _ hk _ _ _ _ => hstEmpty hfl0 j k hk⟩, ?_, rfl, ?_⟩
        · show ((s1.indents.push _).size : Int) - 1 + (s1.flowLevel : Int) ≤ depth _
          rw [hv, hdep, Array.size_push]; have := hI.bound; push_cast; omega
        · show Bal (vals _); rw [hv]; exact hbal
        · show 0 < depth (vals _); rw [hv, hdep]; omega
        · show (vals s1).length ≤ (vals _).length; rw [hv, List.length_set, List.length_set]; exact Nat.le_refl _
      · rename_i hle
        -- Case B: only the `key` is written; the mapping is already open
        have hv : vals ({ s1 with
            tokens := s1.tokens.setIfInBounds (s1.simpleKey.tokenIndex + 1)
              ⟨s1.simpleKey.pos, .key, s1.simpleKey.pos⟩, simpleKey := { possible := false } } : ScannerState) =
            (vals s1).set (s1.simpleKey.tokenIndex + 1) .key := by
          simp only [vals, DirectiveRuns.toks_setIfInBounds]
        have hdep : depth ((vals s1).set (s1.simpleKey.tokenIndex + 1) .key) = depth (vals s1) := by
          rw [depth_set _ _ _ hph.2, hkey0]; omega
        have hpre : 0 < depth ((vals s1).take (s1.simpleKey.tokenIndex + 1)) := by
          rcases hS hp with h | ⟨_, h | h⟩
          · exact h
          · exfalso; omega
          · cases h
        have hgt : 1 < s1.indents.size := indents_gt_one_of_ci s1 hB (by omega)
        refine ⟨⟨?_, ?_, fun h => absurd h Bool.false_ne_true, fun j k hk => hstEmpty hfl0 j k hk,
          fun h => absurd h Bool.false_ne_true, fun j k hk => hstEmpty hfl0 j k hk,
          fun h => absurd h Bool.false_ne_true, fun j _ k _ hk _ _ _ _ => hstEmpty hfl0 j k hk⟩, ?_, rfl, ?_⟩
        · show (s1.indents.size : Int) - 1 + (s1.flowLevel : Int) ≤ depth _
          rw [hv, hdep]; exact hI.bound
        · show Bal (vals _); rw [hv]
          exact Bal_set _ _ _ hI.bal hph.2 (by rw [hkey0]; exact Int.le_refl _) (fun _ => hpre)
        · show 0 < depth (vals _); rw [hv, hdep]; have := hI.bound; omega
        · show (vals s1).length ≤ (vals _).length; rw [hv, List.length_set]; exact Nat.le_refl _
    · rename_i hin
      -- Case C: in flow, only the `key` is written
      have hpos : 0 < s1.flowLevel := by
        have := hin; simp [ScannerState.inFlow] at this; omega
      have hv : vals ({ s1 with
          tokens := s1.tokens.setIfInBounds (s1.simpleKey.tokenIndex + 1)
            ⟨s1.simpleKey.pos, .key, s1.simpleKey.pos⟩, simpleKey := { possible := false } } : ScannerState) =
          (vals s1).set (s1.simpleKey.tokenIndex + 1) .key := by
        simp only [vals, DirectiveRuns.toks_setIfInBounds]
      have hdep : depth ((vals s1).set (s1.simpleKey.tokenIndex + 1) .key) = depth (vals s1) := by
        rw [depth_set _ _ _ hph.2, hkey0]; omega
      have hpre : 0 < depth ((vals s1).take (s1.simpleKey.tokenIndex + 1)) := by
        rcases hS hp with h | ⟨h0, _⟩
        · exact h
        · omega
      refine ⟨⟨?_, ?_, fun h => absurd h Bool.false_ne_true, ?_, fun h => absurd h Bool.false_ne_true, ?_,
        fun h => absurd h Bool.false_ne_true, ?_⟩, ?_, rfl, ?_⟩
      · show (s1.indents.size : Int) - 1 + (s1.flowLevel : Int) ≤ depth _
        rw [hv, hdep]; exact hI.bound
      · show Bal (vals _); rw [hv]
        exact Bal_set _ _ _ hI.bal hph.2 (by rw [hkey0]; exact Int.le_refl _) (fun _ => hpre)
      · intro j k hk hpk
        have hord := hI.ordCur hp j k hk hpk
        show 0 < depth ((vals _).take (k.tokenIndex + 1)) ∨ (j = 0 ∧ s1.currentIndent < (k.pos.col : Int))
        rw [hv, take_set_of_le _ _ _ _ (by omega)]
        exact hI.stack j k hk hpk
      · intro j k hk hpk
        have hord := hI.ordCur hp j k hk hpk
        show PhAt (vals _) k.tokenIndex
        rw [hv]; exact PhAt_set_lt _ _ _ _ (by omega) (hI.stackPh j k hk hpk)
      · intro j j' k k' hk hk' hlt hpj hpj'
        exact hI.ordStk j j' k k' hk hk' hlt hpj hpj'
      · show 0 < depth (vals _); rw [hv, hdep]; exact depth_pos_of_flow s1 hB hI hpos
      · show (vals s1).length ≤ (vals _).length; rw [hv, List.length_set]; exact Nat.le_refl _
  · rename_i hnp
    have hnp' : s1.simpleKey.possible = false := by simpa using hnp
    split
    · rename_i hek
      -- Case D: explicit value; the `:` sits at the mapping's indent
      have hv : vals ({ s1 with simpleKey := { possible := false } } : ScannerState) = vals s1 := rfl
      have hpos : 0 < depth (vals s1) := by
        cases hin : s1.inFlow with
        | true => exact depth_pos_of_flow s1 hB hI (by unfold ScannerState.inFlow at hin; simpa using hin)
        | false =>
          have hcol := scanValueValidate_explicit_col hnp' hin hek hval
          exact depth_pos_of_indents s1 hI (indents_gt_one_of_ci s1 hB (by omega))
      refine ⟨DInv.clearedAppend s1 _ [] (by rw [hv]; simp) ?_ ?_ rfl rfl (Or.inl (Int.le_refl _))
        (stackLen s1 hA) hI, ?_, rfl, ?_⟩
      · show (s1.indents.size : Int) - 1 + (s1.flowLevel : Int) ≤ depth (vals s1); exact hI.bound
      · show Bal (vals s1); exact hI.bal
      · show 0 < depth (vals s1); exact hpos
      · show (vals s1).length ≤ (vals s1).length; exact Nat.le_refl _
    · -- Case E: no key, no explicit key: a fresh mapping at the `:`
      split
      · rename_i hnf
        have hfl0 : s1.flowLevel = 0 := by
          have := hnf; simp [ScannerState.inFlow] at this; omega
        have hkP : (pushMappingIndent s1 s1.col).simpleKey.possible = false := by
          rw [pushMappingIndent_simpleKey]; exact hnp'
        rcases pushMappingIndent_cases s1 s1.col with ⟨hp, hle⟩ | ⟨hv, hsz', hgt⟩
        · rw [hp]
          have hgt : 1 < s1.indents.size := indents_gt_one_of_ci s1 hB (by omega)
          exact ⟨hI, depth_pos_of_indents s1 hI hgt, hnp', Nat.le_refl _⟩
        · refine ⟨DInv.clearedAppend s1 _ [.blockMappingStart] hv ?_ ?_ hkP
            (by unfold pushMappingIndent; split <;> rfl) (Or.inr (by omega)) (stackLen s1 hA) hI, ?_, hkP, ?_⟩
          · rw [hv, depth_append, depth_singleton, hsz']
            rw [show (pushMappingIndent s1 s1.col).flowLevel = s1.flowLevel from by
              unfold pushMappingIndent; split <;> rfl]
            have := hI.bound; simp only [depthStep]; push_cast; omega
          · rw [hv]; exact Bal_snoc_live _ _ hI.bal rfl
          · rw [hv, depth_append, depth_singleton]; simp only [depthStep]; omega
          · rw [hv, List.length_append]; omega
      · exact ⟨hI, depth_pos_of_flow s1 hB hI (by
          rename_i hin; have := hin; simp [ScannerState.inFlow] at this; omega),
          hnp', Nat.le_refl _⟩

lemma DInv_scanValue (s s' : ScannerState) (h : scanValue s = .ok s')
    (hB : SentinelBase s) (hF : FlowSync s) (hS : StrongDSlot s) (hA : AllKeysValid s) (hI : DInv s) :
    DInv s' := by
  obtain ⟨hval, hv, hind⟩ := scanValue_unfold s s' h
  have ht1 := scanValueClearKey_preserves_tokens s
  have hc1 := L4YAML.Proofs.PendingKeySound.scanValueClearKey_core s
  have hst1 := scanValueClearKey_preserves_simpleKeyStack s
  have hk1 := scanValueClearKey_simpleKey s
  have hal1 := scanValueClearKey_simpleKeyAllowed s
  have hv1 : vals (scanValueClearKey s) = vals s := by simp [vals, ht1]
  have hci1 : (scanValueClearKey s).currentIndent = s.currentIndent := by
    simp [ScannerState.currentIndent, hc1.1]
  have hI1 : DInv (scanValueClearKey s) :=
    DInv.ofFields s _ hI hA ht1 hc1.1 hc1.2.2.1 (by rw [hal1]; exact id)
      (fun hp => by
        rcases hk1 with hk1 | hk1
        · exact KeyTr.ofEq hk1 hp
        · rw [hk1] at hp; cases hp) hst1
  have hA1 : AllKeysValid (scanValueClearKey s) := by
    rcases scanValueClearKey_identity_or_clear s with e | ⟨hk, ht⟩
    · rw [e]; exact hA
    · exact AllKeysValid_of_clear s _ ht hst1 hk hA
  have hS1 : StrongDSlot (scanValueClearKey s) := StrongDSlot_of_eq hS hv1 hc1.2.2.1 hci1 hk1
  have hB1 : SentinelBase (scanValueClearKey s) := hB.of_indents_eq hc1.1
  have hsz1 : (scanValueClearKey s).simpleKeyStack.size = (scanValueClearKey s).flowLevel := by
    rw [hst1, hc1.2.2.1]; have := hF.1; have := hF.2; omega
  have hst' : s'.simpleKeyStack = (scanValueClearKey s).simpleKeyStack := by
    rw [scanValue_preserves_simpleKeyStack s s' h, hst1]
  have hfl' : s'.flowLevel = (scanValueClearKey s).flowLevel := by
    rw [scanValue_preserves_flowLevel s s' h, hc1.2.2.1]
  have hk' := scanValue_clears_simpleKey s s' h
  generalize scanValueClearKey s = s1 at *
  obtain ⟨hIP, hposP, _, hlenP⟩ := DInv_prepare s1 hval hB1 hsz1 hS1 hA1 hI1
  have hstP := scanValuePrepare_preserves_simpleKeyStack s1
  have hflP := scanValuePrepare_preserves_flowLevel s1
  refine DInv.clearedAppend _ s' [.value] hv ?_ ?_ hk' (by rw [hst', hstP])
    (Or.inl (by simp [ScannerState.currentIndent, hind])) ?_ hIP
  · rw [hv, depth_append, depth_singleton, hind, hfl', ← hflP]; have := hIP.bound; simp only [depthStep]; omega
  · rw [hv]; exact Bal_snoc_deep _ _ hIP.bal hposP
  · intro j k hk hpk
    rw [hstP] at hk
    have := stackLen s1 hA1 j k hk hpk; omega

lemma DInv_dispatchBlock (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (hB : SentinelBase s) (hF : FlowSync s) (hS : StrongDSlot s) (hA : AllKeysValid s) (hI : DInv s) :
    DInv s' := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact DInv_scanBlockEntry s _ (by assumption) (by simp_all) hF hS hA hI
    | exact DInv_scanKey s _ (by assumption) hB hF hA hI
    | exact DInv_scanValue s _ (by assumption) hB hF hS hA hI

/-! ### Content tokens -/

lemma liveTok_neutral (t : YamlToken) (h : liveTok t = true) : structDead t = false ∧ 0 ≤ depthStep t := by
  cases t <;> simp [liveTok] at h <;> exact ⟨rfl, by simp [depthStep]⟩

lemma DInv_dispatchContent (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s')
    (hS : StrongDSlot s) (hA : AllKeysValid s) (hI : DInv s) : DInv s' := by
  obtain ⟨⟨t, hv, hlive, _⟩, hkey⟩ := dispatchContent_live s c s' h
  have hind := L4YAML.Proofs.IndentStackBase.dispatchContent_preserves_indents h
  have hfl := dispatchContent_preserves_flowLevel s c s' h
  have ht := liveTok_neutral t hlive
  exact DInv.extStrong s s' hI hS hA [t] hv
    (by rw [hv, depth_append, depth_singleton, hind, hfl]; have := hI.bound; omega)
    (by rw [hv]; exact Bal_snoc_live _ _ hI.bal ht.1) hfl
    (Or.inl (by simp [ScannerState.currentIndent, hind])) hkey
    (dispatchContent_preserves_simpleKeyStack s c s' h)

/-! ### One step, the loop, and the scanner entry points -/

lemma DInv_scanNextToken (s s' : ScannerState) (hA : AllKeysValid s)
    (hB : SentinelBase s) (hF : FlowSync s) (hI : DInv s)
    (h : scanNextToken s = .ok (some s')) : DInv s' := by
  unfold scanNextToken at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  rename_i s2 c h_pre
  have hA2 := preprocess_preserves_AllKeysValid s s2 c h_pre hA
  have hB2 := preprocess_base h_pre hB
  have hF2 := FlowSync_preprocess s s2 c h_pre hF
  obtain ⟨hI2, hS2⟩ := DInv_preprocess s s2 c h_pre hB hA hI
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact DInv_dispatchStructural s2 c _ (by assumption) hS2 hB2 hA2 hI2
  · split at h <;> (try (simp at h; done))
    split at h <;> (try (simp at h; done))
    have hA3 := allowDir_ite_preserves_AllKeysValid s2 hA2
    have hI3 : DInv (if s2.allowDirectives = true then
        { s2 with allowDirectives := false, documentEverStarted := true } else s2) := by
      split
      · exact DInv.ofFields s2 _ hI2 hA2 rfl rfl rfl (fun h => h) (KeyTr.ofEq rfl) rfl
      · exact hI2
    have hS3 : StrongDSlot (if s2.allowDirectives = true then
        { s2 with allowDirectives := false, documentEverStarted := true } else s2) := by
      split
      · exact StrongDSlot_of_eq hS2 rfl rfl rfl (Or.inl rfl)
      · exact hS2
    have hF3 : FlowSync (if s2.allowDirectives = true then
        { s2 with allowDirectives := false, documentEverStarted := true } else s2) := by
      split
      · exact ⟨hF2.1, hF2.2⟩
      · exact hF2
    have hB3 : SentinelBase (if s2.allowDirectives = true then
        { s2 with allowDirectives := false, documentEverStarted := true } else s2) := by
      split
      · exact hB2.of_indents_eq rfl
      · exact hB2
    split at h <;> (try (simp at h; done))
    split at h
    · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
      exact DInv_dispatchFlow _ c _ (by assumption) hB3 hF3 hS3 hA3 hI3
    · split at h <;> (try (simp at h; done))
      split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact DInv_dispatchBlock _ c _ (by assumption) hB3 hF3 hS3 hA3 hI3
      · split at h <;> (try (simp at h; done))
        split at h <;> (try (simp at h; done))
        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact DInv_dispatchContent _ c _ (by assumption) hS3 hA3 hI3

lemma DInv_scanLoop : ∀ (fuel : Nat) (s : ScannerState) (ts : Array (Positioned YamlToken)),
    AllKeysValid s → SentinelBase s → FlowSync s → DInv s →
    scanLoop s fuel = .ok ts → Bal (toks ts) := by
  intro fuel
  induction fuel with
  | zero => intro s ts _ _ _ _ h; simp [scanLoop] at h
  | succ n ih =>
    intro s ts hA hB hF hI h
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
              have hI' := DInv_unwindIndents s (-1) (Int.le_refl _) hB hA hI
              show Bal (vals ((unwindIndents s (-1)).emit .streamEnd))
              rw [vals_emit]
              exact Bal_snoc_live _ _ hI'.bal rfl
    · rename_i s' hs'
      exact ih s' ts (scanNextToken_preserves_AllKeysValid s s' hA hs')
        (scanNextToken_base hs' hB) (FlowSync_scanNextToken s s' hF hs')
        (DInv_scanNextToken s s' hA hB hF hI hs') h

lemma DInv_init (input : String) : DInv ((ScannerState.mk' input).emit .streamStart) where
  bound := by simp [vals, toks, ScannerState.mk', ScannerState.emit, depth, depthStep]
  bal := by
    have hv : vals ((ScannerState.mk' input).emit .streamStart) = [.streamStart] := by
      simp [vals, toks, ScannerState.mk', ScannerState.emit]
    rw [hv]; intro i t hi hd
    cases i with
    | zero => simp at hi; subst hi; simp [structDead] at hd
    | succ i => simp at hi
  slot := by intro hp; simp [ScannerState.mk', ScannerState.emit] at hp
  stack := by intro j k hk; simp [ScannerState.mk', ScannerState.emit] at hk
  ph := by intro hp; simp [ScannerState.mk', ScannerState.emit] at hp
  stackPh := by intro j k hk; simp [ScannerState.mk', ScannerState.emit] at hk
  ordCur := by intro hp; simp [ScannerState.mk', ScannerState.emit] at hp
  ordStk := by intro j j' k k' hk; simp [ScannerState.mk', ScannerState.emit] at hk

lemma StrongDSlot_init (input : String) : StrongDSlot ((ScannerState.mk' input).emit .streamStart) := by
  intro hp; simp [ScannerState.mk', ScannerState.emit] at hp

lemma DInv_consumeBOM (s : ScannerState) (hA : AllKeysValid s) (hS : StrongDSlot s) (hI : DInv s) :
    DInv s.consumeBOM := by
  have hv : vals s.consumeBOM = vals s := by simp [vals, consumeBOM_preserves_tokens]
  have hind := consumeBOM_indents s
  exact DInv.extStrong s _ hI hS hA [] (by rw [hv]; simp)
    (by rw [hv, hind, consumeBOM_preserves_flowLevel]; exact hI.bound) (by rw [hv]; exact hI.bal)
    (consumeBOM_preserves_flowLevel s) (Or.inl (by simp [ScannerState.currentIndent, hind]))
    (KeyTr.ofEq (consumeBOM_preserves_simpleKey s)) (consumeBOM_preserves_simpleKeyStack s)

/-- Raw scanner output (placeholders included): every structural dead token sits at positive
    depth. -/
lemma scan_bal (input : String) (ts : Array (Positioned YamlToken)) (h : scan input = .ok ts) :
    Bal (toks ts) := by
  unfold scan at h
  have hA0 := AllKeysValid_init input
  have hB0 := SentinelBase_init input
  have hF0 := FlowSync_init input
  have hI0 := DInv_init input
  dsimp only at h
  split at h
  · have h_tok := consumeBOM_preserves_tokens ((ScannerState.mk' input).emit .streamStart)
    exact DInv_scanLoop _ _ ts
      (AllKeysValid_mono _ _ hA0 (consumeBOM_preserves_simpleKey _)
        (consumeBOM_preserves_simpleKeyStack _) (by simp [h_tok]) (fun i hi => by simp [h_tok]))
      (SentinelBase_consumeBOM _ hB0) (FlowSync_consumeBOM _ hF0)
      (DInv_consumeBOM _ hA0 (StrongDSlot_init input) hI0) h
  · exact DInv_scanLoop _ _ ts hA0 hB0 hF0 hI0 h

/-! ### Through the placeholder filter -/

lemma Bal_snoc_iff (L : List YamlToken) (t : YamlToken) :
    Bal (L ++ [t]) ↔ Bal L ∧ (structDead t = true → 0 < depth L) := by
  constructor
  · intro h
    refine ⟨fun i u hi hd => ?_, fun hd => ?_⟩
    · have hlt : i < L.length := (List.getElem?_eq_some_iff.mp hi).1
      have := h i u (by rw [List.getElem?_append_left hlt]; exact hi) hd
      rwa [List.take_append_of_le_length (Nat.le_of_lt hlt)] at this
    · have := h L.length t (by rw [List.getElem?_append_right (Nat.le_refl _)]; simp) hd
      rwa [List.take_append_of_le_length (Nat.le_refl _), List.take_length] at this
  · rintro ⟨hL, hd⟩
    exact Bal_append L [t] hL (fun i u hi hdu => by
      cases i with
      | zero => simp at hi; subst hi; simpa using hd hdu
      | succ i => simp at hi)

lemma depth_filter (p : YamlToken → Bool) (hp : ∀ t, p t = false → depthStep t = 0) :
    ∀ L : List YamlToken, depth (L.filter p) = depth L := by
  refine snoc_ind' (by simp) ?_
  intro L t ih
  rw [List.filter_append, depth_append, depth_append, depth_singleton]
  cases hpt : p t with
  | true => simp [List.filter_cons, hpt, ih]
  | false => simp [List.filter_cons, hpt, ih, hp t hpt]

lemma Bal_filter (p : YamlToken → Bool)
    (hp : ∀ t, p t = false → depthStep t = 0 ∧ structDead t = false) :
    ∀ L : List YamlToken, Bal L → Bal (L.filter p) := by
  refine snoc_ind' (fun _ => Bal_nil) ?_
  intro L t ih hB
  rw [Bal_snoc_iff] at hB
  rw [List.filter_append]
  cases hpt : p t with
  | true =>
    simp only [List.filter_cons, hpt, List.filter_nil, ite_true]
    rw [Bal_snoc_iff]
    exact ⟨ih hB.1, fun hd => by rw [depth_filter p (fun t ht => (hp t ht).1)]; exact hB.2 hd⟩
  | false => simp only [List.filter_cons, hpt, List.filter_nil, Bool.false_eq_true, ite_false, List.append_nil]; exact ih hB.1

/-- (γ1): on filtered scanner output every `.key` / `.value` / `.blockEnd` / `.flowEntry` /
    `.flowSequenceEnd` / `.flowMappingEnd` sits at positive structural depth. -/
lemma scanFiltered_bal (input : String) (ts : Array (Positioned YamlToken))
    (h : scanFiltered input = .ok ts) : Bal (toks ts) := by
  unfold scanFiltered at h
  split at h
  · rename_i ts0 h0
    simp only [Except.ok.injEq] at h; subst h
    rw [toks_filter]
    exact Bal_filter nonPh (fun t ht => by cases t <;> simp [nonPh] at ht <;> exact ⟨rfl, rfl⟩) _
      (scan_bal input ts0 h0)
  · contradiction

end L4YAML.Proofs.StructDepth
