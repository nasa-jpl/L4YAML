/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Spec.Grammar
import L4YAML.Parser.Composition
import L4YAML.Proofs.Parser.ParserGrammableBase
import L4YAML.Parser.ParseStateIx
import L4YAML.Parser.FuelIx
import L4YAML.Parser.TokenParserIx

/-! # `IndexedNodeProofs` — Phase 3 Step 6c indexed AG + AAR proofs (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 Step 6f cutover commit.

## Role

Indexed twin of `L4YAML/Proofs/Parser/ParserNodeProofs.lean`: the
`AG` (AnchorsGrow) and `AAR` (AllAliasesResolve) propagation proofs
reparented onto `ParseStateIx input` and the indexed `parseNode`
in `L4YAML.TokenParser.Indexed`.

The proofs reason about the *parser structure* (which is identical
between the legacy and indexed parsers — only the token-container
type changed); none of the `AG`/`AAR` lemmas touch `ps.tokens`
directly, so the translation is purely a substitution of the state
type and the namespace under which `parseNode` / `parseBlockSequence`
/ … are resolved.

## Phase 3 Step 6f cutover

At cutover, this file is renamed to `Proofs/Parser/ParserNodeProofs.lean`
(overwriting the legacy file) and the namespace
`L4YAML.Proofs.Indexed.NodeProofs` reverts to
`L4YAML.Proofs.ParserNodeProofs`.
-/

set_option autoImplicit false
open L4YAML L4YAML.Grammar L4YAML.Indexed L4YAML.TokenParser.Indexed
open L4YAML.Proofs.Composition
open L4YAML.Proofs.ParserGrammable

namespace L4YAML.Proofs.Indexed.NodeProofs

-- Local copy of bridge lemma (mirrors legacy `ParserNodeProofs`;
-- self-contained so the cutover commit can drop this file's
-- legacy twin without touching downstream callers).
theorem any_name_implies_findSome_isSome'
    (anchors : Array (String × YamlValue)) (name : String)
    (h : anchors.any (fun (n, _) => n == name) = true) :
    (anchors.findSome? (fun (n, _) => if n == name then some () else none)).isSome = true :=
  Array.any_true_findSome_isSome anchors _ _ (fun ⟨n, _⟩ hp => by simp [hp]) h
  where
    Array.any_true_findSome_isSome
        {α β : Type} (xs : Array α) (f : α → Bool) (g : α → Option β)
        (h_fg : ∀ x, f x = true → (g x).isSome = true)
        (h : xs.any f = true) :
        (xs.findSome? g).isSome = true := by
      rw [Array.findSome?_isSome_iff]
      rw [Array.any_eq_true] at h
      obtain ⟨i, hi, hp⟩ := h
      exact ⟨xs[i], Array.getElem_mem hi, h_fg _ hp⟩

-- Local copy of unfold_loop_at (defined in ParserGrammable, not transitively imported)
open Lean Lean.Meta Lean.Elab.Tactic in
elab "unfold_loop_at" h:ident : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let fvarId ← getFVarId h
    let ldecl ← fvarId.getDecl
    let ty := ldecl.type
    let namesRef ← IO.mkRef (∅ : NameSet)
    let _ ← Lean.Meta.transform ty (pre := fun e => do
      let fn := e.getAppFn
      if fn.isConst then
        let name := fn.constName!
        let leaf := if name.isStr then name.getString! else ""
        let parentLeaf := if name.getPrefix.isStr then name.getPrefix.getString! else ""
        if leaf == "loop" || parentLeaf == "loop" then
          namesRef.modify (·.insert name)
      return .continue)
    let names ← namesRef.get
    if names.isEmpty then throwError "no loop constants found"
    let mut currentTy := ty
    for name in names do
      let result ← Lean.Meta.unfold currentTy name
      currentTy := result.expr
    if ty == currentTy then throwError "no change"
    let mvarId ← mvarId.replaceLocalDeclDefEq fvarId currentTy
    replaceMainGoal [mvarId]


/-! ## AnchorsGrow relation -/

variable {input : String}

def AG (ps ps' : ParseStateIx input) : Prop :=
  ∀ i : Fin ps.anchors.size, ∃ j : Fin ps'.anchors.size,
    ps'.anchors[j] = ps.anchors[i]

variable {ps ps' ps1 ps2 ps3 : ParseStateIx input}

theorem AG.refl : AG ps ps := fun i => ⟨i, rfl⟩
theorem AG.trans (h12 : AG ps1 ps2) (h23 : AG ps2 ps3) : AG ps1 ps3 := by
  intro i; obtain ⟨j, hj⟩ := h12 i; obtain ⟨k, hk⟩ := h23 j; exact ⟨k, hk ▸ hj⟩
theorem AG.of_eq (h : ps'.anchors = ps.anchors) : AG ps ps' :=
  fun ⟨i, hi⟩ => ⟨⟨i, h ▸ hi⟩, by simp [h]⟩
theorem AG.advance (ps : ParseStateIx input) : AG ps ps.advance :=
  AG.of_eq (by simp [ParseStateIx.advance])
theorem AG.withField (ps : ParseStateIx input) (p : YamlPath) :
    AG ps { ps with currentPath := p } := AG.of_eq rfl
theorem AG.tryConsume (ps : ParseStateIx input) (tok : YamlToken) :
    AG ps (ps.tryConsume tok).2 := by
  unfold ParseStateIx.tryConsume
  split
  · split
    · exact AG.advance ps
    · exact AG.refl
  · exact AG.refl

-- tryConsume preserves anchors (needed for unification in AAR proofs)
@[simp] theorem tryConsume_snd_anchors (ps : ParseStateIx input) (tok : YamlToken) :
    (ps.tryConsume tok).snd.anchors = ps.anchors := by
  unfold ParseStateIx.tryConsume; split <;> (try split) <;> simp [ParseStateIx.advance]

theorem applyNodeFinalization_ag
    (val : YamlValue) (ps : ParseStateIx input) (props : NodeProperties)
    (nodeStartPos : YamlPos) :
    AG ps (applyNodeFinalization val ps props nodeStartPos).2 := by
  intro ⟨i, hi⟩
  rcases props with ⟨anchor, tag, dup⟩
  cases anchor with
  | none =>
    simp only [applyNodeFinalization]
    refine ⟨⟨i, ?_⟩, ?_⟩
    · split <;> exact hi
    · split <;> rfl
  | some name =>
    simp only [applyNodeFinalization, ParseStateIx.addAnchor]
    refine ⟨⟨i, ?_⟩, ?_⟩
    · split <;> (simp [Array.size_push]; omega)
    · split <;> (simp [Array.getElem_push, show i < ps.anchors.size from hi])

/-! ## ParseNodeAG induction hypothesis -/

def ParseNodeAG (input : String) (n : Nat) : Prop :=
  ∀ (ps : ParseStateIx input) (m : Nat) (val : YamlValue) (ps' : ParseStateIx input),
    m ≤ n → parseNode ps m = .ok (val, ps') → AG ps ps'

variable {n : Nat}

/-! ## Sub-parser AG lemmas: block sequences -/

theorem parseBlockSequenceLoop_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (items : Array YamlValue)
    (h_fuel : fuel ≤ n + 1)
    (result : Array YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseBlockSequenceLoop ps fuel items = .ok (result, ps')) :
    AG ps ps' := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseBlockSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl
  | succ k ih_fuel =>
    unfold parseBlockSequenceLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · -- peek? = some .blockEntry
      split at h_ok
      -- empty entry: recurse with items.push emptyNode
      · exact AG.trans (AG.advance ps)
          (ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok)
      · exact AG.trans (AG.advance ps)
          (ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok)
      · exact AG.trans (AG.advance ps)
          (ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok)
      -- non-empty: parseNode then recurse
      · split at h_ok
        · simp at h_ok
        · rename_i pn_res heq_pn
          obtain ⟨val_n, ps_n⟩ := pn_res
          dsimp only [] at h_ok
          have h_ag_n := h_ih _ k val_n ps_n (by omega) heq_pn
          exact AG.trans (AG.advance ps)
            (AG.trans (AG.withField ps.advance _)
              (AG.trans h_ag_n
                (AG.trans (AG.withField ps_n _)
                  (ih_fuel _ _ (by omega) h_ok))))
    · -- not blockEntry
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl

theorem parseBlockSequence_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseBlockSequence ps fuel = .ok (val, ps')) :
    AG ps ps' := by
  unfold parseBlockSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨items, ps_loop⟩ := loop_res
      dsimp only [] at h_ok
      have h_ag_loop := parseBlockSequenceLoop_ag h_ih ps.advance k #[] (by omega)
          items ps_loop heq_loop
      split at h_ok <;> (
        simp only [Except.ok.injEq] at h_ok
        obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok)
      · exact AG.trans (AG.advance ps) (AG.trans h_ag_loop (AG.advance ps_loop))
      · exact AG.trans (AG.advance ps) h_ag_loop

/-! ## Sub-parser AG lemmas: implicit block sequences -/

theorem parseImplicitBlockSequenceLoop_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (items : Array YamlValue)
    (h_fuel : fuel ≤ n + 1)
    (result : Array YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseImplicitBlockSequenceLoop ps fuel items = .ok (result, ps')) :
    AG ps ps' := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseImplicitBlockSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl
  | succ k ih_fuel =>
    unfold parseImplicitBlockSequenceLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · split at h_ok
      · exact AG.trans (AG.advance ps)
          (ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok)
      · exact AG.trans (AG.advance ps)
          (ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok)
      · exact AG.trans (AG.advance ps)
          (ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok)
      · exact AG.trans (AG.advance ps)
          (ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok)
      · split at h_ok
        · simp at h_ok
        · rename_i pn_res heq_pn
          obtain ⟨val_n, ps_n⟩ := pn_res
          dsimp only [] at h_ok
          have h_ag_n := h_ih _ k val_n ps_n (by omega) heq_pn
          exact AG.trans (AG.advance ps)
            (AG.trans (AG.withField ps.advance _)
              (AG.trans h_ag_n
                (AG.trans (AG.withField ps_n _)
                  (ih_fuel _ _ (by omega) h_ok))))
    · simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl

theorem parseImplicitBlockSequence_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseImplicitBlockSequence ps fuel = .ok (val, ps')) :
    AG ps ps' := by
  unfold parseImplicitBlockSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨items, ps_loop⟩ := loop_res
      dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
      exact parseImplicitBlockSequenceLoop_ag h_ih ps k #[] (by omega)
          items ps_loop heq_loop

/-! ## Sub-parser AG lemmas: block mapping -/

theorem parseBlockMappingEntryValue_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (keyHasContent : Bool) (keyLine keyCol : Nat)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseBlockMappingEntryValue ps fuel keyHasContent keyLine keyCol = .ok (val, ps')) :
    AG ps ps' := by
  unfold parseBlockMappingEntryValue at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  have h_tc : AG ps (ps.tryConsume .value).2 := AG.tryConsume ps _
  split at h_ok
  · -- consumed = true: for loop + dispatch
    -- Peel through for-loop desugaring
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    -- Empty value: h_ok = .ok (emptyNode, ps_tc)
    all_goals try (obtain ⟨rfl, rfl⟩ := h_ok; exact h_tc)
    -- parseNode: h_ok = parseNode ps_tc fuel = .ok (val, ps')
    all_goals exact AG.trans h_tc (h_ih _ fuel _ _ h_fuel h_ok)
  · -- consumed = false
    obtain ⟨rfl, rfl⟩ := h_ok; exact h_tc

-- handleBlockMappingKeyEntry: advance → if keyHasContent → parseNode/emptyNode → BEV → restore path
set_option maxHeartbeats 400000 in
theorem handleBlockMappingKeyEntry_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (pairIdx : Nat) (key val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : handleBlockMappingKeyEntry ps fuel pairIdx = .ok (key, val, ps')) :
    AG ps ps' := by
  unfold handleBlockMappingKeyEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  -- Split on match ps.advance.peek? (keyHasContent)
  split at h_ok <;> first | contradiction | skip
  -- Resolve emptyNode match if present
  all_goals (try (simp only [emptyNode] at h_ok))
  -- Peel through if/match/bind
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  -- Extract result
  all_goals (simp only [Except.ok.injEq] at h_ok)
  all_goals (obtain ⟨_, _, rfl⟩ := h_ok)
  -- Close: emptyNode key cases (no parseNode, just advance → BEV → path)
  all_goals try exact AG.trans (AG.advance ps) (AG.trans (AG.withField ps.advance _)
      (AG.trans (parseBlockMappingEntryValue_ag h_ih _ _ h_fuel _ _ _ _ _ (by assumption))
        (AG.withField _ _)))
  -- Close: parseNode key cases (advance → parseNode → path → BEV → path)
  all_goals exact AG.trans (AG.advance ps) (AG.trans (h_ih _ fuel _ _ h_fuel (by assumption))
      (AG.trans (AG.withField _ _)
        (AG.trans (parseBlockMappingEntryValue_ag h_ih _ _ h_fuel _ _ _ _ _ (by assumption))
          (AG.withField _ _))))

theorem handleBlockMappingValueEntry_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (pairIdx : Nat) (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : handleBlockMappingValueEntry ps fuel pairIdx = .ok (val, ps')) :
    AG ps ps' := by
  unfold handleBlockMappingValueEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  -- Split on inner match (peek?): combined arm has 3 patterns + 1 catch-all
  split at h_ok
  -- Close all emptyNode cases (some .key, some .blockEnd, none)
  all_goals (try (
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
    exact AG.trans (AG.advance ps) (AG.withField ps.advance _)))
  -- Remaining: catch-all → parseNode
  · split at h_ok
    · simp at h_ok
    · rename_i pn_res heq_pn
      obtain ⟨v, ps_n⟩ := pn_res
      dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
      exact AG.trans (AG.advance ps)
        (AG.trans (AG.withField ps.advance _)
          (AG.trans (h_ih _ fuel v ps_n h_fuel heq_pn) (AG.withField ps_n _)))

theorem parseBlockMappingLoop_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (pairs : Array (YamlValue × YamlValue))
    (h_fuel : fuel ≤ n + 1)
    (result : Array (YamlValue × YamlValue)) (ps' : ParseStateIx input)
    (h_ok : parseBlockMappingLoop ps fuel pairs = .ok (result, ps')) :
    AG ps ps' := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseBlockMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl
  | succ k ih_fuel =>
    unfold parseBlockMappingLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · -- key
      split at h_ok
      · simp at h_ok
      · rename_i entry_res heq_entry
        obtain ⟨key_v, val_v, ps_entry⟩ := entry_res
        dsimp only [] at h_ok
        have h_ag_entry := handleBlockMappingKeyEntry_ag h_ih ps k (by omega)
            _ key_v val_v ps_entry heq_entry
        exact AG.trans h_ag_entry (ih_fuel ps_entry _ (by omega) h_ok)
    · -- value (implicit key)
      split at h_ok
      · simp at h_ok
      · rename_i val_res heq_val
        obtain ⟨val_v, ps_val⟩ := val_res
        dsimp only [] at h_ok
        have h_ag_val := handleBlockMappingValueEntry_ag h_ih ps k (by omega)
            _ val_v ps_val heq_val
        exact AG.trans h_ag_val (ih_fuel ps_val _ (by omega) h_ok)
    · -- not key/value
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl

theorem parseBlockMapping_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseBlockMapping ps fuel = .ok (val, ps')) :
    AG ps ps' := by
  unfold parseBlockMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨pairs, ps_loop⟩ := loop_res
      dsimp only [] at h_ok
      have h_ag_loop := parseBlockMappingLoop_ag h_ih ps.advance k #[] (by omega)
          pairs ps_loop heq_loop
      split at h_ok <;> (
        simp only [Except.ok.injEq] at h_ok
        obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok)
      · exact AG.trans (AG.advance ps) (AG.trans h_ag_loop (AG.advance ps_loop))
      · exact AG.trans (AG.advance ps) h_ag_loop

/-! ## Sub-parser AG lemmas: flow parsers -/

-- parseExplicitKey: emptyNode or parseNode
theorem parseExplicitKey_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseExplicitKey ps fuel = .ok (val, ps')) :
    AG ps ps' := by
  unfold parseExplicitKey at h_ok
  split at h_ok
  · simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl
  · simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl
  · simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl
  · exact h_ih _ fuel _ _ h_fuel h_ok

-- parseFlowMappingValue: withField → tryConsume key → tryConsume value → parseNode/emptyNode
theorem parseFlowMappingValue_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (savedPath : YamlPath) (keyContent : String)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseFlowMappingValue ps fuel savedPath keyContent = .ok (val, ps')) :
    AG ps ps' := by
  unfold parseFlowMappingValue at h_ok
  simp only [bind, Except.bind] at h_ok
  -- tryConsume .key then tryConsume .value
  split at h_ok <;> first | contradiction | skip
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (simp only [Except.ok.injEq] at h_ok)
  all_goals (obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok)
  -- All cases: withField → tryConsume(s) → parseNode/emptyNode → withField
  all_goals try exact AG.trans (AG.withField ps _) (AG.trans (AG.tryConsume _ _)
      (AG.trans (AG.tryConsume _ _) (AG.withField _ _)))
  all_goals try exact AG.trans (AG.withField ps _) (AG.trans (AG.tryConsume _ _)
      (AG.trans (AG.tryConsume _ _) (AG.trans (h_ih _ fuel _ _ h_fuel (by assumption))
        (AG.withField _ _))))
  all_goals exact AG.trans (AG.withField ps _) (AG.trans (AG.tryConsume _ _)
      (AG.trans (AG.tryConsume _ _) (AG.withField _ _)))

-- parseSinglePairMapping: advance → parseNode/emptyNode → withField → tryConsume → parseNode/emptyNode → withField
set_option maxHeartbeats 1600000 in
theorem parseSinglePairMapping_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseSinglePairMapping ps fuel = .ok (val, ps')) :
    AG ps ps' := by
  unfold parseSinglePairMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok  -- fuel = 0
  · rename_i k
    -- Split on key match (emptyNode vs parseNode)
    split at h_ok <;> first | contradiction | skip
    all_goals (try (simp only [emptyNode] at h_ok))
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    -- Extract result
    all_goals (simp only [Except.ok.injEq] at h_ok)
    all_goals (obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok)
    -- Close: emptyNode key, emptyNode val
    all_goals try exact AG.trans (AG.advance ps) (AG.trans (AG.withField ps.advance _)
        (AG.trans (AG.tryConsume _ _) (AG.withField _ _)))
    -- Close: emptyNode key, parseNode val
    all_goals try exact AG.trans (AG.advance ps) (AG.trans (AG.withField ps.advance _)
        (AG.trans (AG.tryConsume _ _) (AG.trans (h_ih _ k _ _ (by omega) (by assumption))
          (AG.withField _ _))))
    -- Close: parseNode key, emptyNode val
    all_goals try exact AG.trans (AG.advance ps) (AG.trans (h_ih _ k _ _ (by omega) (by assumption))
        (AG.trans (AG.withField _ _) (AG.trans (AG.tryConsume _ _) (AG.withField _ _))))
    -- Close: parseNode key, parseNode val
    all_goals exact AG.trans (AG.advance ps) (AG.trans (h_ih _ k _ _ (by omega) (by assumption))
        (AG.trans (AG.withField _ _) (AG.trans (AG.tryConsume _ _)
          (AG.trans (h_ih _ k _ _ (by omega) (by assumption)) (AG.withField _ _)))))

-- parseFlowSequenceLoop
theorem parseFlowSequenceLoop_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (items : Array YamlValue)
    (h_fuel : fuel ≤ n + 1)
    (result : Array YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseFlowSequenceLoop ps fuel items = .ok (result, ps')) :
    AG ps ps' := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl
  | succ k ih_fuel =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    -- First match: peek? = flowSequenceEnd vs other
    split at h_ok
    next => -- flowSequenceEnd
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl
    next => -- other
      split at h_ok
      · -- items.size > 0 → separator check
        split at h_ok
        next => -- flowEntry → advance separator then dispatch
          split at h_ok
          next => -- key → parseSinglePairMapping
            split at h_ok
            next => simp at h_ok
            next spm_res heq_spm =>
              obtain ⟨mv, ps3⟩ := spm_res; dsimp only [] at h_ok
              exact AG.trans (AG.advance ps) (AG.trans (AG.withField ps.advance _)
                  (AG.trans (parseSinglePairMapping_ag h_ih _ k (by omega) mv ps3 heq_spm)
                    (AG.trans (AG.withField ps3 _) (ih_fuel _ _ (by omega) h_ok))))
          next => -- flowSequenceEnd
            simp only [Except.ok.injEq] at h_ok
            obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.advance ps
          next => -- other → parseNode
            split at h_ok
            next => simp at h_ok
            next pn_res heq_pn =>
              obtain ⟨v, ps3⟩ := pn_res; dsimp only [] at h_ok
              exact AG.trans (AG.advance ps) (AG.trans (AG.withField ps.advance _)
                  (AG.trans (h_ih _ k v ps3 (by omega) heq_pn)
                    (AG.trans (AG.withField ps3 _) (ih_fuel _ _ (by omega) h_ok))))
        next => -- not flowEntry → early return
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl
      · -- items.size = 0 → no separator check
        split at h_ok
        next => -- key → parseSinglePairMapping
          split at h_ok
          next => simp at h_ok
          next spm_res heq_spm =>
            obtain ⟨mv, ps3⟩ := spm_res; dsimp only [] at h_ok
            exact AG.trans (AG.withField ps _)
                (AG.trans (parseSinglePairMapping_ag h_ih _ k (by omega) mv ps3 heq_spm)
                  (AG.trans (AG.withField ps3 _) (ih_fuel _ _ (by omega) h_ok)))
        next => -- flowSequenceEnd
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl
        next => -- other → parseNode
          split at h_ok
          next => simp at h_ok
          next pn_res heq_pn =>
            obtain ⟨v, ps3⟩ := pn_res; dsimp only [] at h_ok
            exact AG.trans (AG.withField ps _)
                (AG.trans (h_ih _ k v ps3 (by omega) heq_pn)
                  (AG.trans (AG.withField ps3 _) (ih_fuel _ _ (by omega) h_ok)))

theorem parseFlowSequence_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseFlowSequence ps fuel = .ok (val, ps')) :
    AG ps ps' := by
  unfold parseFlowSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨items, ps_loop⟩ := loop_res
      dsimp only [] at h_ok
      have h_ag_loop := parseFlowSequenceLoop_ag h_ih ps.advance k #[] (by omega)
          items ps_loop heq_loop
      split at h_ok
      · simp only [Except.ok.injEq] at h_ok
        obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
        exact AG.trans (AG.advance ps) (AG.trans h_ag_loop (AG.advance ps_loop))
      · simp at h_ok

-- parseFlowMappingLoop
theorem parseFlowMappingLoop_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (pairs : Array (YamlValue × YamlValue))
    (h_fuel : fuel ≤ n + 1)
    (result : Array (YamlValue × YamlValue)) (ps' : ParseStateIx input)
    (h_ok : parseFlowMappingLoop ps fuel pairs = .ok (result, ps')) :
    AG ps ps' := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl
  | succ k ih_fuel =>
    unfold parseFlowMappingLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    next => -- flowMappingEnd
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl
    next => -- other
      split at h_ok
      · -- pairs.size > 0 → separator check
        split at h_ok
        next => -- flowEntry → advance separator then dispatch
          split at h_ok
          next => -- flowMappingEnd
            simp only [Except.ok.injEq] at h_ok
            obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.advance ps
          next => -- key → advance → parseExplicitKey → FMV → recurse
            split at h_ok
            next => simp at h_ok
            next ek_res heq_ek =>
              obtain ⟨key_v, ps_ek⟩ := ek_res; dsimp only [] at h_ok
              split at h_ok
              next => simp at h_ok
              next fmv_res heq_fmv =>
                obtain ⟨val_v, ps_fmv⟩ := fmv_res; dsimp only [] at h_ok
                exact AG.trans (AG.advance ps) (AG.trans (AG.advance ps.advance)
                    (AG.trans (parseExplicitKey_ag h_ih ps.advance.advance k (by omega) key_v ps_ek heq_ek)
                      (AG.trans (parseFlowMappingValue_ag h_ih ps_ek k (by omega) _ _ val_v ps_fmv heq_fmv)
                        (ih_fuel _ _ (by omega) h_ok))))
          next => -- other → parseNode → FMV → recurse
            split at h_ok
            next => simp at h_ok
            next pn_res heq_pn =>
              obtain ⟨key_v, ps_pn⟩ := pn_res; dsimp only [] at h_ok
              split at h_ok
              next => simp at h_ok
              next fmv_res heq_fmv =>
                obtain ⟨val_v, ps_fmv⟩ := fmv_res; dsimp only [] at h_ok
                exact AG.trans (AG.advance ps)
                    (AG.trans (h_ih _ k key_v ps_pn (by omega) heq_pn)
                      (AG.trans (parseFlowMappingValue_ag h_ih ps_pn k (by omega) _ _ val_v ps_fmv heq_fmv)
                        (ih_fuel _ _ (by omega) h_ok)))
        next => -- not flowEntry → early return
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl
      · -- pairs.size = 0 → no separator check
        split at h_ok
        next => -- flowMappingEnd
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact AG.refl
        next => -- key → advance → parseExplicitKey → FMV → recurse
          split at h_ok
          next => simp at h_ok
          next ek_res heq_ek =>
            obtain ⟨key_v, ps_ek⟩ := ek_res; dsimp only [] at h_ok
            split at h_ok
            next => simp at h_ok
            next fmv_res heq_fmv =>
              obtain ⟨val_v, ps_fmv⟩ := fmv_res; dsimp only [] at h_ok
              exact AG.trans (AG.advance ps)
                  (AG.trans (parseExplicitKey_ag h_ih ps.advance k (by omega) key_v ps_ek heq_ek)
                    (AG.trans (parseFlowMappingValue_ag h_ih ps_ek k (by omega) _ _ val_v ps_fmv heq_fmv)
                      (ih_fuel _ _ (by omega) h_ok)))
        next => -- other → parseNode → FMV → recurse
          split at h_ok
          next => simp at h_ok
          next pn_res heq_pn =>
            obtain ⟨key_v, ps_pn⟩ := pn_res; dsimp only [] at h_ok
            split at h_ok
            next => simp at h_ok
            next fmv_res heq_fmv =>
              obtain ⟨val_v, ps_fmv⟩ := fmv_res; dsimp only [] at h_ok
              exact AG.trans (h_ih _ k key_v ps_pn (by omega) heq_pn)
                  (AG.trans (parseFlowMappingValue_ag h_ih ps_pn k (by omega) _ _ val_v ps_fmv heq_fmv)
                    (ih_fuel _ _ (by omega) h_ok))

theorem parseFlowMapping_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseFlowMapping ps fuel = .ok (val, ps')) :
    AG ps ps' := by
  unfold parseFlowMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨pairs, ps_loop⟩ := loop_res
      dsimp only [] at h_ok
      have h_ag_loop := parseFlowMappingLoop_ag h_ih ps.advance k #[] (by omega)
          pairs ps_loop heq_loop
      split at h_ok
      · simp only [Except.ok.injEq] at h_ok
        obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
        exact AG.trans (AG.advance ps) (AG.trans h_ag_loop (AG.advance ps_loop))
      · simp at h_ok

/-! ## parseNodeProperties AG (trivial — only advance, no parseNode) -/

set_option maxHeartbeats 800000 in
theorem parseNodeProperties_ag
    (ps : ParseStateIx input) (props : NodeProperties) (ps' : ParseStateIx input)
    (h_ok : parseNodeProperties ps = .ok (props, ps')) :
    AG ps ps' := by
  unfold parseNodeProperties at h_ok
  -- Unroll the for-loop (2 iterations + termination check)
  unfold ForIn.forIn instForInOfForIn' at h_ok
  unfold ForIn'.forIn' Std.Legacy.Range.instForIn'NatInferInstanceMembershipOfMonad at h_ok
  unfold Std.Legacy.Range.forIn' at h_ok
  unfold_loop_at h_ok
  simp (config := { decide := true, iota := false }) only [] at h_ok
  unfold_loop_at h_ok
  simp (config := { decide := true, iota := false }) only [] at h_ok
  try unfold_loop_at h_ok
  simp (config := { decide := true, iota := false }) only [
    bind, Except.bind, pure, Except.pure, dite_true] at h_ok
  try unfold_loop_at h_ok
  try simp (config := { decide := true, iota := false }) only [
    bind, Except.bind, pure, Except.pure] at h_ok
  -- Split outermost Except (final result)
  split at h_ok
  · contradiction
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h_ok
    obtain ⟨_hfst, rfl⟩ := h_ok
    rename_i heq
    split at heq
    · contradiction
    · rename_i v heq_first
      cases v with
      | done x =>
        -- First iteration done (break): no second iteration
        simp (config := { iota := true }) only [] at heq
        simp only [Except.ok.injEq] at heq; subst heq
        -- Split first iteration body
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (try contradiction)
        all_goals (try simp only [Except.ok.injEq, ForInStep.done.injEq] at heq_first)
        all_goals (try cases heq_first)
        all_goals (try subst heq_first)
        all_goals (first | exact AG.refl | exact AG.of_eq (by simp [ParseStateIx.advance]))
      | yield x =>
        -- First iteration yielded → second iteration
        simp (config := { iota := true }) only [] at heq
        split at heq
        · contradiction
        · rename_i v2 heq_second
          cases v2 with
          | done y =>
            simp (config := { iota := true }) only [] at heq
            simp only [Except.ok.injEq] at heq; subst heq
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (try contradiction)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (try contradiction)
            all_goals (try cases heq_first)
            all_goals (try cases heq_second)
            all_goals (try simp only [] at *)
            all_goals (try subst_vars)
            all_goals (first | exact AG.refl | exact AG.of_eq (by simp [ParseStateIx.advance]))
          | yield y =>
            simp only [dite_false] at heq
            simp only [Except.ok.injEq] at heq; subst heq
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (try contradiction)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (try contradiction)
            all_goals (try cases heq_first)
            all_goals (try cases heq_second)
            all_goals (try simp only [] at *)
            all_goals (try subst_vars)
            all_goals (first | exact AG.refl | exact AG.of_eq (by simp [ParseStateIx.advance]))

/-! ## parseNodeContent AG -/

theorem parseNodeContent_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (props : NodeProperties) (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseNodeContent ps fuel props = .ok (val, ps')) :
    AG ps ps' := by
  unfold parseNodeContent at h_ok
  split at h_ok
  · -- scalar: just advance
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
    exact AG.advance ps
  · -- blockSequenceStart
    exact parseBlockSequence_ag h_ih ps fuel (by omega) val ps' h_ok
  · -- blockMappingStart
    exact parseBlockMapping_ag h_ih ps fuel (by omega) val ps' h_ok
  · -- blockEntry (implicit block sequence)
    exact parseImplicitBlockSequence_ag h_ih ps fuel (by omega) val ps' h_ok
  · -- flowSequenceStart
    exact parseFlowSequence_ag h_ih ps fuel (by omega) val ps' h_ok
  · -- flowMappingStart
    exact parseFlowMapping_ag h_ih ps fuel (by omega) val ps' h_ok
  · -- empty node: no state change
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
    exact AG.refl

/-! ## Main theorem: parseNode AG by strong induction -/

set_option maxHeartbeats 400000 in
theorem parseNode_ag_all : ∀ n, ParseNodeAG input n := by
  intro n
  induction n with
  | zero =>
    intro ps m val ps' h_le h_ok
    -- m ≤ 0, so m = 0. parseNode ps 0 = error
    have : m = 0 := by omega
    subst this
    simp [parseNode] at h_ok
  | succ n ih =>
    intro ps m val ps' h_le h_ok
    cases m with
    | zero => simp [parseNode] at h_ok
    | succ k =>
      have h_k_le : k ≤ n := by omega
      -- Use ih as the ParseNodeAG input n induction hypothesis
      have h_pnag : ParseNodeAG input n := ih
      unfold parseNode at h_ok
      simp only [bind, Except.bind, pure, Except.pure] at h_ok
      -- Split on alias check (peek?)
      split at h_ok
      · -- alias branch: advance only
        split at h_ok <;> first | contradiction | skip
        -- trackPositions branch
        split at h_ok <;> (
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok)
        · exact AG.advance ps
        · exact AG.advance ps
      · -- normal branch: parseNodeProperties → validateNodeProps → parseNodeContent → applyNodeFinalization
        split at h_ok
        · simp at h_ok  -- parseNodeProperties error
        · rename_i props_res heq_props
          obtain ⟨props, ps_props⟩ := props_res
          dsimp only [] at h_ok
          have h_ag_props := parseNodeProperties_ag ps props ps_props heq_props
          -- validateNodeProps
          split at h_ok <;> first | contradiction | skip
          -- parseNodeContent
          split at h_ok
          · simp at h_ok  -- parseNodeContent error
          · rename_i content_res heq_content
            obtain ⟨val_c, ps_c⟩ := content_res
            dsimp only [] at h_ok
            have h_ag_content := parseNodeContent_ag h_pnag ps_props k h_k_le props val_c ps_c heq_content
            -- applyNodeFinalization: h_ok now says .ok (finalize ...) = .ok (val, ps')
            simp only [Except.ok.injEq] at h_ok
            obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
            exact AG.trans h_ag_props
              (AG.trans h_ag_content
                (applyNodeFinalization_ag val_c ps_c props _))

/-! ## Extract the target theorem -/

theorem parseNode_anchors_grow (ps : ParseStateIx input) (n : Nat)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseNode ps n = .ok (val, ps')) :
    ∀ i : Fin ps.anchors.size, ∃ j : Fin ps'.anchors.size,
      ps'.anchors[j] = ps.anchors[i] :=
  parseNode_ag_all n ps n val ps' Nat.le.refl h_ok

/-! ## AllAliasesResolve (AAR) proofs -/

-- Abbreviation for the ParseNode-level AAR property
def ParseNodeAAR (input : String) (n : Nat) : Prop :=
  ∀ (ps : ParseStateIx input) (m : Nat) (val : YamlValue) (ps' : ParseStateIx input),
    m ≤ n → parseNode ps m = .ok (val, ps') → AllAliasesResolve val ps'.anchors

-- Bridge lemma: imported from ParserAnchorProofs as `any_name_implies_findSome_isSome'`

-- AAR.mono: lift AAR to larger anchors via AG embedding
theorem aar_mono {val : YamlValue} {a1 a2 : Array (String × YamlValue)}
    (h_ag : ∀ i : Fin a1.size, ∃ j : Fin a2.size, a2[j] = a1[i])
    (h : AllAliasesResolve val a1) : AllAliasesResolve val a2 := by
  induction h with
  | scalar s _ => exact .scalar s _
  | alias name anchors h_find =>
    apply AllAliasesResolve.alias
    rw [Array.findSome?_isSome_iff] at h_find ⊢
    obtain ⟨x, hx, hfx⟩ := h_find
    rw [Array.mem_iff_getElem] at hx; obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj⟩ := h_ag ⟨i, hi⟩
    exact ⟨a2[j], Array.getElem_mem j.isLt, hj ▸ hfx⟩
  | sequence style items tag anchor anchors _h ih =>
    exact .sequence style items tag anchor _ (fun i => ih i h_ag)
  | mapping style pairs tag anchor anchors _hk _hv ihk ihv =>
    exact .mapping style pairs tag anchor _ (fun i => ihk i h_ag) (fun i => ihv i h_ag)

-- AAR for applyNodeFinalization: preserves AAR + lifts through anchor push
-- Helper: changing tag/anchor fields preserves AAR
theorem aar_retag_sequence (anchors : Array (String × YamlValue))
    {style : CollectionStyle} {items : Array YamlValue}
    {t1 a1 : Option String} (t2 a2 : Option String)
    (h : AllAliasesResolve (.sequence style items t1 a1) anchors) :
    AllAliasesResolve (.sequence style items t2 a2) anchors := by
  cases h with | sequence _ _ _ _ _ hi => exact .sequence _ _ _ _ _ hi

theorem aar_retag_mapping (anchors : Array (String × YamlValue))
    {style : CollectionStyle} {pairs : Array (YamlValue × YamlValue)}
    {t1 a1 : Option String} (t2 a2 : Option String)
    (h : AllAliasesResolve (.mapping style pairs t1 a1) anchors) :
    AllAliasesResolve (.mapping style pairs t2 a2) anchors := by
  cases h with | mapping _ _ _ _ _ hk hv => exact .mapping _ _ _ _ _ hk hv

-- AAR.push: AllAliasesResolve preserved when anchors grow by one push
theorem aar_push {val : YamlValue} {anchors : Array (String × YamlValue)}
    (entry : String × YamlValue) (h : AllAliasesResolve val anchors) :
    AllAliasesResolve val (anchors.push entry) :=
  aar_mono (fun ⟨i, hi⟩ => ⟨⟨i, by simp [Array.size_push]; omega⟩,
    by simp [Array.getElem_push, show i < anchors.size from hi]⟩) h

theorem applyNodeFinalization_aar
    (val : YamlValue) (ps : ParseStateIx input) (props : NodeProperties)
    (nodeStartPos : YamlPos)
    (h_aar : AllAliasesResolve val ps.anchors) :
    AllAliasesResolve (applyNodeFinalization val ps props nodeStartPos).1
        (applyNodeFinalization val ps props nodeStartPos).2.anchors := by
  rcases props with ⟨anchor, tag, dup⟩
  unfold applyNodeFinalization
  simp only [ParseStateIx.addAnchor]
  cases val with
  | scalar =>
    cases anchor with
    | none => dsimp only []; split <;> exact h_aar
    | some name => dsimp only []; split <;> exact aar_push _ h_aar
  | alias =>
    cases anchor with
    | none => dsimp only []; split <;> exact h_aar
    | some name => dsimp only []; split <;> exact aar_push _ h_aar
  | sequence style items otag oanchor =>
    cases anchor with
    | none =>
      cases otag <;> cases oanchor <;> (dsimp only []; split <;>
        (first | exact aar_retag_sequence ps.anchors tag none h_aar | exact h_aar))
    | some name =>
      cases otag <;> cases oanchor <;> (dsimp only []; split <;>
        (first | exact aar_push _ (aar_retag_sequence ps.anchors tag (some name) h_aar)
                | exact aar_push _ h_aar))
  | mapping style pairs otag oanchor =>
    cases anchor with
    | none =>
      cases otag <;> cases oanchor <;> (dsimp only []; split <;>
        (first | exact aar_retag_mapping ps.anchors tag none h_aar | exact h_aar))
    | some name =>
      cases otag <;> cases oanchor <;> (dsimp only []; split <;>
        (first | exact aar_push _ (aar_retag_mapping ps.anchors tag (some name) h_aar)
                | exact aar_push _ h_aar))

/-! ## AllAliasesResolve (AAR) sub-parser proofs -/

-- Helper: emptyNode is always AAR
theorem emptyNode_aar (anchors : Array (String × YamlValue)) :
    AllAliasesResolve emptyNode anchors := by
  unfold emptyNode; exact .scalar _ _

-- Helper: push preserves items AAR invariant
theorem items_push_aar
    {items : Array YamlValue} {val : YamlValue}
    {a_old a_new : Array (String × YamlValue)}
    (h_ag : ∀ i : Fin a_old.size, ∃ j : Fin a_new.size, a_new[j] = a_old[i])
    (h_pre : ∀ i : Fin items.size, AllAliasesResolve items[i] a_old)
    (h_new : AllAliasesResolve val a_new) :
    ∀ i : Fin (items.push val).size, AllAliasesResolve (items.push val)[i] a_new := by
  intro ⟨i, hi⟩
  simp [Array.getElem_push]
  split
  next h => exact aar_mono h_ag (h_pre ⟨i, h⟩)
  next => exact h_new

-- Helper: push preserves pairs AAR invariant
theorem pairs_push_aar
    {pairs : Array (YamlValue × YamlValue)} {key val : YamlValue}
    {a_old a_new : Array (String × YamlValue)}
    (h_ag : ∀ i : Fin a_old.size, ∃ j : Fin a_new.size, a_new[j] = a_old[i])
    (h_pre_k : ∀ i : Fin pairs.size, AllAliasesResolve pairs[i].1 a_old)
    (h_pre_v : ∀ i : Fin pairs.size, AllAliasesResolve pairs[i].2 a_old)
    (h_new_k : AllAliasesResolve key a_new)
    (h_new_v : AllAliasesResolve val a_new) :
    (∀ i : Fin (pairs.push (key, val)).size, AllAliasesResolve (pairs.push (key, val))[i].1 a_new) ∧
    (∀ i : Fin (pairs.push (key, val)).size, AllAliasesResolve (pairs.push (key, val))[i].2 a_new) := by
  constructor <;> intro ⟨i, hi⟩ <;> (
    simp [Array.getElem_push]
    split
    next h => first | exact aar_mono h_ag (h_pre_k ⟨i, h⟩)
                    | exact aar_mono h_ag (h_pre_v ⟨i, h⟩)
    next => dsimp only []; first | exact h_new_k | exact h_new_v)

-- Block sequence loop AAR
theorem parseBlockSequenceLoop_aar (h_ih_aar : ParseNodeAAR input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (items : Array YamlValue)
    (h_fuel : fuel ≤ n + 1)
    (result : Array YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseBlockSequenceLoop ps fuel items = .ok (result, ps'))
    (h_pre : ∀ i : Fin items.size, AllAliasesResolve items[i] ps.anchors) :
    (∀ i : Fin result.size, AllAliasesResolve result[i] ps'.anchors) := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseBlockSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact h_pre
  | succ k ih_fuel =>
    unfold parseBlockSequenceLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · -- peek? = some .blockEntry
      split at h_ok
      -- empty entry cases: push emptyNode, recurse
      · exact ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok
          (items_push_aar (AG.advance ps) h_pre (emptyNode_aar _))
      · exact ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok
          (items_push_aar (AG.advance ps) h_pre (emptyNode_aar _))
      · exact ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok
          (items_push_aar (AG.advance ps) h_pre (emptyNode_aar _))
      -- non-empty entry: parseNode then recurse
      · split at h_ok
        · simp at h_ok
        · rename_i pn_res heq_pn
          obtain ⟨val_n, ps_n⟩ := pn_res
          dsimp only [] at h_ok
          have h_ag_n := h_ih_ag _ k val_n ps_n (by omega) heq_pn
          have h_aar_n := h_ih_aar _ k val_n ps_n (by omega) heq_pn
          exact ih_fuel _ (items.push val_n) (by omega) h_ok
            (items_push_aar
              (AG.trans (AG.advance ps)
                (AG.trans (AG.withField ps.advance _)
                  (AG.trans h_ag_n (AG.withField ps_n _))))
              h_pre h_aar_n)
    · -- not blockEntry
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact h_pre

-- Block sequence wrapper AAR
theorem parseBlockSequence_aar (h_ih_aar : ParseNodeAAR input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseBlockSequence ps fuel = .ok (val, ps')) :
    AllAliasesResolve val ps'.anchors := by
  unfold parseBlockSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨items_r, ps_r⟩ := loop_res
      dsimp only [] at h_ok
      split at h_ok <;> (
        simp only [Except.ok.injEq] at h_ok
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
        have h_items := parseBlockSequenceLoop_aar h_ih_aar h_ih_ag
          ps.advance k #[] (by omega) items_r ps_r heq_loop
          (fun ⟨i, hi⟩ => absurd hi (Nat.not_lt_zero _))
        first
        | exact .sequence _ _ _ _ _ h_items
        | (have : ps'.anchors = ps_r.anchors := rfl
           rw [this]; exact .sequence _ _ _ _ _ h_items))

-- Implicit block sequence loop AAR
theorem parseImplicitBlockSequenceLoop_aar (h_ih_aar : ParseNodeAAR input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (items : Array YamlValue)
    (h_fuel : fuel ≤ n + 1)
    (result : Array YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseImplicitBlockSequenceLoop ps fuel items = .ok (result, ps'))
    (h_pre : ∀ i : Fin items.size, AllAliasesResolve items[i] ps.anchors) :
    (∀ i : Fin result.size, AllAliasesResolve result[i] ps'.anchors) := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseImplicitBlockSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact h_pre
  | succ k ih_fuel =>
    unfold parseImplicitBlockSequenceLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · -- peek? = some .blockEntry
      split at h_ok
      -- implicit block sequence has 4 empty + 1 non-empty arms
      · exact ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok
          (items_push_aar (AG.advance ps) h_pre (emptyNode_aar _))
      · exact ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok
          (items_push_aar (AG.advance ps) h_pre (emptyNode_aar _))
      · exact ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok
          (items_push_aar (AG.advance ps) h_pre (emptyNode_aar _))
      · exact ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok
          (items_push_aar (AG.advance ps) h_pre (emptyNode_aar _))
      -- non-empty entry: parseNode then recurse
      · split at h_ok
        · simp at h_ok
        · rename_i pn_res heq_pn
          obtain ⟨val_n, ps_n⟩ := pn_res
          dsimp only [] at h_ok
          have h_ag_n := h_ih_ag _ k val_n ps_n (by omega) heq_pn
          have h_aar_n := h_ih_aar _ k val_n ps_n (by omega) heq_pn
          exact ih_fuel _ (items.push val_n) (by omega) h_ok
            (items_push_aar
              (AG.trans (AG.advance ps)
                (AG.trans (AG.withField ps.advance _)
                  (AG.trans h_ag_n (AG.withField ps_n _))))
              h_pre h_aar_n)
    · -- not blockEntry
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact h_pre

-- Implicit block sequence wrapper AAR
theorem parseImplicitBlockSequence_aar (h_ih_aar : ParseNodeAAR input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseImplicitBlockSequence ps fuel = .ok (val, ps')) :
    AllAliasesResolve val ps'.anchors := by
  unfold parseImplicitBlockSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨items_r, ps_r⟩ := loop_res
      dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
      have h_items := parseImplicitBlockSequenceLoop_aar h_ih_aar h_ih_ag
        ps k #[] (by omega) items_r ps_r heq_loop
        (fun ⟨i, hi⟩ => absurd hi (Nat.not_lt_zero _))
      exact .sequence _ _ _ _ _ h_items

/-! ### Block mapping AAR -/

-- parseBlockMappingEntryValue: value is emptyNode or parseNode result
theorem parseBlockMappingEntryValue_aar (h_ih_aar : ParseNodeAAR input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (keyHasContent : Bool) (keyLine keyCol : Nat)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseBlockMappingEntryValue ps fuel keyHasContent keyLine keyCol = .ok (val, ps')) :
    AllAliasesResolve val ps'.anchors := by
  unfold parseBlockMappingEntryValue at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · -- consumed = true: for loop (validation only) + dispatch
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    -- Empty value case: val = emptyNode
    all_goals try (obtain ⟨rfl, rfl⟩ := h_ok; exact emptyNode_aar _)
    -- parseNode case: val from parseNode
    all_goals exact h_ih_aar _ fuel _ _ h_fuel h_ok
  · -- consumed = false: val = emptyNode
    obtain ⟨rfl, rfl⟩ := h_ok; exact emptyNode_aar _

-- handleBlockMappingKeyEntry: (key, val, ps') — both key and val AAR
set_option maxHeartbeats 400000 in
theorem handleBlockMappingKeyEntry_aar (h_ih_aar : ParseNodeAAR input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (pairIdx : Nat) (key val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : handleBlockMappingKeyEntry ps fuel pairIdx = .ok (key, val, ps')) :
    AllAliasesResolve key ps'.anchors ∧ AllAliasesResolve val ps'.anchors := by
  unfold handleBlockMappingKeyEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  -- Split on peek? for keyHasContent
  split at h_ok <;> first | contradiction | skip
  all_goals (try (simp only [emptyNode] at h_ok))
  -- Peel through if/match/bind
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (simp only [Except.ok.injEq] at h_ok)
  all_goals (obtain ⟨rfl, rfl, rfl⟩ := h_ok)
  -- Close: emptyNode key + BEV value
  all_goals try exact ⟨
    aar_mono (AG.trans (AG.withField _ _)
        (AG.trans (parseBlockMappingEntryValue_ag h_ih_ag _ _ h_fuel _ _ _ _ _ (by assumption))
          (AG.withField _ _)))
      (emptyNode_aar _),
    aar_mono (AG.withField _ _)
      (parseBlockMappingEntryValue_aar h_ih_aar _ _ h_fuel _ _ _ _ _ (by assumption))⟩
  -- Close: parseNode key + BEV value
  all_goals try exact ⟨
    aar_mono (AG.trans (AG.withField _ _)
        (AG.trans (parseBlockMappingEntryValue_ag h_ih_ag _ _ h_fuel _ _ _ _ _ (by assumption))
          (AG.withField _ _)))
      (h_ih_aar _ fuel _ _ h_fuel (by assumption)),
    aar_mono (AG.withField _ _)
      (parseBlockMappingEntryValue_aar h_ih_aar _ _ h_fuel _ _ _ _ _ (by assumption))⟩

-- handleBlockMappingValueEntry: (val, ps') — val is emptyNode or parseNode
theorem handleBlockMappingValueEntry_aar (h_ih_aar : ParseNodeAAR input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (pairIdx : Nat) (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : handleBlockMappingValueEntry ps fuel pairIdx = .ok (val, ps')) :
    AllAliasesResolve val ps'.anchors := by
  unfold handleBlockMappingValueEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  -- emptyNode cases (some .key, some .blockEnd, none)
  · simp only [Except.ok.injEq] at h_ok; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact emptyNode_aar _
  · simp only [Except.ok.injEq] at h_ok; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact emptyNode_aar _
  · simp only [Except.ok.injEq] at h_ok; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact emptyNode_aar _
  -- parseNode case (catch-all)
  · split at h_ok
    · simp at h_ok
    · rename_i pn_res heq_pn
      obtain ⟨v, ps_n⟩ := pn_res
      dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
      exact aar_mono (AG.withField ps_n _) (h_ih_aar _ fuel v ps_n h_fuel heq_pn)

-- Block mapping loop AAR
theorem parseBlockMappingLoop_aar (h_ih_aar : ParseNodeAAR input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (pairs : Array (YamlValue × YamlValue))
    (h_fuel : fuel ≤ n + 1)
    (result : Array (YamlValue × YamlValue)) (ps' : ParseStateIx input)
    (h_ok : parseBlockMappingLoop ps fuel pairs = .ok (result, ps'))
    (h_pre_k : ∀ i : Fin pairs.size, AllAliasesResolve pairs[i].1 ps.anchors)
    (h_pre_v : ∀ i : Fin pairs.size, AllAliasesResolve pairs[i].2 ps.anchors) :
    (∀ i : Fin result.size, AllAliasesResolve result[i].1 ps'.anchors) ∧
    (∀ i : Fin result.size, AllAliasesResolve result[i].2 ps'.anchors) := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseBlockMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact ⟨h_pre_k, h_pre_v⟩
  | succ k ih_fuel =>
    unfold parseBlockMappingLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · -- key
      split at h_ok
      · simp at h_ok
      · rename_i entry_res heq_entry
        obtain ⟨key_v, val_v, ps_entry⟩ := entry_res
        dsimp only [] at h_ok
        have ⟨h_k, h_v⟩ := handleBlockMappingKeyEntry_aar h_ih_aar h_ih_ag
            ps k (by omega) _ key_v val_v ps_entry heq_entry
        have h_ag_entry := handleBlockMappingKeyEntry_ag h_ih_ag ps k (by omega)
            _ key_v val_v ps_entry heq_entry
        have ⟨h_pk, h_pv⟩ := pairs_push_aar h_ag_entry h_pre_k h_pre_v h_k h_v
        exact ih_fuel ps_entry _ (by omega) h_ok h_pk h_pv
    · -- value (implicit key)
      split at h_ok
      · simp at h_ok
      · rename_i val_res heq_val
        obtain ⟨val_v, ps_val⟩ := val_res
        dsimp only [] at h_ok
        have h_v := handleBlockMappingValueEntry_aar h_ih_aar
            ps k (by omega) _ val_v ps_val heq_val
        have h_ag_val := handleBlockMappingValueEntry_ag h_ih_ag ps k (by omega)
            _ val_v ps_val heq_val
        have ⟨h_pk, h_pv⟩ := pairs_push_aar h_ag_val h_pre_k h_pre_v
            (aar_mono h_ag_val (emptyNode_aar _)) h_v
        exact ih_fuel ps_val _ (by omega) h_ok h_pk h_pv
    · -- not key/value
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact ⟨h_pre_k, h_pre_v⟩

-- Block mapping wrapper AAR
theorem parseBlockMapping_aar (h_ih_aar : ParseNodeAAR input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseBlockMapping ps fuel = .ok (val, ps')) :
    AllAliasesResolve val ps'.anchors := by
  unfold parseBlockMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨pairs_r, ps_r⟩ := loop_res
      dsimp only [] at h_ok
      split at h_ok <;> (
        simp only [Except.ok.injEq] at h_ok
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
        have ⟨hk, hv⟩ := parseBlockMappingLoop_aar h_ih_aar h_ih_ag
          ps.advance k #[] (by omega) pairs_r ps_r heq_loop
          (fun ⟨i, hi⟩ => absurd hi (Nat.not_lt_zero _))
          (fun ⟨i, hi⟩ => absurd hi (Nat.not_lt_zero _))
        first
        | exact .mapping _ _ _ _ _ hk hv
        | (have : ps'.anchors = ps_r.anchors := rfl
           rw [this]; exact .mapping _ _ _ _ _ hk hv))

/-! ### Flow parser AAR -/

-- parseExplicitKey: emptyNode or parseNode
theorem parseExplicitKey_aar (h_ih_aar : ParseNodeAAR input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseExplicitKey ps fuel = .ok (val, ps')) :
    AllAliasesResolve val ps'.anchors := by
  unfold parseExplicitKey at h_ok
  split at h_ok
  all_goals (try (obtain ⟨rfl, rfl⟩ := h_ok; exact emptyNode_aar _))
  · exact h_ih_aar _ fuel _ _ h_fuel h_ok

-- parseFlowMappingValue: emptyNode or parseNode
theorem parseFlowMappingValue_aar (h_ih_aar : ParseNodeAAR input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (savedPath : YamlPath) (keyContent : String)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseFlowMappingValue ps fuel savedPath keyContent = .ok (val, ps')) :
    AllAliasesResolve val ps'.anchors := by
  unfold parseFlowMappingValue at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · -- consumed value token
    split at h_ok
    -- emptyNode cases
    all_goals (try (
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
      exact emptyNode_aar _))
    -- parseNode case
    · split at h_ok
      · simp at h_ok
      · rename_i pn_res heq_pn
        obtain ⟨v, ps_n⟩ := pn_res
        dsimp only [] at h_ok
        simp only [Except.ok.injEq] at h_ok
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
        exact aar_mono (AG.withField ps_n _) (h_ih_aar _ fuel v ps_n h_fuel heq_pn)
  · -- not consumed: emptyNode
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
    exact emptyNode_aar _

-- parseSinglePairMapping: creates .mapping .flow #[(key, val)]
-- Helper for single-pair mapping AAR close
theorem spm_close (anchors : Array (String × YamlValue)) (k v : YamlValue)
    (hk : AllAliasesResolve k anchors) (hv : AllAliasesResolve v anchors) :
    AllAliasesResolve (.mapping .flow #[(k, v)]) anchors := by
  apply AllAliasesResolve.mapping
  · intro ⟨i, hi⟩; match i, hi with | 0, _ => dsimp; exact hk
  · intro ⟨i, hi⟩; match i, hi with | 0, _ => dsimp; exact hv

-- Helper: AAR from undestrutured parseNode result (avoids Prod.mk unification issue)
theorem aar_of_parseNode (h_ih : ParseNodeAAR input n)
    (ps : ParseStateIx input) (k : Nat) (res : YamlValue × ParseStateIx input)
    (h_fuel : k ≤ n) (h_ok : parseNode ps k = .ok res) :
    AllAliasesResolve res.fst res.snd.anchors :=
  h_ih ps k res.fst res.snd h_fuel (by rw [← Prod.eta res]; exact h_ok)

set_option maxHeartbeats 800000 in
theorem parseSinglePairMapping_aar (h_ih_aar : ParseNodeAAR input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseSinglePairMapping ps fuel = .ok (val, ps')) :
    AllAliasesResolve val ps'.anchors := by
  unfold parseSinglePairMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    -- Blind split pattern (matching AG proof)
    split at h_ok <;> first | contradiction | skip
    all_goals (try (simp only [emptyNode] at h_ok))
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    -- Extract result
    all_goals (simp only [Except.ok.injEq] at h_ok)
    all_goals (obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok)
    -- Simplify tryConsume.snd.anchors for unification
    all_goals (try simp only [tryConsume_snd_anchors])
    -- Close goals by case
    all_goals try exact spm_close _ _ _ (emptyNode_aar _) (emptyNode_aar _)
    all_goals try (exact spm_close _ _ _ (emptyNode_aar _) (aar_of_parseNode h_ih_aar _ k _ (by omega) (by assumption)))
    all_goals try (exact spm_close _ _ _ (aar_of_parseNode h_ih_aar _ k _ (by omega) (by assumption)) (emptyNode_aar _))
    -- parseNode key + parseNode val: key needs aar_mono (AG from key to final)
    all_goals (
      apply spm_close
      · exact aar_mono
          (AG.trans (AG.withField _ _) (AG.trans (AG.tryConsume _ _)
            (AG.trans (h_ih_ag _ k _ _ (by omega) (by assumption)) (AG.withField _ _))))
          (aar_of_parseNode h_ih_aar _ k _ (by omega) (by assumption))
      · exact aar_of_parseNode h_ih_aar _ k _ (by omega) (by assumption))

-- Flow sequence loop AAR
theorem parseFlowSequenceLoop_aar (h_ih_aar : ParseNodeAAR input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (items : Array YamlValue)
    (h_fuel : fuel ≤ n + 1)
    (result : Array YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseFlowSequenceLoop ps fuel items = .ok (result, ps'))
    (h_pre : ∀ i : Fin items.size, AllAliasesResolve items[i] ps.anchors) :
    (∀ i : Fin result.size, AllAliasesResolve result[i] ps'.anchors) := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact h_pre
  | succ k ih_fuel =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · -- flowSequenceEnd: return items
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact h_pre
    · -- items.size > 0 separator handling + content
      -- Complex: need to handle separator check + key/parseNode/flowSeqEnd
      -- Use explicit next for each case after the separator split
      split at h_ok
      next => -- items.size > 0
        split at h_ok
        next => -- flowEntry separator
          split at h_ok
          next => -- key: parseSinglePairMapping
            split at h_ok
            · simp at h_ok
            · rename_i spm_res heq_spm
              obtain ⟨map_val, ps_spm⟩ := spm_res
              dsimp only [] at h_ok
              have h_spm_aar := parseSinglePairMapping_aar h_ih_aar h_ih_ag
                  _ k (by omega) map_val ps_spm heq_spm
              have h_spm_ag := parseSinglePairMapping_ag h_ih_ag
                  _ k (by omega) map_val ps_spm heq_spm
              exact ih_fuel _ (items.push map_val) (by omega) h_ok
                (items_push_aar
                  (AG.trans (AG.advance ps)
                    (AG.trans (AG.withField ps.advance _)
                      (AG.trans h_spm_ag (AG.withField ps_spm _))))
                  h_pre h_spm_aar)
          next => -- flowSequenceEnd
            simp only [Except.ok.injEq] at h_ok
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact h_pre
          next => -- parseNode
            split at h_ok
            · simp at h_ok
            · rename_i pn_res heq_pn
              obtain ⟨val_n, ps_n⟩ := pn_res
              dsimp only [] at h_ok
              have h_pn_aar := h_ih_aar _ k val_n ps_n (by omega) heq_pn
              have h_pn_ag := h_ih_ag _ k val_n ps_n (by omega) heq_pn
              exact ih_fuel _ (items.push val_n) (by omega) h_ok
                (items_push_aar
                  (AG.trans (AG.advance ps)
                    (AG.trans (AG.withField ps.advance _)
                      (AG.trans h_pn_ag (AG.withField ps_n _))))
                  h_pre h_pn_aar)
        next => -- no separator: return
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact h_pre
      next => -- items.size = 0
        split at h_ok
        next => -- key: parseSinglePairMapping
          split at h_ok
          · simp at h_ok
          · rename_i spm_res heq_spm
            obtain ⟨map_val, ps_spm⟩ := spm_res
            dsimp only [] at h_ok
            have h_spm_aar := parseSinglePairMapping_aar h_ih_aar h_ih_ag
                _ k (by omega) map_val ps_spm heq_spm
            have h_spm_ag := parseSinglePairMapping_ag h_ih_ag
                _ k (by omega) map_val ps_spm heq_spm
            exact ih_fuel _ (items.push map_val) (by omega) h_ok
              (items_push_aar
                (AG.trans (AG.withField ps _) (AG.trans h_spm_ag (AG.withField ps_spm _)))
                h_pre h_spm_aar)
        next => -- flowSequenceEnd
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact h_pre
        next => -- parseNode
          split at h_ok
          · simp at h_ok
          · rename_i pn_res heq_pn
            obtain ⟨val_n, ps_n⟩ := pn_res
            dsimp only [] at h_ok
            have h_pn_aar := h_ih_aar _ k val_n ps_n (by omega) heq_pn
            have h_pn_ag := h_ih_ag _ k val_n ps_n (by omega) heq_pn
            exact ih_fuel _ (items.push val_n) (by omega) h_ok
              (items_push_aar
                (AG.trans (AG.withField ps _) (AG.trans h_pn_ag (AG.withField ps_n _)))
                h_pre h_pn_aar)

-- Flow sequence wrapper AAR
theorem parseFlowSequence_aar (h_ih_aar : ParseNodeAAR input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseFlowSequence ps fuel = .ok (val, ps')) :
    AllAliasesResolve val ps'.anchors := by
  unfold parseFlowSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨items_r, ps_r⟩ := loop_res
      dsimp only [] at h_ok
      split at h_ok
      · simp only [Except.ok.injEq] at h_ok
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
        have h_items := parseFlowSequenceLoop_aar h_ih_aar h_ih_ag
          ps.advance k #[] (by omega) items_r ps_r heq_loop
          (fun ⟨i, hi⟩ => absurd hi (Nat.not_lt_zero _))
        exact .sequence _ _ _ _ _ (fun i => aar_mono (AG.advance ps_r) (h_items i))
      · simp at h_ok

-- Flow mapping loop AAR
theorem parseFlowMappingLoop_aar (h_ih_aar : ParseNodeAAR input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (pairs : Array (YamlValue × YamlValue))
    (h_fuel : fuel ≤ n + 1)
    (result : Array (YamlValue × YamlValue)) (ps' : ParseStateIx input)
    (h_ok : parseFlowMappingLoop ps fuel pairs = .ok (result, ps'))
    (h_pre_k : ∀ i : Fin pairs.size, AllAliasesResolve pairs[i].1 ps.anchors)
    (h_pre_v : ∀ i : Fin pairs.size, AllAliasesResolve pairs[i].2 ps.anchors) :
    (∀ i : Fin result.size, AllAliasesResolve result[i].1 ps'.anchors) ∧
    (∀ i : Fin result.size, AllAliasesResolve result[i].2 ps'.anchors) := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact ⟨h_pre_k, h_pre_v⟩
  | succ k ih_fuel =>
    unfold parseFlowMappingLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · -- flowMappingEnd
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact ⟨h_pre_k, h_pre_v⟩
    · split at h_ok
      next => -- pairs.size > 0
        split at h_ok
        next => -- flowEntry separator
          split at h_ok
          next => -- flowMappingEnd
            simp only [Except.ok.injEq] at h_ok
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact ⟨h_pre_k, h_pre_v⟩
          next => -- key
            split at h_ok
            · simp at h_ok
            · rename_i ek_res heq_ek
              obtain ⟨ek_v, ps_ek⟩ := ek_res
              dsimp only [] at h_ok
              split at h_ok
              · simp at h_ok
              · rename_i fmv_res heq_fmv
                obtain ⟨fmv_v, ps_fmv⟩ := fmv_res
                dsimp only [] at h_ok
                have h_ek_aar := parseExplicitKey_aar h_ih_aar _ k (by omega) ek_v ps_ek heq_ek
                have h_fmv_aar := parseFlowMappingValue_aar h_ih_aar
                    ps_ek k (by omega) _ _ fmv_v ps_fmv heq_fmv
                have h_ag := AG.trans (AG.advance ps)
                  (AG.trans (AG.advance ps.advance)
                    (AG.trans (parseExplicitKey_ag h_ih_ag _ k (by omega) ek_v ps_ek heq_ek)
                      (parseFlowMappingValue_ag h_ih_ag ps_ek k (by omega) _ _ fmv_v ps_fmv heq_fmv)))
                have h_fmv_ag := parseFlowMappingValue_ag h_ih_ag ps_ek k (by omega) _ _ fmv_v ps_fmv heq_fmv
                have ⟨h_pk, h_pv⟩ := pairs_push_aar h_ag h_pre_k h_pre_v
                  (aar_mono h_fmv_ag h_ek_aar) h_fmv_aar
                exact ih_fuel ps_fmv _ (by omega) h_ok h_pk h_pv
          next => -- non-key: parseNode then flowMappingValue
            split at h_ok
            · simp at h_ok
            · rename_i pn_res heq_pn
              obtain ⟨key_v, ps_pn⟩ := pn_res
              dsimp only [] at h_ok
              split at h_ok
              · simp at h_ok
              · rename_i fmv_res heq_fmv
                obtain ⟨fmv_v, ps_fmv⟩ := fmv_res
                dsimp only [] at h_ok
                have h_pn_aar := h_ih_aar _ k key_v ps_pn (by omega) heq_pn
                have h_fmv_aar := parseFlowMappingValue_aar h_ih_aar
                    ps_pn k (by omega) _ _ fmv_v ps_fmv heq_fmv
                have h_ag := AG.trans (AG.advance ps)
                  (AG.trans (h_ih_ag _ k key_v ps_pn (by omega) heq_pn)
                    (parseFlowMappingValue_ag h_ih_ag ps_pn k (by omega) _ _ fmv_v ps_fmv heq_fmv))
                have h_fmv_ag := parseFlowMappingValue_ag h_ih_ag ps_pn k (by omega) _ _ fmv_v ps_fmv heq_fmv
                have ⟨h_pk, h_pv⟩ := pairs_push_aar h_ag h_pre_k h_pre_v
                  (aar_mono h_fmv_ag h_pn_aar) h_fmv_aar
                exact ih_fuel ps_fmv _ (by omega) h_ok h_pk h_pv
        next => -- no separator: return
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact ⟨h_pre_k, h_pre_v⟩
      next => -- pairs.size = 0
        split at h_ok
        next => -- flowMappingEnd
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact ⟨h_pre_k, h_pre_v⟩
        next => -- key
          split at h_ok
          · simp at h_ok
          · rename_i ek_res heq_ek
            obtain ⟨ek_v, ps_ek⟩ := ek_res
            dsimp only [] at h_ok
            split at h_ok
            · simp at h_ok
            · rename_i fmv_res heq_fmv
              obtain ⟨fmv_v, ps_fmv⟩ := fmv_res
              dsimp only [] at h_ok
              have h_ek_aar := parseExplicitKey_aar h_ih_aar _ k (by omega) ek_v ps_ek heq_ek
              have h_fmv_aar := parseFlowMappingValue_aar h_ih_aar
                  ps_ek k (by omega) _ _ fmv_v ps_fmv heq_fmv
              have h_ag := AG.trans (AG.advance ps)
                (AG.trans (parseExplicitKey_ag h_ih_ag _ k (by omega) ek_v ps_ek heq_ek)
                  (parseFlowMappingValue_ag h_ih_ag ps_ek k (by omega) _ _ fmv_v ps_fmv heq_fmv))
              have h_fmv_ag := parseFlowMappingValue_ag h_ih_ag ps_ek k (by omega) _ _ fmv_v ps_fmv heq_fmv
              have ⟨h_pk, h_pv⟩ := pairs_push_aar h_ag h_pre_k h_pre_v
                (aar_mono h_fmv_ag h_ek_aar) h_fmv_aar
              exact ih_fuel ps_fmv _ (by omega) h_ok h_pk h_pv
        next => -- non-key: parseNode then flowMappingValue
          split at h_ok
          · simp at h_ok
          · rename_i pn_res heq_pn
            obtain ⟨key_v, ps_pn⟩ := pn_res
            dsimp only [] at h_ok
            split at h_ok
            · simp at h_ok
            · rename_i fmv_res heq_fmv
              obtain ⟨fmv_v, ps_fmv⟩ := fmv_res
              dsimp only [] at h_ok
              have h_pn_aar := h_ih_aar _ k key_v ps_pn (by omega) heq_pn
              have h_fmv_aar := parseFlowMappingValue_aar h_ih_aar
                  ps_pn k (by omega) _ _ fmv_v ps_fmv heq_fmv
              have h_ag := AG.trans
                (h_ih_ag _ k key_v ps_pn (by omega) heq_pn)
                (parseFlowMappingValue_ag h_ih_ag ps_pn k (by omega) _ _ fmv_v ps_fmv heq_fmv)
              have h_fmv_ag := parseFlowMappingValue_ag h_ih_ag ps_pn k (by omega) _ _ fmv_v ps_fmv heq_fmv
              have ⟨h_pk, h_pv⟩ := pairs_push_aar h_ag h_pre_k h_pre_v
                (aar_mono h_fmv_ag h_pn_aar) h_fmv_aar
              exact ih_fuel ps_fmv _ (by omega) h_ok h_pk h_pv

-- Flow mapping wrapper AAR
theorem parseFlowMapping_aar (h_ih_aar : ParseNodeAAR input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseFlowMapping ps fuel = .ok (val, ps')) :
    AllAliasesResolve val ps'.anchors := by
  unfold parseFlowMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨pairs_r, ps_r⟩ := loop_res
      dsimp only [] at h_ok
      split at h_ok
      · simp only [Except.ok.injEq] at h_ok
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
        have ⟨hk, hv⟩ := parseFlowMappingLoop_aar h_ih_aar h_ih_ag
          ps.advance k #[] (by omega) pairs_r ps_r heq_loop
          (fun ⟨i, hi⟩ => absurd hi (Nat.not_lt_zero _))
          (fun ⟨i, hi⟩ => absurd hi (Nat.not_lt_zero _))
        exact .mapping _ _ _ _ _
          (fun i => aar_mono (AG.advance ps_r) (hk i))
          (fun i => aar_mono (AG.advance ps_r) (hv i))
      · simp at h_ok

/-! ### parseNodeContent and parseNode AAR -/

theorem parseNodeContent_aar (h_ih_aar : ParseNodeAAR input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1) (props : NodeProperties)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseNodeContent ps fuel props = .ok (val, ps')) :
    AllAliasesResolve val ps'.anchors := by
  unfold parseNodeContent at h_ok
  split at h_ok
  · -- scalar
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
    exact .scalar _ _
  · exact parseBlockSequence_aar h_ih_aar h_ih_ag ps fuel (by omega) val ps' h_ok
  · exact parseBlockMapping_aar h_ih_aar h_ih_ag ps fuel (by omega) val ps' h_ok
  · exact parseImplicitBlockSequence_aar h_ih_aar h_ih_ag ps fuel (by omega) val ps' h_ok
  · exact parseFlowSequence_aar h_ih_aar h_ih_ag ps fuel (by omega) val ps' h_ok
  · exact parseFlowMapping_aar h_ih_aar h_ih_ag ps fuel (by omega) val ps' h_ok
  · -- empty scalar
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
    exact .scalar _ _

-- Main AAR theorem by strong induction
set_option maxHeartbeats 400000 in
theorem parseNode_aar_all : ∀ n, ParseNodeAAR input n := by
  intro n
  induction n with
  | zero =>
    intro ps m val ps' h_m h_ok
    have : m = 0 := by omega
    subst this
    simp [parseNode] at h_ok
  | succ n ih_aar =>
    intro ps m val ps' h_m h_ok
    cases m with
    | zero => simp [parseNode] at h_ok
    | succ k =>
      have h_k_le : k ≤ n := by omega
      have h_ih_ag : ParseNodeAG input n := parseNode_ag_all n
      unfold parseNode at h_ok
      simp only [bind, Except.bind, pure, Except.pure] at h_ok
      -- Split on peek? for alias check
      split at h_ok
      · -- alias case
        -- Split on !ps.anchors.any (alias undefined check)
        split at h_ok <;> first | contradiction | skip
        -- trackPositions branch
        split at h_ok <;> (
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
          apply AllAliasesResolve.alias
          apply any_name_implies_findSome_isSome'
          -- goal: ps.advance.anchors.any f = true (= ps.anchors.any f)
          rename_i _ h_any _
          show ps.anchors.any _ = true
          cases hb : ps.anchors.any _ with
          | true => rfl
          | false => simp [hb] at h_any)
      · -- non-alias: properties → validate → content → finalize
        split at h_ok
        · simp at h_ok
        · rename_i props_res heq_props
          obtain ⟨props, ps_props⟩ := props_res
          dsimp only [] at h_ok
          -- validateNodeProps: pass through
          split at h_ok <;> first | contradiction | skip
          -- parseNodeContent
          split at h_ok
          · simp at h_ok
          · rename_i content_res heq_content
            obtain ⟨val_c, ps_c⟩ := content_res
            dsimp only [] at h_ok
            simp only [Except.ok.injEq] at h_ok
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
            exact applyNodeFinalization_aar val_c ps_c props _
              (parseNodeContent_aar ih_aar h_ih_ag ps_props k (by omega) props val_c ps_c heq_content)

-- Extraction
theorem parseNode_aliases_resolve'
    (ps : ParseStateIx input) (fuel : Nat) (val : YamlValue) (ps' : ParseStateIx input)
    (h : parseNode ps fuel = .ok (val, ps')) :
    AllAliasesResolve val ps'.anchors :=
  parseNode_aar_all fuel ps fuel val ps' Nat.le.refl h

end L4YAML.Proofs.Indexed.NodeProofs
