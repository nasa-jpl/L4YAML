/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Spec.Grammar
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Parser.ParserGrammableBase
public import L4YAML.Parser.ParseStateIx
public import L4YAML.Parser.FuelIx
public import L4YAML.Parser.TokenParserIx

-- `unfold Std.Legacy.Range.forIn'` needs that body, which core does not expose
-- to a module consumer.  `import all` of its DECLARING module unseals it and
-- is private in scope, so nothing reaches this module's own importers.
import all Init.Data.Range.Basic
-- This module's `elab` bodies are `meta` definitions, while the helpers they
-- call are ordinary code that the library also uses at runtime.  A declaration
-- carries one phase and the `meta` modifier cannot be dropped retroactively,
-- so mixed references inside this module need to be permitted explicitly.
set_option compiler.relaxedMetaCheck true

@[expose] public section Blanket

/-! # `IndexedNodeProofs` — Phase 3 Step 6c indexed AG + AAR proofs

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
lemma any_name_implies_findSome_isSome'
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

/-- A segment across which both anchor registers only grow.  Stated as a
    conjunction of projections rather than as a structure for the reason the
    legacy twin gives (`ParserNodeProofs.AG0`): the parser's states differ in
    fields this relation says nothing about, and a proposition that reads only
    the two registers unifies across those record updates definitionally. -/
def AG0 (ps ps' : ParseStateIx input) : Prop :=
  (∀ i : Fin ps.anchors.size, ∃ j : Fin ps'.anchors.size,
      ps'.anchors[j] = ps.anchors[i]) ∧
  (∀ nm, nm ∈ ps.declaredAnchors → nm ∈ ps'.declaredAnchors)

/-- `AG0`, plus: no declaration outlives the segment that left it unbound.
    `parseNodeProperties` is the one segment without it — §7.1's register is
    written at the `&` and the matching value exists only after the node is
    complete — so that stage concludes in `AG0`. -/
def AG (ps ps' : ParseStateIx input) : Prop :=
  AG0 ps ps' ∧
  (∀ nm, nm ∈ ps'.declaredAnchors →
      nm ∈ ps.declaredAnchors ∨ AnchorBound ps'.anchors nm)

variable {ps ps' ps1 ps2 ps3 : ParseStateIx input}

lemma AG0.anchorsGrow (h : AG0 ps ps') :
    ∀ i : Fin ps.anchors.size, ∃ j : Fin ps'.anchors.size,
      ps'.anchors[j] = ps.anchors[i] := h.1
lemma AG0.declsGrow (h : AG0 ps ps') :
    ∀ nm, nm ∈ ps.declaredAnchors → nm ∈ ps'.declaredAnchors := h.2
lemma AG.toAG0 (h : AG ps ps') : AG0 ps ps' := h.1
lemma AG.anchorsGrow (h : AG ps ps') :
    ∀ i : Fin ps.anchors.size, ∃ j : Fin ps'.anchors.size,
      ps'.anchors[j] = ps.anchors[i] := h.1.1
lemma AG.declsGrow (h : AG ps ps') :
    ∀ nm, nm ∈ ps.declaredAnchors → nm ∈ ps'.declaredAnchors := h.1.2
lemma AG.declsBound (h : AG ps ps') :
    ∀ nm, nm ∈ ps'.declaredAnchors →
      nm ∈ ps.declaredAnchors ∨ AnchorBound ps'.anchors nm := h.2

lemma AG0.refl : AG0 ps ps := ⟨fun i => ⟨i, rfl⟩, fun _ h => h⟩
lemma AG0.trans (h12 : AG0 ps1 ps2) (h23 : AG0 ps2 ps3) : AG0 ps1 ps3 := by
  refine ⟨fun i => ?_, fun nm h => h23.declsGrow nm (h12.declsGrow nm h)⟩
  obtain ⟨j, hj⟩ := h12.anchorsGrow i; obtain ⟨k, hk⟩ := h23.anchorsGrow j
  exact ⟨k, hk ▸ hj⟩

lemma AG.refl : AG ps ps := ⟨AG0.refl, fun _ h => Or.inl h⟩

lemma AG.trans (h12 : AG ps1 ps2) (h23 : AG ps2 ps3) : AG ps1 ps3 := by
  refine ⟨h12.toAG0.trans h23.toAG0, fun nm hnm => ?_⟩
  rcases h23.declsBound nm hnm with h | h
  · rcases h12.declsBound nm h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (AnchorBound.mono h23.anchorsGrow h')
  · exact Or.inr h

/-- A segment that leaves the resolution table alone and only appends to the
    declaration set.  Every arm of the properties stage has this shape. -/
lemma AG0.of_anchors_eq (h : ps'.anchors = ps.anchors)
    (hd : ∀ nm, nm ∈ ps.declaredAnchors → nm ∈ ps'.declaredAnchors) : AG0 ps ps' :=
  ⟨fun ⟨i, hi⟩ => ⟨⟨i, h ▸ hi⟩, by simp [h]⟩, hd⟩

lemma AG.of_eq (h : ps'.anchors = ps.anchors)
    (hd : ps'.declaredAnchors = ps.declaredAnchors) : AG ps ps' := by
  refine ⟨AG0.of_anchors_eq h (fun nm hm => by rw [hd]; exact hm), fun nm hm => ?_⟩
  rw [hd] at hm; exact Or.inl hm

lemma AG.advance (ps : ParseStateIx input) : AG ps ps.advance :=
  AG.of_eq (by simp [ParseStateIx.advance]) (by simp [ParseStateIx.advance])
lemma AG.withField (ps : ParseStateIx input) (p : YamlPath) :
    AG ps { ps with currentPath := p } := AG.of_eq rfl rfl
lemma AG.tryConsume (ps : ParseStateIx input) (tok : YamlToken) :
    AG ps (ps.tryConsume tok).2 := by
  unfold ParseStateIx.tryConsume
  split
  · split
    · exact AG.advance ps
    · exact AG.refl
  · exact AG.refl

-- tryConsume preserves anchors (needed for unification in AAR proofs)
@[simp] lemma tryConsume_snd_anchors (ps : ParseStateIx input) (tok : YamlToken) :
    (ps.tryConsume tok).snd.anchors = ps.anchors := by
  unfold ParseStateIx.tryConsume; split <;> (try split) <;> simp [ParseStateIx.advance]

-- and the declaration set likewise (needed for unification in the AAD proofs)
@[simp] lemma tryConsume_snd_decls (ps : ParseStateIx input) (tok : YamlToken) :
    (ps.tryConsume tok).snd.declaredAnchors = ps.declaredAnchors := by
  unfold ParseStateIx.tryConsume; split <;> (try split) <;> simp [ParseStateIx.advance]

/-- `addAnchor` writes the resolution table and nothing else. -/
@[simp] lemma addAnchor_decls (ps : ParseStateIx input) (name : String) (v : YamlValue) :
    (ps.addAnchor name v).declaredAnchors = ps.declaredAnchors := by
  unfold ParseStateIx.addAnchor; rfl

/-- Finalization writes the resolution table and never the declaration set, so
    its `declsBound` is the trivial half. -/
@[simp] lemma applyNodeFinalization_decls
    (val : YamlValue) (ps : ParseStateIx input) (props : NodeProperties)
    (nodeStartPos : YamlPos) :
    (applyNodeFinalization val ps props nodeStartPos).2.declaredAnchors
      = ps.declaredAnchors := by
  rcases props with ⟨anchor, tag, dup⟩
  simp only [applyNodeFinalization]
  cases anchor <;> split <;> (try split) <;> (try split) <;>
    (first | rfl | contradiction)

/-- G5c position tracking writes `nodePositions` and reads no anchor register. -/
lemma anchors_of_recordPos (ps : ParseStateIx input) (nodeStartPos : YamlPos) :
    (if ps.trackPositions = true then
       { ps with nodePositions :=
           ps.nodePositions.push (ps.currentPath, nodeStartPos,
             ps.lastPos?.getD nodeStartPos) }
     else ps).anchors = ps.anchors := by
  split <;> rfl

/-- Finalization BINDS the anchor its properties carry: the other half of the
    pair that `parseNodeProperties` leaves open. -/
lemma applyNodeFinalization_binds
    (val : YamlValue) (ps : ParseStateIx input) (props : NodeProperties)
    (nodeStartPos : YamlPos) (nm : String) (h : props.anchor = some nm) :
    AnchorBound (applyNodeFinalization val ps props nodeStartPos).2.anchors nm := by
  rcases props with ⟨anchor, tag, dup⟩
  cases anchor with
  | none => exact absurd h (by simp)
  | some name =>
    have h_eq : name = nm := by simpa using h
    subst h_eq
    simp only [applyNodeFinalization]
    rw [anchors_of_recordPos]
    simp only [ParseStateIx.addAnchor]
    exact AnchorBound.push_self _ _ _

lemma applyNodeFinalization_ag
    (val : YamlValue) (ps : ParseStateIx input) (props : NodeProperties)
    (nodeStartPos : YamlPos) :
    AG ps (applyNodeFinalization val ps props nodeStartPos).2 := by
  refine ⟨⟨?_, fun _ h => by simpa using h⟩, fun _ h => Or.inl (by simpa using h)⟩
  intro ⟨i, hi⟩
  rcases props with ⟨anchor, tag, dup⟩
  cases anchor with
  | none =>
    simp only [applyNodeFinalization]
    refine ⟨⟨i, ?_⟩, ?_⟩
    · split <;> exact hi
    · split <;> rfl
  | some name =>
    -- 4.33: keep `addAnchor` out of the pre-split simp — see the legacy twin
    -- (ParserNodeProofs.applyNodeFinalization_ag) for the mechanism.
    simp only [applyNodeFinalization]
    refine ⟨⟨i, ?_⟩, ?_⟩
    · split <;> (simp [ParseStateIx.addAnchor, Array.size_push]; omega)
    · split <;>
        (simp [ParseStateIx.addAnchor, Array.getElem_push, show i < ps.anchors.size from hi])

/-! ## ParseNodeAG induction hypothesis -/

def ParseNodeAG (input : String) (n : Nat) : Prop :=
  ∀ (ps : ParseStateIx input) (m : Nat) (val : YamlValue) (ps' : ParseStateIx input),
    m ≤ n → parseNode ps m = .ok (val, ps') → AG ps ps'

variable {n : Nat}

/-! ## Sub-parser AG lemmas: block sequences -/

lemma parseBlockSequenceLoop_ag (h_ih : ParseNodeAG input n)
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

lemma parseBlockSequence_ag (h_ih : ParseNodeAG input n)
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

lemma parseImplicitBlockSequenceLoop_ag (h_ih : ParseNodeAG input n)
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

lemma parseImplicitBlockSequence_ag (h_ih : ParseNodeAG input n)
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

lemma parseBlockMappingEntryValue_ag (h_ih : ParseNodeAG input n)
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
  · -- consumed = false: retroactive-key skip (V9D5) or empty value.
    -- Prefix AG across the skipped retroactive `key` + consumed `:` — both are
    -- pure position advances, so anchors are preserved.
    have h_pre : AG ps (((ps.tryConsume .value).2.tryConsume .key).2.tryConsume .value).2 :=
      AG.trans h_tc (AG.trans (AG.tryConsume _ _) (AG.tryConsume _ _))
    split at h_ok                    -- outer: peek?, peekNext?
    all_goals (try (split at h_ok))  -- inner: peek? dispatch in the retroactive arm
    all_goals (first
      | (obtain ⟨rfl, rfl⟩ := h_ok; exact h_tc)
      | (obtain ⟨rfl, rfl⟩ := h_ok; exact h_pre)
      | exact AG.trans h_pre (h_ih _ fuel _ _ h_fuel h_ok))

-- handleBlockMappingKeyEntry: advance → if keyHasContent → parseNode/emptyNode → BEV → restore path
set_option maxHeartbeats 400000 in
lemma handleBlockMappingKeyEntry_ag (h_ih : ParseNodeAG input n)
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

lemma handleBlockMappingValueEntry_ag (h_ih : ParseNodeAG input n)
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

lemma parseBlockMappingLoop_ag (h_ih : ParseNodeAG input n)
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

lemma parseBlockMapping_ag (h_ih : ParseNodeAG input n)
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
lemma parseExplicitKey_ag (h_ih : ParseNodeAG input n)
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
lemma parseFlowMappingValue_ag (h_ih : ParseNodeAG input n)
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
lemma parseSinglePairMapping_ag (h_ih : ParseNodeAG input n)
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
    -- 4.33: `emptyNode` stays folded through the splits — see the legacy twin.
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
lemma parseFlowSequenceLoop_ag (h_ih : ParseNodeAG input n)
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

lemma parseFlowSequence_ag (h_ih : ParseNodeAG input n)
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
lemma parseFlowMappingLoop_ag (h_ih : ParseNodeAG input n)
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

lemma parseFlowMapping_ag (h_ih : ParseNodeAG input n)
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
/-- The one shape every arm of the properties stage has: the resolution table
    is untouched, the loop leaves the declaration set alone, and the stage's
    tail appends exactly the anchor the computed properties carry. -/
lemma propsStage_ag0 (ps : ParseStateIx input) (o : Option String)
    (ps_loop : ParseStateIx input)
    (h : ps_loop.anchors = ps.anchors)
    (hd : ps_loop.declaredAnchors = ps.declaredAnchors) :
    AG0 ps (ps_loop.declareAnchorOpt o) ∧
      ∀ nm, nm ∈ (ps_loop.declareAnchorOpt o).declaredAnchors →
        nm ∈ ps.declaredAnchors ∨ o = some nm := by
  cases o with
  | none =>
    refine ⟨AG0.of_anchors_eq h (fun nm hm => ?_), fun nm hm => ?_⟩
    · simp only [ParseStateIx.declareAnchorOpt_none]; rw [hd]; exact hm
    · simp only [ParseStateIx.declareAnchorOpt_none] at hm
      rw [hd] at hm; exact Or.inl hm
  | some name =>
    refine ⟨AG0.of_anchors_eq (by simpa [ParseStateIx.declareAnchor] using h)
      (fun nm hm => ?_), fun nm hm => ?_⟩
    · simp only [ParseStateIx.declareAnchorOpt_some, ParseStateIx.declareAnchor,
        Array.mem_push, hd]
      exact Or.inl hm
    · simp only [ParseStateIx.declareAnchorOpt_some, ParseStateIx.declareAnchor,
        Array.mem_push, hd] at hm
      rcases hm with hm | rfl
      · exact Or.inl hm
      · exact Or.inr rfl

/-- The properties stage is the one segment of the clique with no `declsBound`,
    so it concludes in `AG0` and reports what it declared;
    `parseNode_ag_all` pays the missing half where the matching
    `applyNodeFinalization` is in scope. -/
lemma parseNodeProperties_ag
    (ps : ParseStateIx input) (props : NodeProperties) (ps' : ParseStateIx input)
    (h_ok : parseNodeProperties ps = .ok (props, ps')) :
    AG0 ps ps' ∧ ∀ nm, nm ∈ ps'.declaredAnchors →
      nm ∈ ps.declaredAnchors ∨ props.anchor = some nm := by
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
    -- Both components are needed now, not just the state: the conclusion names
    -- the anchor the COMPUTED properties carry.
    obtain ⟨rfl, rfl⟩ := h_ok
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
        all_goals ((try dsimp only []); apply propsStage_ag0 <;>
          (first | rfl | simp [ParseStateIx.advance]))
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
            all_goals ((try dsimp only []); apply propsStage_ag0 <;>
              (first | rfl | simp [ParseStateIx.advance]))
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
            all_goals ((try dsimp only []); apply propsStage_ag0 <;>
              (first | rfl | simp [ParseStateIx.advance]))

/-! ## parseNodeContent AG -/

lemma parseNodeContent_ag (h_ih : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (props : NodeProperties) (isSeqEntry : Bool) (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseNodeContent ps fuel props isSeqEntry = .ok (val, ps')) :
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
  · -- blockEntry: empty scalar (seq-entry context, C2) or implicit block sequence
    split at h_ok
    · -- isSeqEntry: empty scalar, no state change (C2)
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
      exact AG.refl
    · -- otherwise: implicit block sequence
      exact parseImplicitBlockSequence_ag h_ih ps fuel (by omega) val ps' h_ok
  · -- flowSequenceStart
    exact parseFlowSequence_ag h_ih ps fuel (by omega) val ps' h_ok
  · -- flowMappingStart
    exact parseFlowMapping_ag h_ih ps fuel (by omega) val ps' h_ok
  · -- empty node: no state change
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
    exact AG.refl

/-- `declsBound` for the properties/finalization pair: neither half has it and
    their composition does.  See the legacy twin for the argument. -/
lemma declsBound_of_props_finalization
    (val_c : YamlValue) (ps ps_props ps_c : ParseStateIx input)
    (props : NodeProperties) (pos : YamlPos)
    (h_props : ∀ nm, nm ∈ ps_props.declaredAnchors →
        nm ∈ ps.declaredAnchors ∨ props.anchor = some nm)
    (h_content : AG ps_props ps_c) :
    ∀ nm, nm ∈ (applyNodeFinalization val_c ps_c props pos).2.declaredAnchors →
      nm ∈ ps.declaredAnchors ∨
        AnchorBound (applyNodeFinalization val_c ps_c props pos).2.anchors nm := by
  intro nm hnm
  rw [applyNodeFinalization_decls] at hnm
  rcases h_content.declsBound nm hnm with h_decl | h_bound
  · rcases h_props nm h_decl with h_old | h_anchor
    · exact Or.inl h_old
    · exact Or.inr (applyNodeFinalization_binds _ _ _ _ nm h_anchor)
  · exact Or.inr (AnchorBound.mono
      (applyNodeFinalization_ag val_c ps_c props pos).anchorsGrow h_bound)

/-! ## Main theorem: parseNode AG by strong induction -/

set_option maxHeartbeats 400000 in
lemma parseNode_ag_all : ∀ n, ParseNodeAG input n := by
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
            have h_ag_content := parseNodeContent_ag h_pnag ps_props k h_k_le props _ val_c ps_c heq_content
            -- applyNodeFinalization: h_ok now says .ok (finalize ...) = .ok (val, ps')
            simp only [Except.ok.injEq] at h_ok
            obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
            -- The one place in the clique where a declaration and its
            -- binding meet, as in the legacy twin.
            exact ⟨AG0.trans h_ag_props.1 (AG0.trans h_ag_content.toAG0
                (applyNodeFinalization_ag val_c ps_c props _).toAG0),
              declsBound_of_props_finalization val_c ps ps_props ps_c props _
                h_ag_props.2 h_ag_content⟩

/-! ## Extract the target theorem -/

lemma parseNode_anchors_grow (ps : ParseStateIx input) (n : Nat)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseNode ps n = .ok (val, ps')) :
    ∀ i : Fin ps.anchors.size, ∃ j : Fin ps'.anchors.size,
      ps'.anchors[j] = ps.anchors[i] :=
  (parseNode_ag_all n ps n val ps' Nat.le.refl h_ok).anchorsGrow

/-! ## The §7.1 reading, per node (AAD proofs)

The indexed twin of `ParserNodeProofs`' §7.1 clique: the parse-side obligation
is carried by `AllAliasesDeclared` over the DECLARATION set, because a
collection's own anchor occurs at its start event and is bound only once its
items are complete.  The resolution reading is recovered at the document
boundary in `IndexedGrammable`. -/

-- Abbreviation for the ParseNode-level AAD property
def ParseNodeAAD (input : String) (n : Nat) : Prop :=
  ∀ (ps : ParseStateIx input) (m : Nat) (val : YamlValue) (ps' : ParseStateIx input),
    m ≤ n → parseNode ps m = .ok (val, ps') →
      AllAliasesDeclared val ps'.declaredAnchors

-- AAD.mono: a segment's declaration growth carries the §7.1 reading forward
lemma aad_mono {val : YamlValue} {ps ps' : ParseStateIx input} (h_ag : AG ps ps')
    (h : AllAliasesDeclared val ps.declaredAnchors) :
    AllAliasesDeclared val ps'.declaredAnchors :=
  AllAliasesDeclared.mono h_ag.declsGrow h

-- Helper: changing tag/anchor fields preserves AAD
lemma aad_retag_sequence (names : Array String)
    {style : CollectionStyle} {items : Array YamlValue}
    {t1 a1 : Option String} (t2 a2 : Option String)
    (h : AllAliasesDeclared (.sequence style items t1 a1) names) :
    AllAliasesDeclared (.sequence style items t2 a2) names := by
  cases h with | sequence _ _ _ _ _ hi => exact .sequence _ _ _ _ _ hi

lemma aad_retag_mapping (names : Array String)
    {style : CollectionStyle} {pairs : Array (YamlValue × YamlValue)}
    {t1 a1 : Option String} (t2 a2 : Option String)
    (h : AllAliasesDeclared (.mapping style pairs t1 a1) names) :
    AllAliasesDeclared (.mapping style pairs t2 a2) names := by
  cases h with | mapping _ _ _ _ _ hk hv => exact .mapping _ _ _ _ _ hk hv

/-- Finalization retags the value and writes the resolution table; it declares
    nothing, so the §7.1 reading passes through it without a monotonicity
    step. -/
lemma applyNodeFinalization_aad
    (val : YamlValue) (ps : ParseStateIx input) (props : NodeProperties)
    (nodeStartPos : YamlPos)
    (h_aad : AllAliasesDeclared val ps.declaredAnchors) :
    AllAliasesDeclared (applyNodeFinalization val ps props nodeStartPos).1
        (applyNodeFinalization val ps props nodeStartPos).2.declaredAnchors := by
  rw [applyNodeFinalization_decls]
  rcases props with ⟨anchor, tag, dup⟩
  unfold applyNodeFinalization
  cases val with
  | scalar => exact h_aad
  | alias => exact h_aad
  | sequence style items otag oanchor =>
    cases otag <;> cases oanchor <;>
      (dsimp only []; first | exact aad_retag_sequence _ tag anchor h_aad | exact h_aad)
  | mapping style pairs otag oanchor =>
    cases otag <;> cases oanchor <;>
      (dsimp only []; first | exact aad_retag_mapping _ tag anchor h_aad | exact h_aad)

/-! ## The §7.1 reading: sub-parser proofs -/

-- Helper: emptyNode carries no alias
lemma emptyNode_aad (names : Array String) :
    AllAliasesDeclared emptyNode names := by
  unfold emptyNode; exact .scalar _ _

-- Helper: push preserves the items invariant
lemma items_push_aad
    {items : Array YamlValue} {val : YamlValue} {ps ps' : ParseStateIx input}
    (h_ag : AG ps ps')
    (h_pre : ∀ i : Fin items.size, AllAliasesDeclared items[i] ps.declaredAnchors)
    (h_new : AllAliasesDeclared val ps'.declaredAnchors) :
    ∀ i : Fin (items.push val).size,
      AllAliasesDeclared (items.push val)[i] ps'.declaredAnchors := by
  intro ⟨i, hi⟩
  simp [Array.getElem_push]
  split
  next h => exact aad_mono h_ag (h_pre ⟨i, h⟩)
  next => exact h_new

-- Helper: push preserves the pairs invariant
lemma pairs_push_aad
    {pairs : Array (YamlValue × YamlValue)} {key val : YamlValue}
    {ps ps' : ParseStateIx input}
    (h_ag : AG ps ps')
    (h_pre_k : ∀ i : Fin pairs.size, AllAliasesDeclared pairs[i].1 ps.declaredAnchors)
    (h_pre_v : ∀ i : Fin pairs.size, AllAliasesDeclared pairs[i].2 ps.declaredAnchors)
    (h_new_k : AllAliasesDeclared key ps'.declaredAnchors)
    (h_new_v : AllAliasesDeclared val ps'.declaredAnchors) :
    (∀ i : Fin (pairs.push (key, val)).size,
        AllAliasesDeclared (pairs.push (key, val))[i].1 ps'.declaredAnchors) ∧
    (∀ i : Fin (pairs.push (key, val)).size,
        AllAliasesDeclared (pairs.push (key, val))[i].2 ps'.declaredAnchors) := by
  constructor <;> intro ⟨i, hi⟩ <;> (
    simp [Array.getElem_push]
    split
    next h => first | exact aad_mono h_ag (h_pre_k ⟨i, h⟩)
                    | exact aad_mono h_ag (h_pre_v ⟨i, h⟩)
    next => first | exact h_new_k | exact h_new_v)

lemma parseBlockSequenceLoop_aad (h_ih_aad : ParseNodeAAD input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (items : Array YamlValue)
    (h_fuel : fuel ≤ n + 1)
    (result : Array YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseBlockSequenceLoop ps fuel items = .ok (result, ps'))
    (h_pre : ∀ i : Fin items.size, AllAliasesDeclared items[i] ps.declaredAnchors) :
    (∀ i : Fin result.size, AllAliasesDeclared result[i] ps'.declaredAnchors) := by
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
          (items_push_aad (AG.advance ps) h_pre (emptyNode_aad _))
      · exact ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok
          (items_push_aad (AG.advance ps) h_pre (emptyNode_aad _))
      · exact ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok
          (items_push_aad (AG.advance ps) h_pre (emptyNode_aad _))
      -- non-empty entry: parseNode then recurse
      · split at h_ok
        · simp at h_ok
        · rename_i pn_res heq_pn
          obtain ⟨val_n, ps_n⟩ := pn_res
          dsimp only [] at h_ok
          have h_ag_n := h_ih_ag _ k val_n ps_n (by omega) heq_pn
          have h_aad_n := h_ih_aad _ k val_n ps_n (by omega) heq_pn
          exact ih_fuel _ (items.push val_n) (by omega) h_ok
            (items_push_aad
              (AG.trans (AG.advance ps)
                (AG.trans (AG.withField ps.advance _)
                  (AG.trans h_ag_n (AG.withField ps_n _))))
              h_pre h_aad_n)
    · -- not blockEntry
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact h_pre

-- Block sequence wrapper AAD
lemma parseBlockSequence_aad (h_ih_aad : ParseNodeAAD input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseBlockSequence ps fuel = .ok (val, ps')) :
    AllAliasesDeclared val ps'.declaredAnchors := by
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
        have h_items := parseBlockSequenceLoop_aad h_ih_aad h_ih_ag
          ps.advance k #[] (by omega) items_r ps_r heq_loop
          (fun ⟨i, hi⟩ => absurd hi (Nat.not_lt_zero _))
        first
        | exact .sequence _ _ _ _ _ h_items
        | (have : ps'.declaredAnchors = ps_r.declaredAnchors := rfl
           rw [this]; exact .sequence _ _ _ _ _ h_items))

-- Implicit block sequence loop AAD
lemma parseImplicitBlockSequenceLoop_aad (h_ih_aad : ParseNodeAAD input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (items : Array YamlValue)
    (h_fuel : fuel ≤ n + 1)
    (result : Array YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseImplicitBlockSequenceLoop ps fuel items = .ok (result, ps'))
    (h_pre : ∀ i : Fin items.size, AllAliasesDeclared items[i] ps.declaredAnchors) :
    (∀ i : Fin result.size, AllAliasesDeclared result[i] ps'.declaredAnchors) := by
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
          (items_push_aad (AG.advance ps) h_pre (emptyNode_aad _))
      · exact ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok
          (items_push_aad (AG.advance ps) h_pre (emptyNode_aad _))
      · exact ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok
          (items_push_aad (AG.advance ps) h_pre (emptyNode_aad _))
      · exact ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok
          (items_push_aad (AG.advance ps) h_pre (emptyNode_aad _))
      -- non-empty entry: parseNode then recurse
      · split at h_ok
        · simp at h_ok
        · rename_i pn_res heq_pn
          obtain ⟨val_n, ps_n⟩ := pn_res
          dsimp only [] at h_ok
          have h_ag_n := h_ih_ag _ k val_n ps_n (by omega) heq_pn
          have h_aad_n := h_ih_aad _ k val_n ps_n (by omega) heq_pn
          exact ih_fuel _ (items.push val_n) (by omega) h_ok
            (items_push_aad
              (AG.trans (AG.advance ps)
                (AG.trans (AG.withField ps.advance _)
                  (AG.trans h_ag_n (AG.withField ps_n _))))
              h_pre h_aad_n)
    · -- not blockEntry
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact h_pre

-- Implicit block sequence wrapper AAD
lemma parseImplicitBlockSequence_aad (h_ih_aad : ParseNodeAAD input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseImplicitBlockSequence ps fuel = .ok (val, ps')) :
    AllAliasesDeclared val ps'.declaredAnchors := by
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
      have h_items := parseImplicitBlockSequenceLoop_aad h_ih_aad h_ih_ag
        ps k #[] (by omega) items_r ps_r heq_loop
        (fun ⟨i, hi⟩ => absurd hi (Nat.not_lt_zero _))
      exact .sequence _ _ _ _ _ h_items

/-! ### Block mapping AAD -/

-- parseBlockMappingEntryValue: value is emptyNode or parseNode result
lemma parseBlockMappingEntryValue_aad (h_ih_aad : ParseNodeAAD input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (keyHasContent : Bool) (keyLine keyCol : Nat)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseBlockMappingEntryValue ps fuel keyHasContent keyLine keyCol = .ok (val, ps')) :
    AllAliasesDeclared val ps'.declaredAnchors := by
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
    all_goals try (obtain ⟨rfl, rfl⟩ := h_ok; exact emptyNode_aad _)
    -- parseNode case: val from parseNode
    all_goals exact h_ih_aad _ fuel _ _ h_fuel h_ok
  · -- consumed = false: retroactive-key skip (V9D5) or empty value.
    -- Value is either emptyNode (both fallback and retroactive empty cases) or a
    -- parseNode result (retroactive collection value) — AAD holds for both.
    split at h_ok                    -- outer: peek?, peekNext?
    all_goals (try (split at h_ok))  -- inner: peek? dispatch in the retroactive arm
    all_goals (first
      | (obtain ⟨rfl, rfl⟩ := h_ok; exact emptyNode_aad _)
      | exact h_ih_aad _ fuel _ _ h_fuel h_ok)

-- handleBlockMappingKeyEntry: (key, val, ps') — both key and val AAD
set_option maxHeartbeats 400000 in
lemma handleBlockMappingKeyEntry_aad (h_ih_aad : ParseNodeAAD input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (pairIdx : Nat) (key val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : handleBlockMappingKeyEntry ps fuel pairIdx = .ok (key, val, ps')) :
    AllAliasesDeclared key ps'.declaredAnchors ∧ AllAliasesDeclared val ps'.declaredAnchors := by
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
    aad_mono (AG.trans (AG.withField _ _)
        (AG.trans (parseBlockMappingEntryValue_ag h_ih_ag _ _ h_fuel _ _ _ _ _ (by assumption))
          (AG.withField _ _)))
      (emptyNode_aad _),
    aad_mono (AG.withField _ _)
      (parseBlockMappingEntryValue_aad h_ih_aad _ _ h_fuel _ _ _ _ _ (by assumption))⟩
  -- Close: parseNode key + BEV value
  all_goals try exact ⟨
    aad_mono (AG.trans (AG.withField _ _)
        (AG.trans (parseBlockMappingEntryValue_ag h_ih_ag _ _ h_fuel _ _ _ _ _ (by assumption))
          (AG.withField _ _)))
      (h_ih_aad _ fuel _ _ h_fuel (by assumption)),
    aad_mono (AG.withField _ _)
      (parseBlockMappingEntryValue_aad h_ih_aad _ _ h_fuel _ _ _ _ _ (by assumption))⟩

-- handleBlockMappingValueEntry: (val, ps') — val is emptyNode or parseNode
lemma handleBlockMappingValueEntry_aad (h_ih_aad : ParseNodeAAD input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (pairIdx : Nat) (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : handleBlockMappingValueEntry ps fuel pairIdx = .ok (val, ps')) :
    AllAliasesDeclared val ps'.declaredAnchors := by
  unfold handleBlockMappingValueEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  -- emptyNode cases (some .key, some .blockEnd, none)
  · simp only [Except.ok.injEq] at h_ok; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact emptyNode_aad _
  · simp only [Except.ok.injEq] at h_ok; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact emptyNode_aad _
  · simp only [Except.ok.injEq] at h_ok; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact emptyNode_aad _
  -- parseNode case (catch-all)
  · split at h_ok
    · simp at h_ok
    · rename_i pn_res heq_pn
      obtain ⟨v, ps_n⟩ := pn_res
      dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
      exact aad_mono (AG.withField ps_n _) (h_ih_aad _ fuel v ps_n h_fuel heq_pn)

-- Block mapping loop AAD
lemma parseBlockMappingLoop_aad (h_ih_aad : ParseNodeAAD input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (pairs : Array (YamlValue × YamlValue))
    (h_fuel : fuel ≤ n + 1)
    (result : Array (YamlValue × YamlValue)) (ps' : ParseStateIx input)
    (h_ok : parseBlockMappingLoop ps fuel pairs = .ok (result, ps'))
    (h_pre_k : ∀ i : Fin pairs.size, AllAliasesDeclared pairs[i].1 ps.declaredAnchors)
    (h_pre_v : ∀ i : Fin pairs.size, AllAliasesDeclared pairs[i].2 ps.declaredAnchors) :
    (∀ i : Fin result.size, AllAliasesDeclared result[i].1 ps'.declaredAnchors) ∧
    (∀ i : Fin result.size, AllAliasesDeclared result[i].2 ps'.declaredAnchors) := by
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
        have ⟨h_k, h_v⟩ := handleBlockMappingKeyEntry_aad h_ih_aad h_ih_ag
            ps k (by omega) _ key_v val_v ps_entry heq_entry
        have h_ag_entry := handleBlockMappingKeyEntry_ag h_ih_ag ps k (by omega)
            _ key_v val_v ps_entry heq_entry
        have ⟨h_pk, h_pv⟩ := pairs_push_aad h_ag_entry h_pre_k h_pre_v h_k h_v
        exact ih_fuel ps_entry _ (by omega) h_ok h_pk h_pv
    · -- value (implicit key)
      split at h_ok
      · simp at h_ok
      · rename_i val_res heq_val
        obtain ⟨val_v, ps_val⟩ := val_res
        dsimp only [] at h_ok
        have h_v := handleBlockMappingValueEntry_aad h_ih_aad
            ps k (by omega) _ val_v ps_val heq_val
        have h_ag_val := handleBlockMappingValueEntry_ag h_ih_ag ps k (by omega)
            _ val_v ps_val heq_val
        have ⟨h_pk, h_pv⟩ := pairs_push_aad h_ag_val h_pre_k h_pre_v
            (aad_mono h_ag_val (emptyNode_aad _)) h_v
        exact ih_fuel ps_val _ (by omega) h_ok h_pk h_pv
    · -- not key/value
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact ⟨h_pre_k, h_pre_v⟩

-- Block mapping wrapper AAD
lemma parseBlockMapping_aad (h_ih_aad : ParseNodeAAD input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseBlockMapping ps fuel = .ok (val, ps')) :
    AllAliasesDeclared val ps'.declaredAnchors := by
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
        have ⟨hk, hv⟩ := parseBlockMappingLoop_aad h_ih_aad h_ih_ag
          ps.advance k #[] (by omega) pairs_r ps_r heq_loop
          (fun ⟨i, hi⟩ => absurd hi (Nat.not_lt_zero _))
          (fun ⟨i, hi⟩ => absurd hi (Nat.not_lt_zero _))
        first
        | exact .mapping _ _ _ _ _ hk hv
        | (have : ps'.declaredAnchors = ps_r.declaredAnchors := rfl
           rw [this]; exact .mapping _ _ _ _ _ hk hv))

/-! ### Flow parser AAD -/

-- parseExplicitKey: emptyNode or parseNode
lemma parseExplicitKey_aad (h_ih_aad : ParseNodeAAD input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseExplicitKey ps fuel = .ok (val, ps')) :
    AllAliasesDeclared val ps'.declaredAnchors := by
  unfold parseExplicitKey at h_ok
  split at h_ok
  all_goals (try (obtain ⟨rfl, rfl⟩ := h_ok; exact emptyNode_aad _))
  · exact h_ih_aad _ fuel _ _ h_fuel h_ok

-- parseFlowMappingValue: emptyNode or parseNode
lemma parseFlowMappingValue_aad (h_ih_aad : ParseNodeAAD input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (savedPath : YamlPath) (keyContent : String)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseFlowMappingValue ps fuel savedPath keyContent = .ok (val, ps')) :
    AllAliasesDeclared val ps'.declaredAnchors := by
  unfold parseFlowMappingValue at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · -- consumed value token
    split at h_ok
    -- emptyNode cases
    all_goals (try (
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
      exact emptyNode_aad _))
    -- parseNode case
    · split at h_ok
      · simp at h_ok
      · rename_i pn_res heq_pn
        obtain ⟨v, ps_n⟩ := pn_res
        dsimp only [] at h_ok
        simp only [Except.ok.injEq] at h_ok
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
        exact aad_mono (AG.withField ps_n _) (h_ih_aad _ fuel v ps_n h_fuel heq_pn)
  · -- not consumed: emptyNode
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
    exact emptyNode_aad _

-- parseSinglePairMapping: creates .mapping .flow #[(key, val)]
-- Helper for single-pair mapping AAD close
lemma spm_close (names : Array String) (k v : YamlValue)
    (hk : AllAliasesDeclared k names) (hv : AllAliasesDeclared v names) :
    AllAliasesDeclared (.mapping .flow #[(k, v)]) names := by
  apply AllAliasesDeclared.mapping
  · intro ⟨i, hi⟩; match i, hi with | 0, _ => dsimp; exact hk
  · intro ⟨i, hi⟩; match i, hi with | 0, _ => dsimp; exact hv

-- Helper: AAD from undestrutured parseNode result (avoids Prod.mk unification issue)
lemma aad_of_parseNode (h_ih : ParseNodeAAD input n)
    (ps : ParseStateIx input) (k : Nat) (res : YamlValue × ParseStateIx input)
    (h_fuel : k ≤ n) (h_ok : parseNode ps k = .ok res) :
    AllAliasesDeclared res.fst res.snd.declaredAnchors :=
  h_ih ps k res.fst res.snd h_fuel (by rw [← Prod.eta res]; exact h_ok)

set_option maxHeartbeats 800000 in
lemma parseSinglePairMapping_aad (h_ih_aad : ParseNodeAAD input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseSinglePairMapping ps fuel = .ok (val, ps')) :
    AllAliasesDeclared val ps'.declaredAnchors := by
  unfold parseSinglePairMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    -- Blind split pattern (matching AG proof)
    split at h_ok <;> first | contradiction | skip
    -- 4.33: `emptyNode` stays folded through the splits — see the legacy twin.
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
    all_goals (try simp only [tryConsume_snd_decls])
    -- Close goals by case
    all_goals try exact spm_close _ _ _ (emptyNode_aad _) (emptyNode_aad _)
    all_goals try (exact spm_close _ _ _ (emptyNode_aad _) (aad_of_parseNode h_ih_aad _ k _ (by omega) (by assumption)))
    all_goals try (exact spm_close _ _ _ (aad_of_parseNode h_ih_aad _ k _ (by omega) (by assumption)) (emptyNode_aad _))
    -- parseNode key + parseNode val: key needs aad_mono (AG from key to final)
    all_goals (
      apply spm_close
      · exact aad_mono
          (AG.trans (AG.withField _ _) (AG.trans (AG.tryConsume _ _)
            (AG.trans (h_ih_ag _ k _ _ (by omega) (by assumption)) (AG.withField _ _))))
          (aad_of_parseNode h_ih_aad _ k _ (by omega) (by assumption))
      · exact aad_of_parseNode h_ih_aad _ k _ (by omega) (by assumption))

-- Flow sequence loop AAD
lemma parseFlowSequenceLoop_aad (h_ih_aad : ParseNodeAAD input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (items : Array YamlValue)
    (h_fuel : fuel ≤ n + 1)
    (result : Array YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseFlowSequenceLoop ps fuel items = .ok (result, ps'))
    (h_pre : ∀ i : Fin items.size, AllAliasesDeclared items[i] ps.declaredAnchors) :
    (∀ i : Fin result.size, AllAliasesDeclared result[i] ps'.declaredAnchors) := by
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
              have h_spm_aad := parseSinglePairMapping_aad h_ih_aad h_ih_ag
                  _ k (by omega) map_val ps_spm heq_spm
              have h_spm_ag := parseSinglePairMapping_ag h_ih_ag
                  _ k (by omega) map_val ps_spm heq_spm
              exact ih_fuel _ (items.push map_val) (by omega) h_ok
                (items_push_aad
                  (AG.trans (AG.advance ps)
                    (AG.trans (AG.withField ps.advance _)
                      (AG.trans h_spm_ag (AG.withField ps_spm _))))
                  h_pre h_spm_aad)
          next => -- flowSequenceEnd
            simp only [Except.ok.injEq] at h_ok
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact h_pre
          next => -- parseNode
            split at h_ok
            · simp at h_ok
            · rename_i pn_res heq_pn
              obtain ⟨val_n, ps_n⟩ := pn_res
              dsimp only [] at h_ok
              have h_pn_aad := h_ih_aad _ k val_n ps_n (by omega) heq_pn
              have h_pn_ag := h_ih_ag _ k val_n ps_n (by omega) heq_pn
              exact ih_fuel _ (items.push val_n) (by omega) h_ok
                (items_push_aad
                  (AG.trans (AG.advance ps)
                    (AG.trans (AG.withField ps.advance _)
                      (AG.trans h_pn_ag (AG.withField ps_n _))))
                  h_pre h_pn_aad)
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
            have h_spm_aad := parseSinglePairMapping_aad h_ih_aad h_ih_ag
                _ k (by omega) map_val ps_spm heq_spm
            have h_spm_ag := parseSinglePairMapping_ag h_ih_ag
                _ k (by omega) map_val ps_spm heq_spm
            exact ih_fuel _ (items.push map_val) (by omega) h_ok
              (items_push_aad
                (AG.trans (AG.withField ps _) (AG.trans h_spm_ag (AG.withField ps_spm _)))
                h_pre h_spm_aad)
        next => -- flowSequenceEnd
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok; exact h_pre
        next => -- parseNode
          split at h_ok
          · simp at h_ok
          · rename_i pn_res heq_pn
            obtain ⟨val_n, ps_n⟩ := pn_res
            dsimp only [] at h_ok
            have h_pn_aad := h_ih_aad _ k val_n ps_n (by omega) heq_pn
            have h_pn_ag := h_ih_ag _ k val_n ps_n (by omega) heq_pn
            exact ih_fuel _ (items.push val_n) (by omega) h_ok
              (items_push_aad
                (AG.trans (AG.withField ps _) (AG.trans h_pn_ag (AG.withField ps_n _)))
                h_pre h_pn_aad)

-- Flow sequence wrapper AAD
lemma parseFlowSequence_aad (h_ih_aad : ParseNodeAAD input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseFlowSequence ps fuel = .ok (val, ps')) :
    AllAliasesDeclared val ps'.declaredAnchors := by
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
        have h_items := parseFlowSequenceLoop_aad h_ih_aad h_ih_ag
          ps.advance k #[] (by omega) items_r ps_r heq_loop
          (fun ⟨i, hi⟩ => absurd hi (Nat.not_lt_zero _))
        exact .sequence _ _ _ _ _ (fun i => aad_mono (AG.advance ps_r) (h_items i))
      · simp at h_ok

-- Flow mapping loop AAD
lemma parseFlowMappingLoop_aad (h_ih_aad : ParseNodeAAD input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (pairs : Array (YamlValue × YamlValue))
    (h_fuel : fuel ≤ n + 1)
    (result : Array (YamlValue × YamlValue)) (ps' : ParseStateIx input)
    (h_ok : parseFlowMappingLoop ps fuel pairs = .ok (result, ps'))
    (h_pre_k : ∀ i : Fin pairs.size, AllAliasesDeclared pairs[i].1 ps.declaredAnchors)
    (h_pre_v : ∀ i : Fin pairs.size, AllAliasesDeclared pairs[i].2 ps.declaredAnchors) :
    (∀ i : Fin result.size, AllAliasesDeclared result[i].1 ps'.declaredAnchors) ∧
    (∀ i : Fin result.size, AllAliasesDeclared result[i].2 ps'.declaredAnchors) := by
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
                have h_ek_aad := parseExplicitKey_aad h_ih_aad _ k (by omega) ek_v ps_ek heq_ek
                have h_fmv_aad := parseFlowMappingValue_aad h_ih_aad
                    ps_ek k (by omega) _ _ fmv_v ps_fmv heq_fmv
                have h_ag := AG.trans (AG.advance ps)
                  (AG.trans (AG.advance ps.advance)
                    (AG.trans (parseExplicitKey_ag h_ih_ag _ k (by omega) ek_v ps_ek heq_ek)
                      (parseFlowMappingValue_ag h_ih_ag ps_ek k (by omega) _ _ fmv_v ps_fmv heq_fmv)))
                have h_fmv_ag := parseFlowMappingValue_ag h_ih_ag ps_ek k (by omega) _ _ fmv_v ps_fmv heq_fmv
                have ⟨h_pk, h_pv⟩ := pairs_push_aad h_ag h_pre_k h_pre_v
                  (aad_mono h_fmv_ag h_ek_aad) h_fmv_aad
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
                have h_pn_aad := h_ih_aad _ k key_v ps_pn (by omega) heq_pn
                have h_fmv_aad := parseFlowMappingValue_aad h_ih_aad
                    ps_pn k (by omega) _ _ fmv_v ps_fmv heq_fmv
                have h_ag := AG.trans (AG.advance ps)
                  (AG.trans (h_ih_ag _ k key_v ps_pn (by omega) heq_pn)
                    (parseFlowMappingValue_ag h_ih_ag ps_pn k (by omega) _ _ fmv_v ps_fmv heq_fmv))
                have h_fmv_ag := parseFlowMappingValue_ag h_ih_ag ps_pn k (by omega) _ _ fmv_v ps_fmv heq_fmv
                have ⟨h_pk, h_pv⟩ := pairs_push_aad h_ag h_pre_k h_pre_v
                  (aad_mono h_fmv_ag h_pn_aad) h_fmv_aad
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
              have h_ek_aad := parseExplicitKey_aad h_ih_aad _ k (by omega) ek_v ps_ek heq_ek
              have h_fmv_aad := parseFlowMappingValue_aad h_ih_aad
                  ps_ek k (by omega) _ _ fmv_v ps_fmv heq_fmv
              have h_ag := AG.trans (AG.advance ps)
                (AG.trans (parseExplicitKey_ag h_ih_ag _ k (by omega) ek_v ps_ek heq_ek)
                  (parseFlowMappingValue_ag h_ih_ag ps_ek k (by omega) _ _ fmv_v ps_fmv heq_fmv))
              have h_fmv_ag := parseFlowMappingValue_ag h_ih_ag ps_ek k (by omega) _ _ fmv_v ps_fmv heq_fmv
              have ⟨h_pk, h_pv⟩ := pairs_push_aad h_ag h_pre_k h_pre_v
                (aad_mono h_fmv_ag h_ek_aad) h_fmv_aad
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
              have h_pn_aad := h_ih_aad _ k key_v ps_pn (by omega) heq_pn
              have h_fmv_aad := parseFlowMappingValue_aad h_ih_aad
                  ps_pn k (by omega) _ _ fmv_v ps_fmv heq_fmv
              have h_ag := AG.trans
                (h_ih_ag _ k key_v ps_pn (by omega) heq_pn)
                (parseFlowMappingValue_ag h_ih_ag ps_pn k (by omega) _ _ fmv_v ps_fmv heq_fmv)
              have h_fmv_ag := parseFlowMappingValue_ag h_ih_ag ps_pn k (by omega) _ _ fmv_v ps_fmv heq_fmv
              have ⟨h_pk, h_pv⟩ := pairs_push_aad h_ag h_pre_k h_pre_v
                (aad_mono h_fmv_ag h_pn_aad) h_fmv_aad
              exact ih_fuel ps_fmv _ (by omega) h_ok h_pk h_pv

-- Flow mapping wrapper AAD
lemma parseFlowMapping_aad (h_ih_aad : ParseNodeAAD input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseFlowMapping ps fuel = .ok (val, ps')) :
    AllAliasesDeclared val ps'.declaredAnchors := by
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
        have ⟨hk, hv⟩ := parseFlowMappingLoop_aad h_ih_aad h_ih_ag
          ps.advance k #[] (by omega) pairs_r ps_r heq_loop
          (fun ⟨i, hi⟩ => absurd hi (Nat.not_lt_zero _))
          (fun ⟨i, hi⟩ => absurd hi (Nat.not_lt_zero _))
        exact .mapping _ _ _ _ _
          (fun i => aad_mono (AG.advance ps_r) (hk i))
          (fun i => aad_mono (AG.advance ps_r) (hv i))
      · simp at h_ok

/-! ### parseNodeContent and parseNode AAD -/

lemma parseNodeContent_aad (h_ih_aad : ParseNodeAAD input n) (h_ih_ag : ParseNodeAG input n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n + 1) (props : NodeProperties)
    (isSeqEntry : Bool) (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseNodeContent ps fuel props isSeqEntry = .ok (val, ps')) :
    AllAliasesDeclared val ps'.declaredAnchors := by
  unfold parseNodeContent at h_ok
  split at h_ok
  · -- scalar
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
    exact .scalar _ _
  · exact parseBlockSequence_aad h_ih_aad h_ih_ag ps fuel (by omega) val ps' h_ok
  · exact parseBlockMapping_aad h_ih_aad h_ih_ag ps fuel (by omega) val ps' h_ok
  · -- blockEntry: empty scalar (seq-entry context, C2) or implicit block sequence
    split at h_ok
    · -- isSeqEntry: empty scalar (C2)
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
      exact .scalar _ _
    · -- otherwise: implicit block sequence
      exact parseImplicitBlockSequence_aad h_ih_aad h_ih_ag ps fuel (by omega) val ps' h_ok
  · exact parseFlowSequence_aad h_ih_aad h_ih_ag ps fuel (by omega) val ps' h_ok
  · exact parseFlowMapping_aad h_ih_aad h_ih_ag ps fuel (by omega) val ps' h_ok
  · -- empty scalar
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
    exact .scalar _ _

-- Main AAD theorem by strong induction
set_option maxHeartbeats 400000 in
lemma parseNode_aad_all : ∀ n, ParseNodeAAD input n := by
  intro n
  induction n with
  | zero =>
    intro ps m val ps' h_m h_ok
    have : m = 0 := by omega
    subst this
    simp [parseNode] at h_ok
  | succ n ih_aad =>
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
        -- Split on !ps.declaredAnchors.any (alias undefined check)
        split at h_ok <;> first | contradiction | skip
        -- trackPositions branch
        split at h_ok <;> (
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
          -- §7.1's guard IS this predicate's leaf: the name is a member of
          -- the declaration set, and an alias node declares nothing.
          refine AllAliasesDeclared.alias _ _ (mem_of_any_beq ?_)
          rename_i _ h_any _
          show ps.declaredAnchors.any _ = true
          simpa [DeclaredIndex.contains_eq_any] using h_any)
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
            exact applyNodeFinalization_aad val_c ps_c props _
              (parseNodeContent_aad ih_aad h_ih_ag ps_props k (by omega) props _ val_c ps_c heq_content)

-- Extraction
lemma parseNode_aliases_declared'
    (ps : ParseStateIx input) (fuel : Nat) (val : YamlValue) (ps' : ParseStateIx input)
    (h : parseNode ps fuel = .ok (val, ps')) :
    AllAliasesDeclared val ps'.declaredAnchors :=
  parseNode_aad_all fuel ps fuel val ps' Nat.le.refl h

end L4YAML.Proofs.Indexed.NodeProofs

end Blanket
