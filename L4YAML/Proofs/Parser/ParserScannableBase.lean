module

public import L4YAML.Proofs.Parser.ParserGrammableBase

@[expose] public section Blanket

/-!
# The `Scannable`-valued compose chain

`ParserGrammableBase`'s `compose_grammable` concludes
`Grammable doc.compose.value false`, and `Grammable` has no alias constructor —
§3.2.2: the representation graph carries no aliases.  One shape escapes that.
A node that has itself as a descendant via an alias (§3.2.1.3) leaves a
`.alias` in the composed value which no finite substitution removes, because
`YamlValue` expresses sharing by substitution and nothing else: a collection's
anchor binds only after its items are resolved, so its own interior alias never
sees it.

For that shape the chain here ends in `Scannable`, which is `Grammable` plus the
`| alias` constructor, and `ParserSoundness.scannableValue_has_witness` carries
it the rest of the way to a `ValidNode` witness — the conclusion the capstone
`parseStream_respects_grammar_unconditional` actually states.

Every declaration below mirrors its `Grammable` original with the predicate
renamed.  Two carry new content, both one line: `stripAnchors` and
`adaptForFlowContext` each leave `.alias` untouched (`| .alias _ => v`), so each
alias case is `Scannable.alias`.  The third is `compose_value_scannable_ordered`'s
alias case, which reaches a branch its `Grammable` original cannot: resolution
finds no preceding definition and returns the alias unchanged.  No anchor-table
hypothesis appears anywhere here, because `resolveAliasesOrdered` reads only the
ordered environment.

This is a separate module rather than a section of `ParserGrammableBase` because
`compose_value_scannable_ordered` and `compose_value_grammable_ordered` are both
`maxHeartbeats 4000000` inductions over `YamlValue`, and elaborating the two in
one module reached 137 GB resident without finishing.
-/

namespace L4YAML.Proofs.ParserGrammable

open L4YAML
open L4YAML.Grammar
open L4YAML.TokenParser

/-! ## The `Scannable`-valued mirror of the compose chain

`compose_grammable` above concludes `Grammable doc.compose.value false`, and
`Grammable` has no alias constructor (§3.2.2: the representation graph carries
no aliases).  A node that has itself as a descendant via an alias — §3.2.1.3 —
leaves a `.alias` in the composed value that no finite substitution removes,
because `YamlValue` expresses sharing by substitution and nothing else.  For
that one shape the chain below ends in `Scannable`, which is `Grammable` plus
the `| alias` constructor, and the witness route `scannableValue_has_witness`
(`ParserSoundness.lean`) carries it the rest of the way to `ValidNode`.

Each declaration mirrors its `Grammable` original with the predicate renamed.
Two carry new content, both one line: `stripAnchors` and `adaptForFlowContext`
each leave `.alias` untouched, so each alias case is `Scannable.alias`.  The
third piece of new content is in `compose_value_scannable_ordered`'s alias
case, which drops the `AllAliasesResolve` hypothesis entirely and therefore
reaches a branch the `Grammable` version could not: the parse-time table misses
and `resolveAliasesOrdered` returns the alias itself.
-/

set_option maxHeartbeats 2400000 in
/-- `stripAnchors` preserves `Scannable` for any value.

The proof is by induction on the `Scannable` derivation. The scalar
case uses metadata independence. The sequence/mapping cases use the
`stripList_eq_map`/`stripPairs_eq_map` lemmas to reduce where-clause
mutual recursion to `List.map`, then apply the IH element-wise. -/
lemma stripAnchors_preserves_Scannable (v : YamlValue) (inFlow : Bool) :
    Scannable v inFlow → Scannable v.stripAnchors inFlow := by
  intro h
  induction h with
  | scalar s inFlow h_ss =>
    exact .scalar { s with anchor := none } inFlow
      (fun hplain hlen => h_ss hplain hlen)
  | alias name inFlow =>
    -- `stripAnchors` leaves `.alias` untouched (`| .alias _ => v`).
    exact Scannable.alias name inFlow
  | sequence style items tag anchor inFlow h_items ih_items =>
    show Scannable (.sequence style (YamlValue.stripAnchors.stripList items.toList).toArray tag none) inFlow
    rw [stripList_eq_map]
    apply Scannable.sequence
    intro ⟨i, hi⟩
    simp at hi ⊢
    exact ih_items ⟨i, hi⟩
  | mapping style pairs tag anchor inFlow hk hv ih_k ih_v =>
    show Scannable (.mapping style (YamlValue.stripAnchors.stripPairs pairs.toList).toArray tag none) inFlow
    rw [stripPairs_eq_map]
    apply Scannable.mapping
    · intro ⟨i, hi⟩
      simp at hi ⊢
      exact ih_k ⟨i, hi⟩
    · intro ⟨i, hi⟩
      simp at hi ⊢
      exact ih_v ⟨i, hi⟩

set_option maxHeartbeats 800000 in
lemma adaptForFlowContext_scannable_forall (v : YamlValue) (b : Bool)
    (h : Scannable v b) : ∀ inFlow, Scannable v.adaptForFlowContext inFlow := by
  induction h with
  | alias name inFlow =>
    -- `adaptForFlowContext` leaves `.alias` untouched (`| .alias _ => v`).
    intro _; exact Scannable.alias name _
  | scalar s b h_ss =>
    intro inFlow
    show Scannable (if s.style == .plain && hasFlowIndicator s.content.toList
      then .scalar { s with style := .doubleQuoted } else .scalar s) inFlow
    split
    · -- s.style == .plain && hasFlowIndicator → doubleQuoted (vacuously scannable)
      exact .scalar { s with style := .doubleQuoted } inFlow
        (fun h_plain => by dsimp only [] at h_plain; contradiction)
    · -- else: s unchanged
      rename_i h_neg
      simp only [Bool.and_eq_true] at h_neg
      by_cases hplain : s.style = .plain
      · -- plain but no flow indicators
        have h_no_fi : hasFlowIndicator s.content.toList = false := by
          cases h_fi : hasFlowIndicator s.content.toList with
          | false => rfl
          | true =>
            have h_beq : (s.style == ScalarStyle.plain) = true := by rw [hplain]; decide
            exact absurd ⟨h_beq, h_fi⟩ h_neg
        have h_nfi := hasFlowIndicator_false_noFlowIndicators s.content h_no_fi
        have h_false := L4YAML.Proofs.ScannerPlainScalarValid.ScalarScannable_any_implies_false s b h_ss
        cases inFlow with
        | false => exact .scalar s false h_false
        | true =>
          exact .scalar s true (ScalarScannable_false_to_true_noFI s h_false h_nfi)
      · -- non-plain: vacuously scannable
        exact .scalar s inFlow (fun h_eq => absurd h_eq hplain)
  | sequence style items tag anchor b h_items ih_items =>
    intro inFlow
    show Scannable (.sequence style
      (YamlValue.adaptForFlowContext.adaptList items.toList).toArray tag anchor) inFlow
    rw [adaptList_eq_map]
    apply Scannable.sequence
    intro ⟨i, hi⟩
    simp at hi ⊢
    exact ih_items ⟨i, hi⟩ _
  | mapping style pairs tag anchor b hk hv ih_k ih_v =>
    intro inFlow
    show Scannable (.mapping style
      (YamlValue.adaptForFlowContext.adaptPairs pairs.toList).toArray tag anchor) inFlow
    rw [adaptPairs_eq_map]
    apply Scannable.mapping
    · intro ⟨i, hi⟩
      simp at hi ⊢
      exact ih_k ⟨i, hi⟩ _
    · intro ⟨i, hi⟩
      simp at hi ⊢
      exact ih_v ⟨i, hi⟩ _

/-- Environment bindings are well-formed: after stripping, bound values are
    `Scannable` at every flow context.  This is the only well-formedness
    hypothesis the chain needs: `resolveAliasesOrdered` reads the threaded
    environment and nothing else, so there is no anchor-table counterpart. -/
def WellFormedEnvS (env : List (String × YamlValue)) : Prop :=
  ∀ (name : String) (val : YamlValue),
    env.findSome? (fun (n, v) => if n == name then some v else none) = some val →
      ∀ inFlow, Scannable val.stripAnchors inFlow

/-- The empty environment is well-formed. -/
lemma wellFormedEnvS_nil : WellFormedEnvS [] := fun _ _ h => nomatch h

/-- Extending a well-formed environment with a binding whose value is
    universally grammable after stripping preserves well-formedness. -/
lemma WellFormedEnvS.cons {env : List (String × YamlValue)}
    (h_env : WellFormedEnvS env) (a : String) (val : YamlValue)
    (h_val : ∀ inFlow, Scannable val.stripAnchors inFlow) :
    WellFormedEnvS ((a, val) :: env) := by
  intro name w h_find inFlow
  simp only [List.findSome?_cons] at h_find
  cases hcond : (a == name) with
  | true =>
    simp only [hcond] at h_find
    cases h_find
    exact h_val inFlow
  | false =>
    simp only [hcond] at h_find
    exact h_env name w h_find inFlow

/-- Joint contract for `goList`: threading over a list whose every element
    satisfies the element-level (grammable ∧ well-formed-env) contract keeps
    every resolved element grammable after stripping and the final
    environment well-formed. -/
lemma goList_scannable_ordered
    (anchors : Array (String × YamlValue)) (ctx : Bool)
    (l : List YamlValue)
    (H : ∀ v ∈ l, ∀ env, WellFormedEnvS env →
      Scannable ((v.resolveAliasesOrdered anchors env).fst).stripAnchors ctx ∧
      WellFormedEnvS (v.resolveAliasesOrdered anchors env).snd) :
    ∀ env, WellFormedEnvS env →
      (∀ w ∈ (YamlValue.resolveAliasesOrdered.goList anchors l env).fst,
        Scannable w.stripAnchors ctx) ∧
      WellFormedEnvS (YamlValue.resolveAliasesOrdered.goList anchors l env).snd := by
  induction l with
  | nil =>
    intro env h_env
    simp only [YamlValue.resolveAliasesOrdered.goList]
    exact ⟨(fun w hw => nomatch hw), h_env⟩
  | cons v vs ih =>
    intro env h_env
    have hv := H v List.mem_cons_self env h_env
    have hrest := ih (fun w hw => H w (List.mem_cons_of_mem _ hw))
      ((v.resolveAliasesOrdered anchors env).snd) hv.2
    simp only [YamlValue.resolveAliasesOrdered.goList]
    refine ⟨fun w hw => ?_, hrest.2⟩
    rcases List.mem_cons.mp hw with h_eq | h_mem
    · exact h_eq ▸ hv.1
    · exact hrest.1 w h_mem

/-- Joint contract for `goPairs`: the key/value analog of
    `goList_scannable_ordered` (key resolved before value before the rest,
    each step re-arming the environment invariant). -/
lemma goPairs_scannable_ordered
    (anchors : Array (String × YamlValue)) (ctx : Bool)
    (l : List (YamlValue × YamlValue))
    (Hk : ∀ p ∈ l, ∀ env, WellFormedEnvS env →
      Scannable ((p.1.resolveAliasesOrdered anchors env).fst).stripAnchors ctx ∧
      WellFormedEnvS (p.1.resolveAliasesOrdered anchors env).snd)
    (Hv : ∀ p ∈ l, ∀ env, WellFormedEnvS env →
      Scannable ((p.2.resolveAliasesOrdered anchors env).fst).stripAnchors ctx ∧
      WellFormedEnvS (p.2.resolveAliasesOrdered anchors env).snd) :
    ∀ env, WellFormedEnvS env →
      (∀ q ∈ (YamlValue.resolveAliasesOrdered.goPairs anchors l env).fst,
        Scannable q.1.stripAnchors ctx ∧ Scannable q.2.stripAnchors ctx) ∧
      WellFormedEnvS (YamlValue.resolveAliasesOrdered.goPairs anchors l env).snd := by
  induction l with
  | nil =>
    intro env h_env
    simp only [YamlValue.resolveAliasesOrdered.goPairs]
    exact ⟨(fun q hq => nomatch hq), h_env⟩
  | cons p rest ih =>
    intro env h_env
    obtain ⟨k, v⟩ := p
    have hk := Hk (k, v) List.mem_cons_self env h_env
    have hv := Hv (k, v) List.mem_cons_self
      ((k.resolveAliasesOrdered anchors env).snd) hk.2
    have hrest := ih (fun q hq => Hk q (List.mem_cons_of_mem _ hq))
      (fun q hq => Hv q (List.mem_cons_of_mem _ hq))
      ((v.resolveAliasesOrdered anchors (k.resolveAliasesOrdered anchors env).snd).snd) hv.2
    simp only [YamlValue.resolveAliasesOrdered.goPairs]
    refine ⟨fun q hq => ?_, hrest.2⟩
    rcases List.mem_cons.mp hq with h_eq | h_mem
    · exact h_eq ▸ ⟨hk.1, hv.1⟩
    · exact hrest.1 q h_mem

set_option maxHeartbeats 4000000 in
/-- C1 for the order-aware resolver: composing a `Scannable` value with
    `resolveAliasesOrdered` produces a `Scannable` value, provided all aliases
    resolve in the fallback table, the table is well-formed, and the threaded
    environment is well-formed.

    The conclusion is a JOINT (grammable ∧ well-formed-env), generalized over
    the environment: the walk binds each anchored node *after* its content
    (cleaned `stripAnchors ∘ adaptForFlowContext`, exactly like
    `ParseState.addAnchor`), and the binding edge is discharged by the case's
    own grammability conjunct lifted by `adaptForFlowContext_scannable_forall`. -/
lemma compose_value_scannable_ordered
    (v : YamlValue) (anchors : Array (String × YamlValue)) (inFlow : Bool)
    (h_scan : Scannable v inFlow) :
    ∀ env, WellFormedEnvS env →
      Scannable ((v.resolveAliasesOrdered anchors env).fst).stripAnchors inFlow ∧
      WellFormedEnvS (v.resolveAliasesOrdered anchors env).snd := by
  induction h_scan with
  | scalar s inFlow h_ss =>
    intro env h_env
    constructor
    · -- fst = .scalar s regardless of the binding made
      exact Scannable.scalar { s with anchor := none } inFlow
        ((ScalarScannable_strip_anchor s inFlow).mp h_ss)
    · cases h_anchor : s.anchor with
      | none =>
        have h2 : ((YamlValue.scalar s).resolveAliasesOrdered anchors env).snd = env := by
          simp only [YamlValue.resolveAliasesOrdered, h_anchor]
        rw [h2]; exact h_env
      | some a =>
        have h2 : ((YamlValue.scalar s).resolveAliasesOrdered anchors env).snd =
            (a, (YamlValue.scalar { s with anchor := none }).adaptForFlowContext) :: env := by
          simp only [YamlValue.resolveAliasesOrdered, h_anchor]
        rw [h2]
        refine WellFormedEnvS.cons h_env a _ (fun ctx => ?_)
        rw [show (YamlValue.scalar { s with anchor := none })
              = (YamlValue.scalar s).stripAnchors from rfl,
            adaptForFlowContext_stripAnchors, stripAnchors_stripAnchors]
        exact adaptForFlowContext_scannable_forall _ inFlow
          (Scannable.scalar { s with anchor := none } inFlow
            ((ScalarScannable_strip_anchor s inFlow).mp h_ss)) ctx
  | alias name inFlow =>
    intro env h_env
    cases h_lookup : env.findSome? (fun (n, val) => if n == name then some val else none) with
    | some val =>
      have h1 : (YamlValue.alias name).resolveAliasesOrdered anchors env = (val, env) := by
        simp only [YamlValue.resolveAliasesOrdered, h_lookup]
      rw [h1]
      exact ⟨h_env name val h_lookup inFlow, h_env⟩
    | none =>
      -- §3.2.2.2 resolves an alias against the most recent preceding event and
      -- nothing else, so one with no preceding definition comes back unchanged
      -- (`| none => (v, env)`) and `Scannable.alias` discharges it.  This is
      -- the branch `Grammable` cannot reach, having no alias constructor.
      have h1 : (YamlValue.alias name).resolveAliasesOrdered anchors env
          = (YamlValue.alias name, env) := by
        simp only [YamlValue.resolveAliasesOrdered, h_lookup]
      rw [h1]
      exact ⟨Scannable.alias name inFlow, h_env⟩
  | sequence style items tag anchor inFlow h_items ih_items =>
    intro env h_env
    have H : ∀ w ∈ items.toList, ∀ env', WellFormedEnvS env' →
        Scannable ((w.resolveAliasesOrdered anchors env').fst).stripAnchors
          (inFlow || style == .flow) ∧
        WellFormedEnvS (w.resolveAliasesOrdered anchors env').snd := by
      intro w hw
      obtain ⟨i, hi, h_eq⟩ := List.getElem_of_mem hw
      have hi' : i < items.size := by rwa [Array.length_toList] at hi
      have h_w : w = items[i] := by rw [← h_eq, Array.getElem_toList]
      subst h_w
      exact ih_items ⟨i, hi'⟩
    have h_fold := goList_scannable_ordered anchors (inFlow || style == .flow)
      items.toList H env h_env
    have h1 : ((YamlValue.sequence style items tag anchor).resolveAliasesOrdered anchors env).fst
        = .sequence style
            (YamlValue.resolveAliasesOrdered.goList anchors items.toList env).fst.toArray
            tag anchor := by
      simp only [YamlValue.resolveAliasesOrdered]
    have h_scan_v' : Scannable (YamlValue.sequence style
        (YamlValue.resolveAliasesOrdered.goList anchors items.toList env).fst.toArray
        tag anchor).stripAnchors inFlow := by
      show Scannable (.sequence style
        (YamlValue.stripAnchors.stripList
          ((YamlValue.resolveAliasesOrdered.goList anchors items.toList env).fst.toArray).toList).toArray
        tag none) inFlow
      rw [List.toList_toArray, stripList_eq_map]
      apply Scannable.sequence
      intro ⟨i, hi⟩
      simp at hi ⊢
      exact h_fold.1 _ (List.getElem_mem _)
    constructor
    · rw [h1]; exact h_scan_v'
    · cases h_anchor : anchor with
      | none =>
        have h2 : ((YamlValue.sequence style items tag none).resolveAliasesOrdered anchors env).snd
            = (YamlValue.resolveAliasesOrdered.goList anchors items.toList env).snd := by
          simp only [YamlValue.resolveAliasesOrdered]
        rw [h2]; exact h_fold.2
      | some a =>
        have h2 : ((YamlValue.sequence style items tag (some a)).resolveAliasesOrdered anchors env).snd
            = (a, (YamlValue.sequence style
                (YamlValue.resolveAliasesOrdered.goList anchors items.toList env).fst.toArray
                tag (some a)).stripAnchors.adaptForFlowContext)
              :: (YamlValue.resolveAliasesOrdered.goList anchors items.toList env).snd := by
          simp only [YamlValue.resolveAliasesOrdered]
        rw [h2]
        refine WellFormedEnvS.cons h_fold.2 a _ (fun ctx => ?_)
        rw [adaptForFlowContext_stripAnchors, stripAnchors_stripAnchors]
        exact adaptForFlowContext_scannable_forall _ inFlow h_scan_v' ctx
  | mapping style pairs tag anchor inFlow hk hv ih_k ih_v =>
    intro env h_env
    have Hk : ∀ p ∈ pairs.toList, ∀ env', WellFormedEnvS env' →
        Scannable ((p.1.resolveAliasesOrdered anchors env').fst).stripAnchors
          (inFlow || style == .flow) ∧
        WellFormedEnvS (p.1.resolveAliasesOrdered anchors env').snd := by
      intro p hp
      obtain ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp
      have hi' : i < pairs.size := by rwa [Array.length_toList] at hi
      have h_p : p = pairs[i] := by rw [← h_eq, Array.getElem_toList]
      subst h_p
      exact ih_k ⟨i, hi'⟩
    have Hv : ∀ p ∈ pairs.toList, ∀ env', WellFormedEnvS env' →
        Scannable ((p.2.resolveAliasesOrdered anchors env').fst).stripAnchors
          (inFlow || style == .flow) ∧
        WellFormedEnvS (p.2.resolveAliasesOrdered anchors env').snd := by
      intro p hp
      obtain ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp
      have hi' : i < pairs.size := by rwa [Array.length_toList] at hi
      have h_p : p = pairs[i] := by rw [← h_eq, Array.getElem_toList]
      subst h_p
      exact ih_v ⟨i, hi'⟩
    have h_fold := goPairs_scannable_ordered anchors (inFlow || style == .flow)
      pairs.toList Hk Hv env h_env
    have h1 : ((YamlValue.mapping style pairs tag anchor).resolveAliasesOrdered anchors env).fst
        = .mapping style
            (YamlValue.resolveAliasesOrdered.goPairs anchors pairs.toList env).fst.toArray
            tag anchor := by
      simp only [YamlValue.resolveAliasesOrdered]
    have h_scan_v' : Scannable (YamlValue.mapping style
        (YamlValue.resolveAliasesOrdered.goPairs anchors pairs.toList env).fst.toArray
        tag anchor).stripAnchors inFlow := by
      show Scannable (.mapping style
        (YamlValue.stripAnchors.stripPairs
          ((YamlValue.resolveAliasesOrdered.goPairs anchors pairs.toList env).fst.toArray).toList).toArray
        tag none) inFlow
      rw [List.toList_toArray, stripPairs_eq_map]
      apply Scannable.mapping
      · intro ⟨i, hi⟩
        simp at hi ⊢
        exact (h_fold.1 _ (List.getElem_mem _)).1
      · intro ⟨i, hi⟩
        simp at hi ⊢
        exact (h_fold.1 _ (List.getElem_mem _)).2
    constructor
    · rw [h1]; exact h_scan_v'
    · cases h_anchor : anchor with
      | none =>
        have h2 : ((YamlValue.mapping style pairs tag none).resolveAliasesOrdered anchors env).snd
            = (YamlValue.resolveAliasesOrdered.goPairs anchors pairs.toList env).snd := by
          simp only [YamlValue.resolveAliasesOrdered]
        rw [h2]; exact h_fold.2
      | some a =>
        have h2 : ((YamlValue.mapping style pairs tag (some a)).resolveAliasesOrdered anchors env).snd
            = (a, (YamlValue.mapping style
                (YamlValue.resolveAliasesOrdered.goPairs anchors pairs.toList env).fst.toArray
                tag (some a)).stripAnchors.adaptForFlowContext)
              :: (YamlValue.resolveAliasesOrdered.goPairs anchors pairs.toList env).snd := by
          simp only [YamlValue.resolveAliasesOrdered]
        rw [h2]
        refine WellFormedEnvS.cons h_fold.2 a _ (fun ctx => ?_)
        rw [adaptForFlowContext_stripAnchors, stripAnchors_stripAnchors]
        exact adaptForFlowContext_scannable_forall _ inFlow h_scan_v' ctx

/-- C1 applied to `YamlDocument.compose` (order-aware resolution): the walk
    starts from the empty (trivially well-formed) environment. -/
lemma compose_scannable (doc : YamlDocument)
    (h_scan : Scannable doc.value false) :
    Scannable doc.compose.value false := by
  simp only [YamlDocument.compose]
  exact (compose_value_scannable_ordered doc.value doc.anchors false h_scan
    [] wellFormedEnvS_nil).1

end L4YAML.Proofs.ParserGrammable

end Blanket
