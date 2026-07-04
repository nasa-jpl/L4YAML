import L4YAML.Proofs.Output.EmitterScannability

/-!
# Reflection — the R447 provider's gate is close-UNGATED and its statement REFUTABLE

`seqBody_recseqbody_provider` (`SeqInteriorSeparators.lean`, the lone R447 sorry) is stated with the
gate `FlowBodyWindow ∧ FlowBodyContentDeepSeq ∧ SeqEnclosed ∧ 2 ≤ lo ∧ hi ≤ size-2` — WITHOUT the
close-token fact `tokens[hi]!.val = .flowSequenceEnd` that its sole consumer (`seqRoot_carrier_r447`'s
`recIH`) holds in scope and DROPS at the call site.

That ungated statement is **FALSE**.  On the real emission `["a","b"]` the window `[2, 4)` — the
first scalar entry PLUS the depth-`0` `.flowEntry` separator, ending just BEFORE the second entry —
satisfies every stated hypothesis:

* `FlowBodyWindow tokens 2 4` — the slice `["a", ,]` is balanced (both deltas `0`), Dyck, well-typed,
  and in bounds (`4 ≤ 7 - 2`);
* `FlowBodyContentDeepSeq tokens 2 4` — the head is a scalar (content-start) and the opener/separator
  fields are vacuous (`k + 1 < 4` leaves only `k = 2`, a scalar);
* `SeqEnclosed tokens 2` — the btFold top after `streamStart · [` is `true`;

yet the conclusion `RecSeqBody [.scalar "a" _, .flowEntry]` is structurally UNINHABITABLE: a body
never ends on a separator (`.single`'s entry has no 2-token scalar-headed shape; `.cons` demands a
non-empty body AFTER the separator, forcing length ≥ 3).

This is [[inhabitation-debt-validate-target-defs]] Rule 2 applied at the SORRY-STATEMENT level:
probing the target BEFORE the multi-session navigator build catches that the navigator would have
been aimed at an unprovable goal.  The fix (landed with this probe) adds the missing close-gate
conjunct `tokens[hi]!.val = .flowSequenceEnd` to the provider's signature; the consumer supplies it
verbatim (`_h_close`, previously discarded).  With the close-gate, the counterexample window is
excluded (`tokens[4]!.val` is the second scalar, not `.flowSequenceEnd`), and every gated window is
a genuine suffix-of-interior body window (`hi` is forced to the matching close of `lo`'s nearest
enclosing opener by the window's own Dyck floor), which the stored root `RecSeqBody` navigator can
serve.
-/

namespace ProviderCloseGate

open L4YAML
open L4YAML.Emit
open L4YAML.Grammar
open L4YAML.Scanner
open L4YAML.Proofs.ParserGrammable
open L4YAML.Proofs.EmitterScannability

/-- Two plain scalars — the smallest emission whose body has a depth-`0` separator. -/
def items2 : Array YamlValue :=
  #[.scalar { content := "a", style := .plain }, .scalar { content := "b", style := .plain }]

/-- A `RecSeqBody` never consists of exactly a scalar followed by a `.flowEntry`: `.single`'s entry
    cannot be that 2-token list (no `RecSeqEntry` constructor produces a scalar-headed 2-token
    window), and `.cons` forces a non-empty body after the separator (length ≥ 3). -/
theorem recseqbody_scalar_fe_false (l : List (Positioned YamlToken))
    (h : RecSeqBody l) (c : String) (s : ScalarStyle)
    (hval : l.map (·.val) = [.scalar c s, .flowEntry]) : False := by
  cases h with
  | single e h_ne h_e h_head =>
    cases h_e with
    | scalar t c' s' ht =>
      -- length 1 ≠ 2
      simp at hval
    | seqEmpty op cl h_op h_cl =>
      -- head would be `[`, but `hval` pins it a scalar
      simp at hval
      rw [h_op] at hval
      exact absurd hval.1 (by simp)
    | seq op cl interior h_op h_cl h_wb h_rec =>
      simp at hval
      rw [h_op] at hval
      exact absurd hval.1 (by simp)
    | map op cl interior h_op h_cl h_wb =>
      simp at hval
      rw [h_op] at hval
      exact absurd hval.1 (by simp)
    | mapRec op cl interior h_op h_cl h_wb h_rec =>
      simp at hval
      rw [h_op] at hval
      exact absurd hval.1 (by simp)
  | cons e fe rest h_ne h_e h_head h_fe h_rest =>
    -- `|e| ≥ 1` and `|rest| ≥ 1` force `|l| ≥ 3`, but `hval` pins `|l| = 2`.
    have h_len := congrArg List.length hval
    simp [List.length_append] at h_len
    have h_e_pos : 0 < e.length := List.length_pos_iff.mpr h_ne
    have h_rest_pos : 0 < rest.length := by
      cases h_rest with
      | single e' h_ne' _ _ => exact List.length_pos_iff.mpr h_ne'
      | cons e' fe' rest' h_ne' _ _ _ _ =>
        have := List.length_pos_iff.mpr h_ne'
        simp [List.length_append]
        omega
    omega

/-- **The ungated provider statement is refuted** — the exact ∀-shape of the pre-fix
    `seqBody_recseqbody_provider` (no close-gate) is FALSE on real emission. -/
theorem provider_ungated_refuted :
    ¬ (∀ (items : Array YamlValue) (tokens : Array (Positioned YamlToken)),
        Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens →
        items.toList ≠ [] →
        (∀ v ∈ items.toList, EmitScansInFlowRecEntry v) →
        ∀ lo hi, FlowBodyWindow tokens lo hi → FlowBodyContentDeepSeq tokens lo hi →
            SeqEnclosed tokens lo → 2 ≤ lo → hi ≤ tokens.size - 2 →
            RecSeqBody ((tokens.toList.take hi).drop lo)) := by
  intro H
  -- Ground the emission: the scan succeeds; name its token array.
  match hscan : Scanner.scanFiltered ("[" ++ emit.emitList items2.toList ++ "]") with
  | .error e =>
    have h_ok : (Scanner.scanFiltered ("[" ++ emit.emitList items2.toList ++ "]")).toOption.isSome
        = true := by native_decide
    rw [hscan] at h_ok
    simp [Except.toOption] at h_ok
  | .ok tokens =>
    have key : ∀ {α : Type} (g : Array (Positioned YamlToken) → α) (a : α),
        (Scanner.scanFiltered ("[" ++ emit.emitList items2.toList ++ "]")).toOption.map g
            = some a →
        g tokens = a := by
      intro α g a e; rw [hscan] at e; exact Option.some.inj e
    have hsz : tokens.size = 7 := key (fun t => t.size) 7 (by native_decide)
    have h2 : tokens[2]!.val = .scalar "a" .doubleQuoted :=
      key (fun t => t[2]!.val) _ (by native_decide)
    -- FlowBodyWindow tokens 2 4
    have h_bal : flowBracketBalance tokens 2 4 = 0 :=
      key (fun t => flowBracketBalance t 2 4) 0 (by native_decide)
    have h_bal3 : flowBracketBalance tokens 2 3 = 0 :=
      key (fun t => flowBracketBalance t 2 3) 0 (by native_decide)
    have h_bal2 : flowBracketBalance tokens 2 2 = 0 :=
      key (fun t => flowBracketBalance t 2 2) 0 (by native_decide)
    have h_wt : btFold (some []) ((tokens.toList.take 4).drop 2) = some [] :=
      key (fun t => btFold (some []) ((t.toList.take 4).drop 2)) (some []) (by native_decide)
    have h_win : FlowBodyWindow tokens 2 4 := by
      refine ⟨Nat.le_refl 2, by omega, by omega, by omega, h_bal, ?_, h_wt⟩
      intro i hi1 hi2
      rcases (show i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl
      · rw [h_bal2]; decide
      · rw [h_bal3]; decide
      · rw [h_bal]; decide
    -- FlowBodyContentDeepSeq tokens 2 4 (head scalar; other fields vacuous at k = 2)
    have h_deep : FlowBodyContentDeepSeq tokens 2 4 := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h2]; exact Or.inl ⟨"a", .doubleQuoted, rfl⟩
      · intro k hk1 hk2 hopen _hne
        have hk : k = 2 := by omega
        subst hk
        rw [h2] at hopen
        cases hopen
      · intro k hk1 hk2 hfe _hne
        have hk : k = 2 := by omega
        subst hk
        rw [h2] at hfe
        cases hfe
    -- SeqEnclosed tokens 2
    have h_enc : SeqEnclosed tokens 2 := by
      show (btFold (some []) (tokens.toList.take 2)).bind (·.head?) = some true
      exact key (fun t => (btFold (some []) (t.toList.take 2)).bind (·.head?)) (some true)
        (by native_decide)
    -- The per-item recursive-emission hypothesis, from `Grammable` (plain scalars).
    have h_all : ∀ v ∈ items2.toList, EmitScansInFlowRecEntry v := by
      intro v hv
      have hg : Grammable v true := by
        simp [items2] at hv
        rcases hv with rfl | rfl <;>
        · refine .scalar _ true ?_
          unfold ScalarScannable
          intro _hplain _hlen
          exact ⟨by decide, by decide, by decide, fun _ => by decide⟩
      exact emit_scans_in_flow_rec_entry v hg
    -- Apply the ungated statement at the counterexample window and refute its conclusion.
    have h := H items2 tokens hscan (by simp [items2]) h_all 2 4 h_win h_deep h_enc
      (Nat.le_refl 2) (by omega)
    have hslice : ((tokens.toList.take 4).drop 2).map (·.val)
        = [.scalar "a" .doubleQuoted, .flowEntry] :=
      key (fun t => ((t.toList.take 4).drop 2).map (·.val)) _ (by native_decide)
    exact recseqbody_scalar_fe_false _ h "a" .doubleQuoted hslice

end ProviderCloseGate

/-! ## Axiom audit

`provider_ungated_refuted` runs the real scanner under `native_decide`, so its profile is
`[propext, Classical.choice, Quot.sound]` plus the per-decl reflected-decide axioms
(`._native.native_decide.ax_*`, including the environment's escape/roundtrip reflected leaves) --
audited at landing, NO `sorryAx`.  The pin below covers the structural inversion lemma, whose
profile is stable. -/

/-- info: 'ProviderCloseGate.recseqbody_scalar_fe_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProviderCloseGate.recseqbody_scalar_fe_false
