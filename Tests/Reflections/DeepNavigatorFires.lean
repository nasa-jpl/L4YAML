import L4YAML.Proofs.Output.EmitterScannability

/-!
# Reflection — the deep-family navigator FIRES on the map-nested window class

`seqBody_recseqbody_provider` (the R447 residual) is now CLOSED by the deep-family navigator
(`DeepNavigator.lean`): the stored severance-free root `RecSeqBodyDeep`
(`seqRoot_recseqbodyDeep`, off `emitList_scans_recseqbodyDeep`) is walked positionally by
`deep_navigate_core` down to any close-gated window.  This probe drives the closure through the
HARDEST window class — the map-nested seq `[b]` inside `[{a:[b]}]` — which the token-spine
navigator (`nestedSeq_recseqbody_of_locator`, gate `SeqPathAllSeq`) provably cannot reach
(`seqPathAllSeq_map_descend_excluded`), and which motivated the whole structural-navigator design.

Layout of `[{a:[b]}]` (12 tokens):
`ss · [ · { · key · "a" · value · [ · "b" · ] · } · ] · se` — positions `0..11`.

* the inner `[b]` interior is the window `[7, 8)` (close `]` at 8, two bracket levels deep, one
  through a `{` frame) — the SEQ half fires there;
* the `{a:[b]}` interior is the window `[3, 9)` (close `}` at 9, `.key` head) — the MAP half of
  `deep_navigate_core` fires there (the `h_map_rec` shape the `FlowSubrangesOk` chain consumes).
-/

namespace DeepNavigatorFires

open L4YAML
open L4YAML.Emit
open L4YAML.Grammar
open L4YAML.Scanner
open L4YAML.Proofs.ParserGrammable
open L4YAML.Proofs.EmitterScannability

/-- `{a:[b]}` — a flow mapping whose value is a nested flow seq. -/
def mn_map : YamlValue :=
  .mapping .flow
    #[(.scalar { content := "a", style := .plain },
       .sequence .flow #[.scalar { content := "b", style := .plain }] none none)]
    none none

def mn_items : Array YamlValue := #[mn_map]

/-- The item is grammable in flow context (plain one-char scalars pass `ScalarScannable`). -/
theorem mn_map_grammable : Grammable mn_map true := by
  refine .mapping .flow _ none none true (fun i => ?_) (fun i => ?_)
  · -- the key `"a"`
    match i with
    | ⟨0, _⟩ =>
      refine .scalar _ _ ?_
      unfold ScalarScannable
      intro _ _
      exact ⟨by decide, by decide, by decide, fun _ => by decide⟩
  · -- the value `["b"]`
    match i with
    | ⟨0, _⟩ =>
      refine .sequence .flow _ none none _ (fun j => ?_)
      match j with
      | ⟨0, _⟩ =>
        refine .scalar _ _ ?_
        unfold ScalarScannable
        intro _ _
        exact ⟨by decide, by decide, by decide, fun _ => by decide⟩

theorem mn_all_deep : ∀ v ∈ mn_items.toList, EmitScansInFlowRecEntryDeep v := by
  intro v hv
  have h_eq : v = mn_map := by simpa [mn_items] using hv
  rw [h_eq]
  exact emit_scans_in_flow_rec_entry_deep mn_map mn_map_grammable

/-- **The provider fires at the map-nested seq window `[7, 8)`** — the class-2 window
    `SeqPathAllSeq` cannot serve.  Every gate fact is discharged on the REAL scanned emission. -/
theorem provider_fires_map_nested :
    ∀ tokens, Scanner.scanFiltered ("[" ++ emit.emitList mn_items.toList ++ "]") = .ok tokens →
      RecSeqBody ((tokens.toList.take 8).drop 7) := by
  intro tokens hscan
  have key : ∀ {α : Type} (g : Array (Positioned YamlToken) → α) (a : α),
      (Scanner.scanFiltered ("[" ++ emit.emitList mn_items.toList ++ "]")).toOption.map g
          = some a →
      g tokens = a := by
    intro α g a e; rw [hscan] at e; exact Option.some.inj e
  have hsz : tokens.size = 12 := key (fun t => t.size) 12 (by native_decide)
  have h7 : tokens[7]!.val = .scalar "b" .doubleQuoted :=
    key (fun t => t[7]!.val) _ (by native_decide)
  have h8 : tokens[8]!.val = .flowSequenceEnd :=
    key (fun t => t[8]!.val) _ (by native_decide)
  have h_bal77 : flowBracketBalance tokens 7 7 = 0 :=
    key (fun t => flowBracketBalance t 7 7) 0 (by native_decide)
  have h_bal78 : flowBracketBalance tokens 7 8 = 0 :=
    key (fun t => flowBracketBalance t 7 8) 0 (by native_decide)
  have h_wt : btFold (some []) ((tokens.toList.take 8).drop 7) = some [] :=
    key (fun t => btFold (some []) ((t.toList.take 8).drop 7)) (some []) (by native_decide)
  have h_win : FlowBodyWindow tokens 7 8 := by
    refine ⟨by omega, by omega, by omega, by omega, h_bal78, ?_, h_wt⟩
    intro i hi1 hi2
    rcases (show i = 7 ∨ i = 8 by omega) with rfl | rfl
    · rw [h_bal77]; decide
    · rw [h_bal78]; decide
  have h_deep : FlowBodyContentDeepSeq tokens 7 8 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [h7]; exact Or.inl ⟨"b", .doubleQuoted, rfl⟩
    · intro k hk1 hk2 _ _; omega
    · intro k hk1 hk2 _ _; omega
  have h_enc : SeqEnclosed tokens 7 := by
    show (btFold (some []) (tokens.toList.take 7)).bind (·.head?) = some true
    exact key (fun t => (btFold (some []) (t.toList.take 7)).bind (·.head?)) (some true)
      (by native_decide)
  exact seqBody_recseqbody_provider mn_items tokens hscan (by simp [mn_items]) mn_all_deep
    7 8 h_win h_deep h_enc h8 (by omega) (by omega)

/-- **The navigator's MAP half fires at the `{a:[b]}` interior `[3, 9)`** — the per-window
    `RecMapBody` shape the `FlowSubrangesOk` chain's `h_map_rec` consumes, produced here from the
    SAME root walk (no map carrier anywhere). -/
theorem navigator_map_half_fires :
    ∀ tokens, Scanner.scanFiltered ("[" ++ emit.emitList mn_items.toList ++ "]") = .ok tokens →
      RecMapBody ((tokens.toList.take 9).drop 3) := by
  intro tokens hscan
  have key : ∀ {α : Type} (g : Array (Positioned YamlToken) → α) (a : α),
      (Scanner.scanFiltered ("[" ++ emit.emitList mn_items.toList ++ "]")).toOption.map g
          = some a →
      g tokens = a := by
    intro α g a e; rw [hscan] at e; exact Option.some.inj e
  have hsz : tokens.size = 12 := key (fun t => t.size) 12 (by native_decide)
  have h3 : tokens[3]!.val = .key := key (fun t => t[3]!.val) _ (by native_decide)
  have h9 : tokens[9]!.val = .flowMappingEnd := key (fun t => t[9]!.val) _ (by native_decide)
  have h10 : tokens[10]!.val = .flowSequenceEnd := key (fun t => t[10]!.val) _ (by native_decide)
  have h_bal : ∀ i, 3 ≤ i → i ≤ 9 → flowBracketBalance tokens 3 i ≥ 0 := by
    have b3 : flowBracketBalance tokens 3 3 = 0 :=
      key (fun t => flowBracketBalance t 3 3) 0 (by native_decide)
    have b4 : flowBracketBalance tokens 3 4 = 0 :=
      key (fun t => flowBracketBalance t 3 4) 0 (by native_decide)
    have b5 : flowBracketBalance tokens 3 5 = 0 :=
      key (fun t => flowBracketBalance t 3 5) 0 (by native_decide)
    have b6 : flowBracketBalance tokens 3 6 = 0 :=
      key (fun t => flowBracketBalance t 3 6) 0 (by native_decide)
    have b7 : flowBracketBalance tokens 3 7 = 1 :=
      key (fun t => flowBracketBalance t 3 7) 1 (by native_decide)
    have b8 : flowBracketBalance tokens 3 8 = 1 :=
      key (fun t => flowBracketBalance t 3 8) 1 (by native_decide)
    have b9 : flowBracketBalance tokens 3 9 = 0 :=
      key (fun t => flowBracketBalance t 3 9) 0 (by native_decide)
    intro i hi1 hi2
    rcases (show i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [b3]; decide
    · rw [b4]; decide
    · rw [b5]; decide
    · rw [b6]; decide
    · rw [b7]; decide
    · rw [b8]; decide
    · rw [b9]; decide
  have h_bal39 : flowBracketBalance tokens 3 9 = 0 :=
    key (fun t => flowBracketBalance t 3 9) 0 (by native_decide)
  have h_root := seqRoot_recseqbodyDeep mn_items tokens hscan (by simp [mn_items]) mn_all_deep
  have h_nav := (deep_navigate_core tokens ((tokens.size - 2) - 2) 2 (tokens.size - 2)
      (Nat.le_refl _) (by omega)).1 h_root (by rw [show tokens.size - 2 = 10 by omega]; exact h10)
  exact RecMapBodyDeep.toFlat ((h_nav 3 9 ⟨by omega, by omega, by omega, h_bal39, h_bal,
    Or.inr ⟨h9, Or.inl h3⟩⟩).2 h9)

end DeepNavigatorFires

/-! ## Axiom audit

Both firings run the real scanner under `native_decide` for the gate facts, so they add the
per-decl reflected-decide axioms; the load-bearing check is NO `sorryAx` — the provider is closed
by a real proof.  The stable pins live on the production side (`R447RootCarrier.lean`'s
`seqRoot_carrier_r447_type_ok` pin, now `sorryAx`-free). -/
