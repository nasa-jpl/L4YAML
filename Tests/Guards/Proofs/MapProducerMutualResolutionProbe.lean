import L4YAML.Spec.Grammar

/-!
# R451 de-risk probe — the producer citation cycle (#1 value ↔ #2 saved-key) that R450 surfaced is
# broken by a CONJUNCTION-MOTIVE single induction, NOT a `mutual theorem` block.

R450 found that supplying the additive `h_rec : RecMapBody interior` field forces the value producer #1
(`emit_scans_in_flow_rec_entry`) and the saved-key producer #2 (`emit_scans_in_flow_saved_key_rec_entry`)
to cite each other — a cycle Lean rejects outside a `mutual` block.  The R450 Blueprint Next step proposed
restructuring #1 and #2 into a `mutual theorem` block (structural recursion on `YamlValue`/`Grammable`),
which would drag in the Reflection-234 `mutual`-block gotchas (doc-comment-on-`mutual`, the `induction`
tactic inside a mutual theorem, `Or`-nesting).

**This probe finds a strictly simpler resolution and validates it on the REAL `Grammable`/`YamlValue`
recursor.**  #1 and #2 both recurse on the SAME inductive (`Grammable v inFlow`, structurally recursive on
`YamlValue` — its `sequence`/`mapping` constructors carry the sub-value `Grammable` proofs under
`∀ i : Fin _.size`).  When two mutually-citing producers recurse on the SAME data, you do NOT need a mutual
block of THEOREMS — you prove the CONJUNCTION of their deliverables by ONE `induction`, and the single
shared induction hypothesis carries BOTH deliverables at every sub-value, so each arm reads the component
it needs off the IH instead of citing the sibling theorem.  The mutual structure stays where it already is —
in the DATA (`RecSeqEntry` ↔ `RecMapBody`; here the mirror `EValue` ↔ `ESkey`) — and the PRODUCER collapses
to ONE ordinary theorem.

The probe is decisive because it runs over the ACTUAL `Grammable` recursor with the ACTUAL `∀ i : Fin _.size`
array nesting (the part the R450 toy demo — a binary tree — did NOT exercise), reproducing the exact
cross-citation pattern of #1/#2:

* `EValue` mirrors #1's deliverable; its `.mapping` arm needs the SAVED-KEY deliverable on the keys
  (`ihk i |>.2`) and the VALUE deliverable on the values (`ihv i |>.1`) — exactly why #1's map arm reaches
  the sibling #2 today.
* `ESkey` mirrors #2's deliverable; its `.sequence` arm needs the VALUE deliverable on the items
  (`ih i |>.1`) — exactly the existing #2 → #1 edge (`NonemptyStructure.lean:3233`).

`grammable_gives_both` proves `EValue v ∧ ESkey v` by ONE `induction hg`, supplying every cross-edge from the
conjunction IH.  It compiles ⇒ the real refactor needs NO `mutual theorem` block: replace #1 and #2 with one
`emit_scans_in_flow_rec_entry_both` delivering the conjunction, projecting `.1`/`.2` at the consumers, and
the map arm feeds the assembler #3 the saved-key keys from `(ihk i).2` and the value values from `(ihv i).1`.
-/

namespace L4YAML.Proofs.EmitterScannability.MapProducerMutualResolutionProbe

open L4YAML L4YAML.Grammar

/- A lightweight mirror of the two recursive deliverables, as a MUTUAL INDUCTIVE on `YamlValue` — the
   data-level mutual reference (`EValue` ↔ `ESkey`) that already exists in the real types
   (`RecSeqEntry` ↔ `RecMapBody`).  The cross-edges are encoded in the constructors:

   * `EValue.mapping` / `ESkey.mapping` take `ESkey` on the keys and `EValue` on the values;
   * `ESkey.sequence` takes `EValue` on the items (the #2 → #1 edge).

   NOTE the plain `/- -/`, not a doc comment `/-- -/`: a doc comment cannot attach to the `mutual`
   keyword (the Reflection-234 attachment gotcha — and the first thing this probe got wrong).  This is
   the same discipline the real refactor sidesteps entirely by NOT needing a mutual THEOREM block. -/
mutual
  inductive EValue : YamlValue → Prop where
    | scalar (s : Scalar) : EValue (.scalar s)
    | alias (n : String) : EValue (.alias n)
    | sequence (style : CollectionStyle) (items : Array YamlValue)
        (tag anchor : Option String)
        (h : ∀ i : Fin items.size, EValue items[i]) :
        EValue (.sequence style items tag anchor)
    | mapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
        (tag anchor : Option String)
        (hk : ∀ i : Fin pairs.size, ESkey pairs[i].1)   -- keys need the SAVED-KEY deliverable
        (hv : ∀ i : Fin pairs.size, EValue pairs[i].2) : -- values need the VALUE deliverable
        EValue (.mapping style pairs tag anchor)
  inductive ESkey : YamlValue → Prop where
    | scalar (s : Scalar) : ESkey (.scalar s)
    | alias (n : String) : ESkey (.alias n)
    | sequence (style : CollectionStyle) (items : Array YamlValue)
        (tag anchor : Option String)
        (h : ∀ i : Fin items.size, EValue items[i]) :   -- the #2 → #1 edge: seq values via the VALUE form
        ESkey (.sequence style items tag anchor)
    | mapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
        (tag anchor : Option String)
        (hk : ∀ i : Fin pairs.size, ESkey pairs[i].1)
        (hv : ∀ i : Fin pairs.size, EValue pairs[i].2) :
        ESkey (.mapping style pairs tag anchor)
end

/-- **THE DE-RISK.**  ONE `induction hg` over the REAL `Grammable` recursor delivers BOTH mirror
    deliverables; every cross-edge is read off the conjunction IH, never a sibling theorem.  No `mutual`
    block of theorems, no `Or`-nesting, no `induction`-inside-`mutual` gotcha — just a single induction
    whose IH carries both components.  This is the resolution the real #1/#2 refactor should take. -/
theorem grammable_gives_both (v : YamlValue) {inFlow : Bool}
    (hg : Grammable v inFlow) : EValue v ∧ ESkey v := by
  induction hg with
  | scalar s _ _ => exact ⟨.scalar s, .scalar s⟩
  | sequence style items tag anchor _ _ ih =>
      -- ih i : EValue items[i] ∧ ESkey items[i].  BOTH seq arms take EValue on items — the ESkey.sequence
      -- arm is the #2 → #1 edge, served from the SAME IH's `.1` component, no sibling call.
      exact ⟨.sequence style items tag anchor (fun i => (ih i).1),
             .sequence style items tag anchor (fun i => (ih i).1)⟩
  | mapping style pairs tag anchor _ _ _ ihk ihv =>
      -- ihk i : EValue pairs[i].1 ∧ ESkey pairs[i].1   (key sub-value, BOTH deliverables)
      -- ihv i : EValue pairs[i].2 ∧ ESkey pairs[i].2   (value sub-value, BOTH deliverables)
      -- The map arms need SAVED-KEY on keys (`.2`) and VALUE on values (`.1`): exactly the cross pattern
      -- that forces #1 → #2 today.  Here both come off the one conjunction IH.
      exact ⟨.mapping style pairs tag anchor (fun i => (ihk i).2) (fun i => (ihv i).1),
             .mapping style pairs tag anchor (fun i => (ihk i).2) (fun i => (ihv i).1)⟩

/-- The two projections the consumers see — `emit_scans_in_flow_rec_entry` / `_saved_key_rec_entry` become
    these thin `.1` / `.2` wrappers over the combined theorem; their existing signatures are unchanged. -/
theorem grammable_gives_value (v : YamlValue) {inFlow : Bool}
    (hg : Grammable v inFlow) : EValue v := (grammable_gives_both v hg).1

theorem grammable_gives_savedkey (v : YamlValue) {inFlow : Bool}
    (hg : Grammable v inFlow) : ESkey v := (grammable_gives_both v hg).2

end L4YAML.Proofs.EmitterScannability.MapProducerMutualResolutionProbe
