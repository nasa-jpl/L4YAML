import Tests.Reflections.RebaseFactFromEnclosingWindow

/-!
# Reflection 305 — the carrier ASSEMBLES from a per-window enclosing-facts `provider`: factor a heavy locate boundary as an EXISTENTIAL provider, discharge the assemble, PROBE the provider is satisfiable

Self-contained (core Lean) toy of `(i'-b-locate-enclosing)`'s factoring move
(`seqInteriorSeparators_of_enclosing_provider`).  The R304 rebase
(`succ_rebase`, imported below) is the CONSUME side — it spreads an *enclosing* window's fact to any
re-seated sub-window.  The PRODUCE side — *locate* the enclosing window and *supply* its fact — is
heavy (in L4YAML it needs the typed-stack opener, its matching close, and the seq body's
`SafeBodyUnit`).  So we FACTOR by [[ref-parametric-assembler-extraction]]: lift the locate into an
EXISTENTIAL `provider` hypothesis (`∀ window, gate → ∃ enclosing, preconditions ∧ encFact`), and
discharge the ASSEMBLE now — `carrier_of_provider` is one `obtain` + the proven `succ_rebase`.

**The new lesson over plain assembler-extraction:** the lifted hypothesis is an EXISTENTIAL the locator
must later satisfy, so before committing to the assembler, PROBE that the provider is *satisfiable* on
a concrete witness (`#guard succB enc = true`).  A perfectly-proven assembler over an UNSATISFIABLE
provider is a vacuous dead-end: `provider_mapT_unsat` shows that on the map body `{ con : con }`, where
the enclosing `Succ` is FALSE (`not_succ_map`), `ProviderAt mapT 1 4` cannot exist — feeding it to the
correct assembler would derive the false `Succ mapT 1 4`.  The `#guard succB mapT 1 4 = false` is
exactly the probe that catches this before any locator work.

This is the positive complement of [[ref-probe-provider-head-blind-gate]] (R303 — probe a provider
universal for FALSITY, to ABANDON a route): here we probe an extracted provider for SATISFIABILITY, to
VALIDATE the residual hypothesis the assembler stands on.
-/

namespace Tests.Reflections.ProbeProviderSatisfiableBeforeAssembler

set_option autoImplicit false

open Tests.Reflections.RebaseFactFromEnclosingWindow

/-- **Toy gate** for a window `[a,b)`: balanced AND its start `a` re-based to the enclosing top level.
    The real `SeqTypedInterior` carries an enclosing-SEQ conjunct (`btFold`-top `= some true`) whose
    LOCATE CONCLUSION is `bal loS a = 0`; here we fold that re-seating into the gate so the provider can
    read it off — the locator that recovers it from the typed stack is the residual this demo isolates,
    not models. -/
def Gate (T : List Tok) (lo a b : Nat) : Prop :=
  bal T a b = 0 ∧ bal T lo a = 0

/-- **The carrier** (toy `SeqInteriorSeparators`): at every gated sub-window, the toy `bodySuccFact`. -/
def CarrierAt (T : List Tok) (lo hi : Nat) : Prop :=
  ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → Gate T lo a b → Succ T a b

/-- **THE EXTRACTED PROVIDER** (toy of `seqInteriorSeparators_of_enclosing_provider`'s `provider`): for
    every gated sub-window, deliver the enclosing window `[loS,hiS)` with the rebase preconditions and
    its enclosing `Succ`.  This is the heavy locate boundary lifted into a single hypothesis. -/
def ProviderAt (T : List Tok) (lo hi : Nat) : Prop :=
  ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → Gate T lo a b →
    ∃ loS hiS, loS ≤ a ∧ b ≤ hiS ∧ bal T loS a = 0 ∧ Succ T loS hiS

/-- **THE ASSEMBLER** — the carrier reduces to the provider by one `obtain` + the proven `succ_rebase`.
    No locate, no per-window structure: the ASSEMBLE side is trivial, the locate isolated as the
    residual (the provider hypothesis). -/
theorem carrier_of_provider (T : List Tok) (lo hi : Nat) (prov : ProviderAt T lo hi) :
    CarrierAt T lo hi := by
  intro a b ha hab hb hg
  obtain ⟨loS, hiS, h1, h2, h3, h4⟩ := prov a b ha hab hb hg
  exact succ_rebase T loS a b hiS h1 h2 h3 h4

/-! ## The enclosing fact for the seq witness (the provider's deliverable, proven). -/

/-- `Succ seqT 1 4` — the enclosing seq body `[ con , con ]` satisfies the toy `bodySuccFact`: the
    `con` at `1` is followed by the `sep` at `2`; the `sep` at `2` contradicts the non-separator
    premise; the `con` at `3` closes the window (`k+1 = 4`). -/
theorem succ_seqT : Succ seqT 1 4 := by
  intro k h1 h2 _hbal hns
  have hk : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk with rfl | rfl | rfl
  · exact Or.inr ⟨by decide, by decide⟩      -- con at 1, next is sep
  · exact absurd hns (by decide)             -- sep at 2: isSep = true, contradicts hns
  · exact Or.inl (by decide)                 -- con at 3, k+1 = 4 = b closes

/-! ## POSITIVE — the provider is SATISFIABLE on the seq witness, and the assembler discharges. -/

/-- `ProviderAt seqT 1 4` holds: the enclosing window is the whole `[1,4)` (`loS = lo = 1`), so the
    rebase precondition `bal seqT loS a = 0` IS the gate's re-seating conjunct `hg.2`, and the enclosing
    fact is `succ_seqT`.  (The "root" case — enclosing is the outer seq.) -/
theorem provider_seqT : ProviderAt seqT 1 4 := by
  intro a b ha hab hb hg
  exact ⟨1, 4, ha, hb, hg.2, succ_seqT⟩

-- The carrier follows from the satisfiable provider, and a concrete sub-window inherits the fact.
example : CarrierAt seqT 1 4 := carrier_of_provider seqT 1 4 provider_seqT
example : Succ seqT 3 4 :=
  carrier_of_provider seqT 1 4 provider_seqT 3 4 (by decide) (by decide) (by decide)
    ⟨by decide, by decide⟩

-- The #guard satisfiability probe (the analog of the real `#guard` de-risk on `[[1,2],9]`):
-- the enclosing fact holds, so the provider is satisfiable.
#guard succB seqT 1 4 = true

/-! ## NEGATIVE — the LESSON: a perfectly-proven assembler over an UNSATISFIABLE provider is a
    dead-end.  On the map body `{ con : con }`, the gated window `[1,4)` has a FALSE enclosing `Succ`
    (`not_succ_map`), so `ProviderAt mapT 1 4` cannot exist — feeding it to the (correct!) assembler
    would derive the false `Succ mapT 1 4`.  Hence PROBE the provider is satisfiable before building
    atop the assembler. -/

-- The satisfiability probe is FALSE on the map: the enclosing fact fails, so NO provider exists.
#guard succB mapT 1 4 = false

/-- The provider is UNSATISFIABLE on the map window — proven via the assembler: any `ProviderAt mapT 1 4`
    would, through the correct `carrier_of_provider`, yield the false `Succ mapT 1 4`. -/
theorem provider_mapT_unsat : ¬ ProviderAt mapT 1 4 := by
  intro prov
  exact not_succ_map
    (carrier_of_provider mapT 1 4 prov 1 4 (by decide) (by decide) (by decide)
      ⟨by decide, by decide⟩)

end Tests.Reflections.ProbeProviderSatisfiableBeforeAssembler
