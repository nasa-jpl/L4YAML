/-! # Reflection 513 — the MAP separator carrier, the `some false` mirror of the seq carrier

R512 collapsed the SEQ half of the frontier obligation `FlowSubrangesOk tokens` to a single root carrier
`SeqInteriorSeparators tokens 2 (size-2)`, leaving the MAP half as its SEVEN raw per-window producers
(`h_map_rec` + the six map-grammar facts) — the recorded seq/map ASYMMETRY. R513
(`MapInteriorSeparators`) lands the FOUNDATION of the map mirror: the gate `MapTypedInterior`, the bundled
`MapGrammarFacts`, the carrier `MapInteriorSeparators`, and its three subset-restriction edges
(`_narrow`/`_descend`/`_advance`).

Two design facts the brick pins, each modelled below over a tiny toy:

* **Window-absolute ⇒ subset restriction is fact-count-AGNOSTIC.**  Every gate condition and every one of
  the six asserted facts is keyed ONLY on the sub-window `a, b` and the global tokens — never on the outer
  origin `lo`/`hi`, which enters solely through the domain bounds `lo ≤ a`, `b ≤ hi`.  So `_narrow` reuses
  the body verbatim and shrinks only the domain; its proof is BYTE-IDENTICAL to the seq carrier's
  (`SeqInteriorSeparators_narrow`) however many facts are bundled — `_narrow` never inspects the body.
  ([[ref-window-absolute-gate-subset-restriction]].)
* **The map gate is the `some false` DUAL of `some true`.**  The `btStep` convention is `true = [`,
  `false = {`; the seq gate reads a `btFold`-top `= some true`, the map gate `= some false`.  The carrier
  shape is type-AGNOSTIC: the same `narrow`/`descend`/`advance` core drives both axes off one design.
* **Marker-FREE ⇒ re-projects for free.**  The consumer's six hypotheses carry `flowMappingEnd`/
  `flowMappingStart` boundary premises; the carrier drops them (its `= some false` enclosure identifies the
  map interior instead), so the carrier fact is STRICTLY STRONGER and implies each marker-bearing consumer
  hypothesis by simply discarding the markers — the next brick `mapGrammarFacts_of_mapRoot` at
  `a := lo, b := hi`.

This demo (self-contained core Lean, no imports) models all three: a boolean-tagged gate (`false` = map),
a multi-conjunct grammar bundle, the carrier as a guarded universal over sub-windows, the three edges
proven by `Nat.le_trans` exactly as in the real file, a `projects_to_consumer` lemma dropping a marker
premise, and a concrete `run`.

Axioms: `demo` depends on NONE (the real `MapInteriorSeparators_narrow`/`_advance` carry `[propext]`,
inherited from `Prop`-level structure; the toy sheds even that).
-/

namespace MapCarrierFoundation

/-- Toy token alphabet: `0` = separator (`,`), `1` = key, `2` = value, `3` = content. -/
abbrev Toks := List Nat
def SEP : Nat := 0
def KEY : Nat := 1
def VALUE : Nat := 2
def CONTENT : Nat := 3

/-- Toy `flowBracketBalance` stand-in over `[a,b)` — abstract; the carrier never computes it, it only
    threads it window-absolutely (keyed on `a`, never on the outer origin). -/
def bal (_t : Toks) (_a _b : Nat) : Int := 0

/-- Toy `(btFold (some []) (tokens.toList.take a)).bind (·.head?)` — the enclosing-opener TOP at `a`:
    `some false` = a `{` (map), `some true` = a `[` (seq).  Constant in the toy. -/
def enclTop (_t : Toks) (_a : Nat) : Option Bool := some false

/-- **The gate**: a MAP interior reads the enclosing-opener top `= some false` — the `some false` DUAL of
    the seq gate's `= some true`.  A genuine `Prop` (no data field): the discriminator is an equation. -/
structure Gate (t : Toks) (a b : Nat) : Prop where
  balanced : bal t a b = 0
  /-- `some false` = enclosing `{` (map); the dual of the seq gate's `some true`. -/
  isMap : enclTop t a = some false

/-- **The bundled grammar facts**, relativised to `[a,b)` and keyed window-absolutely on `a` (toy stand-in
    for the six `MapGrammarFacts`).  Multi-conjunct on purpose: to exhibit that `_narrow` ignores them. -/
structure GrammarFacts (t : Toks) (a b : Nat) : Prop where
  keyContent : a ≤ b          -- toy of `h_key_content` (key → content), keyed on a, b only
  valueContent : a ≤ b        -- toy of `h_value_content`
  noOuterOrigin : True        -- the body never mentions an outer `lo`/`hi`

/-- **The map carrier** — a guarded universal over sub-windows `[a,b) ⊆ [lo,hi)` (mirror of
    `MapInteriorSeparators`).  `lo`/`hi` enter ONLY through the domain bounds. -/
def MapCarrier (t : Toks) (lo hi : Nat) : Prop :=
  ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → Gate t a b → GrammarFacts t a b

/-- **Subset restriction (the descend/advance edge core).**  Byte-identical to the seq carrier's
    `_narrow`: body reused verbatim, domain shrunk; the bundled facts are never inspected. -/
theorem MapCarrier_narrow {t : Toks} {lo hi lo' hi' : Nat}
    (h_lo : lo ≤ lo') (h_hi : hi' ≤ hi) (h : MapCarrier t lo hi) :
    MapCarrier t lo' hi' := by
  intro a b ha hab hb hgate
  exact h a b (Nat.le_trans h_lo ha) hab (Nat.le_trans hb h_hi) hgate

/-- **DESCEND.**  Into a nested interior `[lo',hi') ⊆ [lo,hi)` — pure subset restriction. -/
theorem MapCarrier_descend {t : Toks} {lo hi lo' hi' : Nat}
    (h_lo : lo ≤ lo') (h_hi : hi' ≤ hi) (h : MapCarrier t lo hi) :
    MapCarrier t lo' hi' :=
  MapCarrier_narrow h_lo h_hi h

/-- **ADVANCE.**  Past a separator at `m` to the tail `[m+1, hi)` — `hi` unchanged. -/
theorem MapCarrier_advance {t : Toks} {lo hi m : Nat}
    (h_lo : lo ≤ m + 1) (h : MapCarrier t lo hi) :
    MapCarrier t (m + 1) hi :=
  MapCarrier_narrow h_lo (Nat.le_refl hi) h

/-- A MARKER-bearing consumer hypothesis (toy of one of the six `flowSubrangesOk_of_window_producers`
    hypotheses): the same fact, GUARDED by a boundary marker premise the carrier drops. -/
def ConsumerFact (_t : Toks) (lo hi : Nat) : Prop :=
  -- `marker` = `tokens[hi]!.val = .flowMappingEnd`, present in the consumer, absent from the carrier.
  (∃ marker : Prop, marker) → lo ≤ hi

/-- **Marker-free ⇒ re-projects for free.**  The carrier fact (no markers) implies the marker-bearing
    consumer hypothesis by simply DISCARDING the marker premise — the carrier is strictly stronger.
    This is `mapGrammarFacts_of_mapRoot` in miniature (instantiated at `a := lo, b := hi`). -/
theorem projects_to_consumer {t : Toks} {lo hi : Nat}
    (h : MapCarrier t lo hi) (hgate : Gate t lo hi) (h_le : lo ≤ hi) :
    ConsumerFact t lo hi := by
  intro _marker
  exact (h lo hi (Nat.le_refl lo) h_le (Nat.le_refl hi) hgate).keyContent

/-- A concrete map interior `[0,2)` over `[ KEY, CONTENT ]` (counts irrelevant to the toy gate). -/
def sample : Toks := [KEY, CONTENT]

theorem sample_carrier : MapCarrier sample 0 2 :=
  fun _a _b _ hab _ _ => ⟨hab, hab, trivial⟩

theorem sample_gate : Gate sample 0 2 := ⟨rfl, rfl⟩

/-- A RUN: descend the carrier to a sub-window, then re-project its fact to a marker-bearing consumer
    hypothesis — the seq/map symmetric foundation in action. -/
theorem run : ConsumerFact sample 0 2 :=
  projects_to_consumer sample_carrier sample_gate (by decide)

/-- The demo deliverable: the three subset-restriction edges hold, AND the marker-free carrier projects
    to a marker-bearing consumer hypothesis for free. -/
theorem demo :
    MapCarrier sample 0 1
    ∧ MapCarrier sample 1 2
    ∧ ConsumerFact sample 0 2 :=
  ⟨MapCarrier_descend (Nat.le_refl 0) (by decide) sample_carrier,
   MapCarrier_advance (lo := 0) (Nat.zero_le 1) sample_carrier,
   run⟩

end MapCarrierFoundation

-- Axiom audit: the toy sheds even `propext` (the real edges carry `[propext]`).
#print axioms MapCarrierFoundation.demo
#print axioms MapCarrierFoundation.run
