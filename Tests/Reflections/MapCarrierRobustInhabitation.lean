import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators
import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner

/-!
# Reflection 541 — INHABITATION PROBE for the boundary-robust map carrier `MapInteriorSeparators'`

This file is the inhabitation test the [[feedback-inhabitation-debt-validate-target-defs]] discipline
demands, applied to the NEW boundary-robust carrier landed in
`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean` (R541). Unlike the abstract
companion `BoundaryRobustVsFragileFact.lean` (the principle in the small), this file imports the REAL
defs and probes them. It lives under `Tests/` — NOT inline in the source — so the carrier's
inhabitation is a build-time REGRESSION test, kept separate from the library definition (the
discipline's "write the inhabitation tests in `tests/`" rule).

## What R540 caught, and what this probes

R540 found the STRICT carrier `MapInteriorSeparators` UNPROVABLE: its `MapGrammarFacts` is
boundary-FRAGILE — at a window that ends one past a `flowBracketDelta`-`0` `.key`/`.value` marker
(`b = k + 1`), conjunct 1 demands `k + 1 < b`, i.e. `b < b`, FALSE. The strict carrier had been
surrounded by ~8 consumers before anyone checked it was inhabited (the inhabitation DEBT).

The robust replacement `MapGrammarFacts'` adds a window-close escape `b ≤ <position>` to each fragile
conjunct. This file PROBES, against the REAL defs, the exact boundary the strict form died on
(inhabitation-debt rule 2 — instantiate the universal at the DEGENERATE/EDGE window `b = a` / `b = a + 1`,
never the comfortable interior):

* `mapGrammarFacts'_degenerate` — the robust facts hold on EVERY window-close window `[k, k+1)`, for
  EVERY stream, UNCONDITIONALLY. This is the boundary the strict facts are refuted on.
* `mapGrammarFacts_degenerate_key_false` — the STRICT facts are REFUTED on that same window whenever
  the trigger is a `.key`. This is the one-line probe that, run at the strict carrier's birth, would
  have caught the bug before any consumer was built on top.
* `mapInteriorSeparators'_unit` — the robust CARRIER itself holds on a unit span `[lo, lo+1)`, for
  EVERY stream (every gated sub-window has width ≤ 1, so the empty-window and window-close cases cover
  it). The strict carrier `MapInteriorSeparators tokens lo (lo+1)` is NOT provable this way.
-/

namespace MapCarrierRobustInhabitation

open L4YAML
open L4YAML.Proofs.ParserGrammable
open L4YAML.Proofs.EmitterScannability

/-- The robust facts hold on the EMPTY window `[a, a)` — every conjunct's `a ≤ k → k < a` premise
    pair is contradictory, so all six are vacuous. -/
theorem mapGrammarFacts'_empty (tokens : Array (Positioned YamlToken)) (a : Nat) :
    MapGrammarFacts' tokens a a := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k h1 h2; exact absurd h2 (by omega)
  · intro k h1 h2; exact absurd h2 (by omega)
  · intro k h1 h2; exact absurd h2 (by omega)
  · intro k h1 h2; exact absurd h2 (by omega)
  · intro k j h1 h2; exact absurd h2 (by omega)
  · intro k j h1 h2; exact absurd h2 (by omega)

/-- **The robust facts SURVIVE the window-close boundary** — `MapGrammarFacts' tokens k (k+1)` holds
    for EVERY stream and EVERY `k`. The only candidate trigger position is `k` itself, and every
    fragile conjunct's escape `b ≤ <position>` fires there (`k + 1 ≤ k + 1`, `k + 1 ≤ k + 2`);
    conjuncts 5/6 are vacuous (no room for an interior closer `j` with `k + 1 < j < k + 1`). This is
    exactly the boundary the strict `MapGrammarFacts` is refuted on. -/
theorem mapGrammarFacts'_degenerate (tokens : Array (Positioned YamlToken)) (k : Nat) :
    MapGrammarFacts' tokens k (k + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k' h1 h2 _ _; exact Or.inl (by omega)
  · intro k' h1 h2 _ _ _; exact Or.inl (by omega)
  · intro k' h1 h2 _ _; exact Or.inl (by omega)
  · intro k' h1 h2 _ _ _; exact Or.inl (by omega)
  · intro k' j h1 h2 _ _ h3 h4 _ _; exact absurd h4 (by omega)
  · intro k' j h1 h2 _ _ h3 h4 _ _; exact absurd h4 (by omega)

/-- **The STRICT facts are REFUTED on the same window** when the trigger is a `.key`: conjunct 1
    demands `k + 1 < k + 1`. This is the one-line, `decide`-cheap probe that — owed at the strict
    carrier's BIRTH — would have exposed the inhabitation bug R540 only found after ~8 consumers had
    been built on top. -/
theorem mapGrammarFacts_degenerate_key_false (tokens : Array (Positioned YamlToken)) (k : Nat)
    (hk : tokens[k]!.val = .key) : ¬ MapGrammarFacts tokens k (k + 1) := by
  intro h
  obtain ⟨h1, _⟩ := h
  have hbal : flowBracketBalance tokens k k = 0 := by simp [flowBracketBalance]
  have hcontra := (h1 k (Nat.le_refl k) (by omega) hbal hk).1
  omega

/-- **The robust CARRIER is inhabited on a unit span** `[lo, lo+1)` — for EVERY stream. Every gated
    sub-window `[a,b) ⊆ [lo, lo+1)` has width `b - a ≤ 1`, so it is either the empty window
    (`mapGrammarFacts'_empty`) or a window-close window (`mapGrammarFacts'_degenerate`). The strict
    carrier `MapInteriorSeparators tokens lo (lo+1)` is NOT provable this way — its facts are refuted
    at the very window-close window this one survives (R540's `{a:1}` cut window `[1,2)`). -/
theorem mapInteriorSeparators'_unit (tokens : Array (Positioned YamlToken)) (lo : Nat) :
    MapInteriorSeparators' tokens lo (lo + 1) := by
  intro a b ha hab hb _hgate
  rcases Nat.lt_or_ge a b with hLt | hGe
  · have hb1 : b = a + 1 := by omega
    rw [hb1]; exact mapGrammarFacts'_degenerate tokens a
  · have hEq : a = b := by omega
    rw [← hEq]; exact mapGrammarFacts'_empty tokens a

/-- **De-risk for the R542 ASSEMBLE half** — `mapInteriorSeparators'_of_enclosing_provider` is
    NON-VACUOUS. Fed a concrete provider it yields an inhabited carrier, so its NEW `provider`
    HYPOTHESIS shape (`∀ window, gate → ∃ enclosing, … ∧ MapGrammarFacts' loS hiS`) is satisfiable —
    the inhabitation-debt rule-3 check on the assembler (a hypothesis with no producer is the alarm).

    On the unit span `[lo, lo+1)` the IDENTITY provider works: each gated sub-window `[a,b)` is its own
    enclosing window, re-seated trivially (`loS = a`, `hiS = b`, `flowBracketBalance tokens a a = 0`),
    with its facts supplied by `mapGrammarFacts'_empty` / `mapGrammarFacts'_degenerate` (every such
    window has width `b - a ≤ 1`). The assembler drives that provider through `mapGrammarFacts_rebase'`
    and reproduces `mapInteriorSeparators'_unit` — the same inhabited carrier, now via the real
    ASSEMBLE path rather than directly. -/
theorem mapInteriorSeparators'_of_enclosing_provider_unit
    (tokens : Array (Positioned YamlToken)) (lo : Nat) :
    MapInteriorSeparators' tokens lo (lo + 1) :=
  mapInteriorSeparators'_of_enclosing_provider tokens lo (lo + 1)
    (fun a b ha hab hb _hgate =>
      ⟨a, b, Nat.le_refl a, Nat.le_refl b, by simp [flowBracketBalance],
        by
          rcases Nat.lt_or_ge a b with hLt | hGe
          · have hb1 : b = a + 1 := by omega
            rw [hb1]; exact mapGrammarFacts'_degenerate tokens a
          · have hEq : a = b := by omega
            rw [← hEq]; exact mapGrammarFacts'_empty tokens a⟩)

/-- **De-risk for the R543 provider ASSEMBLE half** — `mapEnclosingFacts'_provider_of_located` is
    NON-VACUOUS, and the R542 assembler's `provider` is reachable THROUGH it.  Where R542's
    `mapInteriorSeparators'_of_enclosing_provider_unit` built the per-window existential inline
    (`⟨a, b, …⟩`), this routes it through the named `mapEnclosingFacts'_provider_of_located` assembler:
    at each gated sub-window `[a,b)` of the unit span `[lo, lo+1)`, feed the IDENTITY enclosing window
    (`loS = a`, `hiS = b`, re-seat `flowBracketBalance tokens a a = 0`) with its robust facts (width
    `b - a ≤ 1`, so `mapGrammarFacts'_empty` / `mapGrammarFacts'_degenerate`), and the assembler packages
    the provider existential.  Driving that provider through the R542 assembler reproduces the inhabited
    carrier — confirming the lifted `MapGrammarFacts'` hypothesis the parametric-assembler split
    introduces is satisfiable (the assembler aims at a reachable producer, not a trap), via the real
    LOCATE-output→provider-of-located path rather than an inline tuple. -/
theorem mapInteriorSeparators'_via_provider_of_located_unit
    (tokens : Array (Positioned YamlToken)) (lo : Nat) :
    MapInteriorSeparators' tokens lo (lo + 1) :=
  mapInteriorSeparators'_of_enclosing_provider tokens lo (lo + 1)
    (fun a b _ha _hab _hb _hgate =>
      mapEnclosingFacts'_provider_of_located tokens a b a b
        (Nat.le_refl a) (Nat.le_refl b) (by simp [flowBracketBalance])
        (by
          rcases Nat.lt_or_ge a b with hLt | hGe
          · have hb1 : b = a + 1 := by omega
            rw [hb1]; exact mapGrammarFacts'_degenerate tokens a
          · have hEq : a = b := by omega
            rw [← hEq]; exact mapGrammarFacts'_empty tokens a))

/-- **De-risk for the map DISPATCHER** — `mapInteriorSeparators'_of_safebody_and_descent` is
    NON-VACUOUS, and its NEW `desc` hypothesis is satisfiable (inhabitation-debt rule 3).  The
    dispatcher is the `dite` that routes each gated sub-window to one of two suppliers: the window's
    OWN robust facts `h_facts` (the `flowBracketBalance tokens lo a = 0` branch) or the descent
    provider `desc` (the `≠ 0` branch).  On the unit span `[lo, lo+1)` we feed it BOTH concretely:

    * `h_facts := mapGrammarFacts'_degenerate tokens lo : MapGrammarFacts' tokens lo (lo+1)` — the
      window's own robust facts, surviving the window-close boundary;
    * a concrete IDENTITY `desc`: at each nested gated sub-window `[a,b)` (width `b - a ≤ 1` here),
      hand back `[a,b)` as its own enclosing window (`loS = a`, `hiS = b`, re-seat
      `flowBracketBalance tokens a a = 0`) with robust facts via `mapGrammarFacts'_degenerate` /
      `mapGrammarFacts'_empty`, routed through the R543 `mapEnclosingFacts'_provider_of_located`.

    The dispatcher drives the R542 assembler and recovers `mapInteriorSeparators'_unit` — the same
    inhabited carrier, now through the real DISPATCH path with BOTH `dite` branches type-checked
    (the `= 0` branch fires at `a = lo`, the `≠ 0` branch is available at `a = lo+1` when the window
    opener carries depth).  Confirms the dispatcher aims at reachable suppliers, not a trap, before
    the root seed `mapRoot_mapInteriorSeparators'` and the map descent locator that produce them
    exist. -/
theorem mapInteriorSeparators'_via_dispatcher_unit
    (tokens : Array (Positioned YamlToken)) (lo : Nat) :
    MapInteriorSeparators' tokens lo (lo + 1) :=
  mapInteriorSeparators'_of_safebody_and_descent tokens lo (lo + 1)
    (mapGrammarFacts'_degenerate tokens lo)
    (fun a b _ha _hab _hb _hbal _hgate =>
      mapEnclosingFacts'_provider_of_located tokens a b a b
        (Nat.le_refl a) (Nat.le_refl b) (by simp [flowBracketBalance])
        (by
          rcases Nat.lt_or_ge a b with hLt | hGe
          · have hb1 : b = a + 1 := by omega
            rw [hb1]; exact mapGrammarFacts'_degenerate tokens a
          · have hEq : a = b := by omega
            rw [← hEq]; exact mapGrammarFacts'_empty tokens a))

/-! ## R545 — the FIRST non-degenerate `MapGrammarFacts` witness + the strict→robust connector probed

R540 refuted the STRICT `MapGrammarFacts` at the window-close CUT (`[1,2)`), establishing one pole of
its boundary-fragility. This is the OTHER pole: the strict facts are genuinely TRUE on a COMPLETE map
body, where every marker's content sits truly interior. Together the two poles fully characterise the
fragility — and this complete-window witness is the non-degenerate inhabitant that inhabitation-debt
rule 2 demanded BEFORE the strict→robust connector `mapGrammarFacts'_of_mapGrammarFacts` could land
(a connector whose input type were only ever empty would be a vacuous function). The witness exercises
conjuncts 1–4 FIRING (not vacuously), and the connector is then read back through the strict-interior
arm to confirm the robust output it produces is genuine, not the window-close escape. -/

/-- Positioned-token helper: wrap a `YamlToken` with a `default` position (the position is irrelevant
    to `MapGrammarFacts`, which inspects only `.val`). -/
private def pt (t : YamlToken) : Positioned YamlToken := { pos := default, val := t }

/-- The canonical `{a: 1}` flow-map token stream — `{`, `.key`, `scalar "a"`, `.value`, `scalar "1"`,
    `}` (indices 0–5). The complete map BODY is the window `[1, 5)` (strictly between the braces);
    index 5 (`}`) is read by conjunct 4 at the window edge. This is the dual pole to R540's degenerate
    refutation on the cut window `[1, 2)`. -/
def fixtureMapA1 : Array (Positioned YamlToken) :=
  #[pt .flowMappingStart, pt .key, pt (.scalar "a" .plain),
    pt .value, pt (.scalar "1" .plain), pt .flowMappingEnd]

/-- **The FIRST non-degenerate `MapGrammarFacts` witness** — the strict facts hold on the complete
    `{a:1}` map body `[1, 5)`, with conjuncts 1–4 genuinely FIRING: at the key `k = 1` content sits at
    index 2 and the `.value` at index 3 (conjuncts 1, 2); at the value `k = 3` content sits at index 4
    and the closing `}` at index 5 (conjuncts 3, 4). Conjuncts 5/6 are vacuous — the only interior
    positions `j ∈ {3,4}` carry `flowBracketDelta = 0`, not `-1`. The dual of R540's
    `mapGrammarFacts_degenerate_key_false`: strict FALSE at the cut, strict TRUE here. -/
theorem mapGrammarFacts_complete_window : MapGrammarFacts fixtureMapA1 1 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- conjunct 1: key → content-start at k+1 (fires at k = 1)
  · intro k hak hkb _hbal htok
    have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    · exact ⟨by omega, Or.inl ⟨"a", .plain, by rfl⟩⟩
    · exact absurd htok (by decide)
    · exact absurd htok (by decide)
    · exact absurd htok (by decide)
  -- conjunct 2: key + scalar → .value at k+2 (fires at k = 1)
  · intro k hak hkb _hbal htok _hsc
    have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    · exact ⟨by omega, by rfl⟩
    · exact absurd htok (by decide)
    · exact absurd htok (by decide)
    · exact absurd htok (by decide)
  -- conjunct 3: value → content-start at k+1 (fires at k = 3)
  · intro k hak hkb _hbal htok
    have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    · exact absurd htok (by decide)
    · exact absurd htok (by decide)
    · exact ⟨by omega, Or.inl ⟨"1", .plain, by rfl⟩⟩
    · exact absurd htok (by decide)
  -- conjunct 4: value + scalar → flowEntry / (mappingEnd ∧ k+2=b) at k+2 (fires at k = 3, mappingEnd arm)
  · intro k hak hkb _hbal htok _hsc
    have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    · exact absurd htok (by decide)
    · exact absurd htok (by decide)
    · exact ⟨by omega, Or.inr ⟨by rfl, by omega⟩⟩
    · exact absurd htok (by decide)
  -- conjunct 5: key + interior closer j → .value at j+1 — vacuous (no delta = -1 inside [1,5))
  · intro k j hak _hkb _hbal _htok hkj hjb hdelta _hbalj
    have hj : j = 3 ∨ j = 4 := by omega
    rcases hj with rfl | rfl
    · exact absurd hdelta (by decide)
    · exact absurd hdelta (by decide)
  -- conjunct 6: value + interior closer j → flowEntry/mappingEnd at j+1 — vacuous likewise
  · intro k j hak _hkb _hbal _htok hkj hjb hdelta _hbalj
    have hj : j = 3 ∨ j = 4 := by omega
    rcases hj with rfl | rfl
    · exact absurd hdelta (by decide)
    · exact absurd hdelta (by decide)

/-- **Non-vacuity probe for the R545 connector** `mapGrammarFacts'_of_mapGrammarFacts`. Fed the
    complete-window witness, the connector produces robust facts whose conjunct 1 at the key position
    `k = 1` lands in the GENUINE strict-interior arm (`Or.inr`), NOT the window-close escape `b ≤ k+1`
    (here `5 ≤ 2`, refuted by `omega`). Reading the connector's output back through the disjunction
    confirms it carries a real interior content fact — the connector is exercised on a real inhabitant
    of its fragile domain, not vacuously (inhabitation-debt rule 2/3). -/
theorem mapGrammarFacts'_complete_window_fires :
    isFlowContentStart fixtureMapA1[2]!.val := by
  have hrobust : MapGrammarFacts' fixtureMapA1 1 5 :=
    mapGrammarFacts'_of_mapGrammarFacts fixtureMapA1 1 5 mapGrammarFacts_complete_window
  rcases hrobust.1 1 (by omega) (by omega) (by decide) (by decide) with hesc | ⟨_, hc⟩
  · exact absurd hesc (by omega)
  · exact hc

/-! ## R546 — the robust → strict bridge probed by a strict → robust → strict ROUND-TRIP

R545 landed the FREE direction (strict → robust, `mapGrammarFacts'_of_mapGrammarFacts`). R546 lands the
genuine INVERSE (`mapGrammarFacts_of_mapGrammarFacts'`, robust → strict), which is boundary-FRAGILE: it
holds only at a complete body where each window-close escape can be REFUTED, with the refuters (the "no
marker hugs the close" emission facts) lifted as hypotheses. This probe closes the loop on the `{a:1}`
body `[1,5)`: weaken the strict witness to robust (R545 connector), then re-strengthen it back to strict
through the bridge, supplying the five refuters proved INDEPENDENTLY off the concrete fixture — NOT
projected out of the strict witness (inhabitation-debt rule 3: the lifted refuter hypotheses have a real
producer at the genuine close, so the bridge's domain is genuinely inhabited, not a trap). Recovering the
strict witness confirms the bridge is the connector's true inverse on a complete body. -/

/-- **The robust → strict bridge probed by a full ROUND-TRIP** on the `{a:1}` complete body `[1, 5)`:
    `mapGrammarFacts_complete_window` (strict) ──connector──▶ robust ──bridge──▶ strict, recovering
    `MapGrammarFacts fixtureMapA1 1 5`. The five refuters are proved INDEPENDENTLY here (case-split on the
    concrete index, fire the in-window bound via `omega`, kill the off-window position via
    `absurd … (by decide)`) — the genuine close-structure facts the windowed-map separator leaf must
    eventually produce off emission, exhibited at the fixture to show they are reachable, not vacuous. -/
theorem mapGrammarFacts_strict_roundtrip : MapGrammarFacts fixtureMapA1 1 5 := by
  have hrobust : MapGrammarFacts' fixtureMapA1 1 5 :=
    mapGrammarFacts'_of_mapGrammarFacts fixtureMapA1 1 5 mapGrammarFacts_complete_window
  refine mapGrammarFacts_of_mapGrammarFacts' fixtureMapA1 1 5 hrobust ?_ ?_ ?_ ?_ ?_
  -- hk1: every `.key` in the body has its content successor strictly inside (no key at index 4)
  · intro k hak hkb _ htok
    rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl | rfl <;>
      first | omega | exact absurd htok (by decide)
  -- hk2: every `.key` with a scalar successor has its `.value` strictly inside
  · intro k hak hkb _ htok _hsc
    rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl | rfl <;>
      first | omega | exact absurd htok (by decide)
  -- hv1: every `.value` in the body has its content successor strictly inside (no value at index 4)
  · intro k hak hkb _ htok
    rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl | rfl <;>
      first | omega | exact absurd htok (by decide)
  -- hv2: every `.value` with a scalar successor has its separator/close at most at the boundary
  · intro k hak hkb _ htok _hsc
    rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl | rfl <;>
      first | omega | exact absurd htok (by decide)
  -- hk5: no interior closer `j` (every body position carries `flowBracketDelta = 0`, not `-1`)
  · intro k j hak hkb _ _htok hkj hjb hdelta _
    rcases (show j = 3 ∨ j = 4 by omega) with rfl | rfl <;> exact absurd hdelta (by decide)

/-! ## R547 — the BRACKET-VALUED boundary catches the carrier's DEEPER falsity (rule 2, untested edge)

Every probe above (R541–R546) used the SCALAR-ONLY fixture `{a:1}`, where conjuncts 5/6 — keyed on an
interior bracket closer `j` with `flowBracketDelta = -1` — are VACUOUS (no body position carries
`-1`). So conjuncts 5/6 of `MapGrammarFacts'` (and the identical `MapLocated.h_key_bracket_succ`
consumer field, `NonemptyStructure.lean:10531`) had been validated by NOBODY on a real bracket-bearing
map. This is exactly inhabitation-debt rule 2: *probe the boundary, not the middle* — and the
untested boundary here is not the window CLOSE (which R541 made robust) but a bracket-VALUED entry.

Probing that boundary against REAL emission refutes the robust carrier. Conjunct 5 is keyed on a
`.key` and a GENERIC depth-0-returning closer `j` with NO guard that `tokens[k+1]` is a bracket-start
(unlike `MapBodyProps.key_bracket_value`, M5, `ParserGrammableBase.lean:1240`, which IS so guarded).
So on `{a: [1], b: 2}` the FIRST key (index 2) sees the FIRST VALUE's `]` closer (index 7, balance
back to 0 at 8) and conjunct 5 demands `.value` at index 8 — but index 8 is `.flowEntry` (the pair
separator). FALSE. And robustness cannot save it: the window-close escape `b ≤ j+1` is `13 ≤ 8`,
refuted, because the false firing is at an INTERIOR closer, a fragility orthogonal to the window-close
one R541 fixed (rule 4 — the robust dual inherited the strict conjunct-5 SHAPE, and that shape was
itself wrong, not merely boundary-fragile). The salvage is a refactor not a teardown
([[ref-additive-parallel-type-over-shared-edit]]): re-key conjuncts 5/6 to the M5/M8 bracket-start
guard (fire only on a COMPLEX KEY whose `j` is its own bracket's matching close), landed as a new
additive `MapGrammarFacts''` and re-probed on BOTH fixtures — the next brick, NOT a strict-def edit
(whose R513–R546 consumers depend on the exact shape).

The fixture is GROUNDED in real emission (rule 5 — probe real data, not a hand-built guess that might
not correspond to any emitted map): the `#guard` proves `fixtureMapSeqVal`'s val-stream IS
`scanFiltered (emit {a:[1], b:2})`. Lives under `Tests/` as a build-time regression that the bug
stays caught until the guarded conjuncts land. -/

/-- Plain scalar value helper. -/
private def sc (s : String) : YamlValue := .scalar { content := s, style := .plain }

/-- `{a: [1], b: 2}` — the smallest map exercising conjunct 5 at an interior (non-window-close) closer:
    a bracket-valued FIRST entry followed by a second entry, so the value's `]` closer has `j + 1 ≠ b`. -/
def valMapSeqVal : YamlValue :=
  .mapping .flow #[(sc "a", .sequence .flow #[sc "1"]), (sc "b", sc "2")]

/-- The REAL `scanFiltered (emit valMapSeqVal)` filtered token stream, hand-mirrored for `decide`.
    Indices: 0 `streamStart`, 1 `{`, 2 `.key`, 3 `"a"`, 4 `.value`, 5 `[`, 6 `"1"`, 7 `]`,
    8 `.flowEntry`, 9 `.key`, 10 `"b"`, 11 `.value`, 12 `"2"`, 13 `}`, 14 `streamEnd`.  The map BODY is
    the window `[2, 13)` (= `[2, size - 2)`, the root convention `seqRoot_seqInteriorSeparators` uses).
    Plain scalars emit double-quoted (`emit {a:1}` ⇒ `{"a": "1"}`), irrelevant to the grammar facts
    (which inspect only token TAGS, not scalar content/style). -/
def fixtureMapSeqVal : Array (Positioned YamlToken) :=
  #[pt .streamStart, pt .flowMappingStart, pt .key, pt (.scalar "a" .doubleQuoted),
    pt .value, pt .flowSequenceStart, pt (.scalar "1" .doubleQuoted), pt .flowSequenceEnd,
    pt .flowEntry, pt .key, pt (.scalar "b" .doubleQuoted), pt .value,
    pt (.scalar "2" .doubleQuoted), pt .flowMappingEnd, pt .streamEnd]

-- **Grounding (rule 5).** The fixture's val-stream IS the real scanner output for `emit valMapSeqVal`
-- — so the falsity below is a falsity on a GENUINELY EMITTED map, not a hand-built artifact.
#guard (L4YAML.Scanner.scanFiltered (L4YAML.Emit.emit valMapSeqVal)).toOption.map
          (fun toks => toks.toList.map (fun t => t.val))
        = some (fixtureMapSeqVal.toList.map (fun t => t.val))

/-- **The gate FIRES on the genuine body window** `[2, 13)` — it is balanced, `{`-enclosed, and Dyck
    (every prefix balance `≥ 0`). So the carrier `MapInteriorSeparators'` genuinely must cover this
    window: there is no gate technicality excusing it from asserting the per-window fact. -/
theorem mapTypedInterior_bracketVal : MapTypedInterior fixtureMapSeqVal 2 13 := by
  refine ⟨by decide, by decide, ?_⟩
  intro i h2 h13
  rcases (show i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 by omega)
    with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- **The ROBUST per-window fact is FALSE on this gated body window.** Conjunct 5 fires at the `.key`
    (index 2) and the VALUE's `]` closer (index 7, `flowBracketBalance … 8 = 0`) and demands `.value`
    at index 8 — but index 8 is `.flowEntry`. The window-close escape `13 ≤ 8` is refuted (`omega`):
    the firing is at an INTERIOR closer, which robustness does not protect. This is the one-line probe
    that — owed when conjuncts 5/6 were FIRST written — would have caught the bug before the R542–R546
    assembler/connector/bridge chain was built on top. -/
theorem mapGrammarFacts'_bracketVal_false : ¬ MapGrammarFacts' fixtureMapSeqVal 2 13 := by
  intro h
  obtain ⟨_, _, _, _, c5, _⟩ := h
  have hb_k : flowBracketBalance fixtureMapSeqVal 2 2 = 0 := by decide
  have hb_j : flowBracketBalance fixtureMapSeqVal 2 8 = 0 := by decide
  rcases c5 2 7 (by omega) (by omega) hb_k (by decide) (by omega) (by omega) (by decide) hb_j with
    hesc | ⟨_, hval⟩
  · omega
  · exact absurd hval (by decide)

/-- **THE INHABITATION BUG, made a theorem.** The boundary-robust carrier `MapInteriorSeparators'` —
    the R541–R546 target — is REFUTED on `{a:[1], b:2}`, a genuine flow map. Instantiated at its own
    gated body window `[2, 13)` it would assert the per-window fact that `mapGrammarFacts'_bracketVal_false`
    refutes. So NO producer (`mapRoot_mapInteriorSeparators'`, the planned next brick) can build this
    carrier off emission as currently defined — the conjuncts 5/6 must gain the M5/M8 bracket-start
    guard first. -/
theorem mapInteriorSeparators'_bracketVal_false : ¬ MapInteriorSeparators' fixtureMapSeqVal 2 13 := by
  intro h
  exact mapGrammarFacts'_bracketVal_false
    (h 2 13 (Nat.le_refl 2) (by omega) (Nat.le_refl 13) mapTypedInterior_bracketVal)

-- Axiom audit — the carrier inhabitation and the boundary-survival probe lean only on core; the
-- ASSEMBLE non-vacuity checks also pull in `Classical.choice` through the rebase's
-- `flowBracketBalance_compose`.
/-- info: 'MapCarrierRobustInhabitation.mapInteriorSeparators'_unit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapInteriorSeparators'_unit

/-- info: 'MapCarrierRobustInhabitation.mapInteriorSeparators'_of_enclosing_provider_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mapInteriorSeparators'_of_enclosing_provider_unit

/-- info: 'MapCarrierRobustInhabitation.mapInteriorSeparators'_via_provider_of_located_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mapInteriorSeparators'_via_provider_of_located_unit

/-- info: 'MapCarrierRobustInhabitation.mapInteriorSeparators'_via_dispatcher_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mapInteriorSeparators'_via_dispatcher_unit

/-- info: 'MapCarrierRobustInhabitation.mapGrammarFacts'_degenerate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapGrammarFacts'_degenerate

/-- info: 'MapCarrierRobustInhabitation.mapGrammarFacts_complete_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapGrammarFacts_complete_window

/-- info: 'MapCarrierRobustInhabitation.mapGrammarFacts'_complete_window_fires' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapGrammarFacts'_complete_window_fires

/-- info: 'MapCarrierRobustInhabitation.mapGrammarFacts_strict_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapGrammarFacts_strict_roundtrip

/-- info: 'MapCarrierRobustInhabitation.mapTypedInterior_bracketVal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapTypedInterior_bracketVal

/-- info: 'MapCarrierRobustInhabitation.mapGrammarFacts'_bracketVal_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapGrammarFacts'_bracketVal_false

/-- info: 'MapCarrierRobustInhabitation.mapInteriorSeparators'_bracketVal_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapInteriorSeparators'_bracketVal_false

end MapCarrierRobustInhabitation
