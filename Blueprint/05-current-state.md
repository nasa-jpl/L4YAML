# Current state (2026-04-21)

An honest accounting of where L4YAML is, not what we wish it were.

## Sorry audit

Grep of `L4YAML/Proofs/*.lean` for the string `sorry` yields **113
matches across 35 files**. Some of those are in comments (e.g.
"0 sorry" claims, historical notes); the actual count of *active*
`sorry` tactics by file:

| File | `sorry` count | Role |
| ---- | ------------- | ---- |
| `StreamAccum.lean` | 28 | Grammar-derivation composition (Group 7.1) |
| `ParserWellBehaved.lean` | 28 | Fuel monotonicity — see "Deletion candidates" below |
| `EmitterScannability.lean` | 15 | Emitter round-trip closure (Group 6.8–6.9) |
| `ScalarProduction.lean` | 5 | Scalar grammar derivation (Group 7.3) |
| `ScannerCorrectness.lean` | 3 | Scanner validity (Group 2.1) |
| `DocumentProduction.lean` | 3 | Document grammar derivation (Group 7.3) |
| `ScannerPlainScalarValid.lean` | 2 | Plain-scalar validity |
| `PreprocessProduction.lean` | 2 | Preprocessing grammar derivation |
| *(~18 files × 1 each)* | 18 | various 1-offs |
| **Total (grep hits)** | **113** | approximate active-sorry ≈ **90–100** |

This contradicts `doc/Doc/L4YAML/Overview.lean:41`:

> Axioms / `sorry` / `partial def` → Zero / Zero / Zero

**Action item**: reconcile the Verso manual. Either (a) the metric
is meant for a frozen historical milestone (say the one
`lean4-yaml-verified` was released at), (b) it refers to the
non-Proofs/ portion only, or (c) it's out of date. Clarify which
and state it accurately.

## Deletion candidates (high confidence)

These ship cost but contribute nothing traceable to a capstone.
Recommend deletion pending one-more-look.

### Group A — Fuel-monotonicity scaffolding with 0 external callers

| Name | Location | LoC | Sorry? |
| ---- | -------- | --- | ------ |
| `parseNode_fuel_mono_succ` | [`ParserWellBehaved.lean:5477`](../L4YAML/Proofs/ParserWellBehaved.lean#L5477) | ~10 | no |
| `parseSinglePairMapping_fuel_mono_succ` | [`ParserWellBehaved.lean:5487`](../L4YAML/Proofs/ParserWellBehaved.lean#L5487) | ~10 | no |

**Evidence**: `grep -rn 'parseNode_fuel_mono_succ'` and
`grep -rn 'parseSinglePairMapping_fuel_mono_succ'` each return **only
the theorem's own definition and doc comments**. Zero call sites in
the entire 66,000-line project.

### Group B — Parts 16–24 of Step 1 (known-unsound for some; unvalidated for rest)

`ParseBlockSequence_succ 0`, `ParseBlockMapping_succ 0`,
`ParseImplicitBlockSequence_succ 0`, and their three loop
counterparts are **unprovable as stated**. The outer parsers have no
error branch in their `fuel + 1` body (`| _ => ps` defaults), so the
`fuel = 1 → fuel = 2` hypothesis always holds; at fuel = 2 the loop
can push `emptyNode` or call `parseNode 0` which errors — producing
a different `val` or a `.error`. See previous conversation for the
concrete counterexample (`ps.advance.peek? = some .blockEntry`).

| Part | Theorem | Line | Status |
| ---- | ------- | ---- | ------ |
| 16 | `parseBlockSequence_mono_zero` | :4672 | ❓ unprovable — delete |
| 17 | `parseBlockMapping_mono_zero` | :4675 | ❓ unprovable — delete |
| 18 | `parseImplicitBlockSequence_mono_zero` | :4678 | ❓ unprovable — delete |
| 19 | `parseSinglePairMapping_mono_zero` | :4681 | ⏳ may be provable (error-gated body) |
| 20 | `parseFlowSequenceLoop_mono_zero` | :4684 | ⏳ may be provable |
| 21 | `parseFlowMappingLoop_mono_zero` | :4687 | ⏳ may be provable |
| 22 | `parseBlockSequenceLoop_mono_zero` | :4690 | ❓ unprovable — same pattern as Part 16 |
| 23 | `parseBlockMappingLoop_mono_zero` | :4693 | ❓ unprovable — same pattern |
| 24 | `parseImplicitBlockSequenceLoop_mono_zero` | :4696 | ❓ unprovable — same pattern |

### Group C — The enclosing `parser_fuel_mono_succ`

Because Group B contains unprovable parts, `parser_fuel_mono_succ`
**cannot be proved in its current form** (the `zero` case projects
Parts 13–24 in conjunction). Either:

- **Option 1 — Restructure**: change the outer induction base from
  `zero ↦ ParseX_succ 0` to `zero ↦ ParseX_succ 1` (i.e. base case
  proves `fuel = 2 → fuel = 3`). Parts 13–15 (already proved) would
  be dropped; Parts 16–24 become unnecessary at the zero-case
  level; the base case becomes the current step-case applied at
  `n = 0`, which still needs the loop IHs — but those exist via
  the step lemmas themselves. **This is my recommendation.**
- **Option 2 — Delete entire `parser_fuel_mono_succ`** and
  prove `parseFlowSequenceLoop_fuel_mono` (the one actually-used
  consequence, 1 callsite) directly as a specialized lemma. Saves
  ~1,000 LoC of infrastructure.

Either way, the 28 `sorry`s in `ParserWellBehaved.lean` are
candidates for elimination-by-deletion rather than
elimination-by-proof.

### Group D — Parts 14–15 recently proved, wasted effort

Parts 14 (`parseFlowSequence_mono_zero`) and 15
(`parseFlowMapping_mono_zero`), proved 2026-04-21 (~24 LoC each),
will be dropped if Option 1 or 2 is taken. Noting for transparency.

## Gaps (capstones that need work)

Priority-ordered by user-facing impact:

### Priority 1 — The universal round-trip (Capstone 6.10)

Currently **docstring-only** in
[`Completeness.lean:90-105`](../L4YAML/Proofs/Completeness.lean) and
[`RoundTrip.lean:50-62`](../L4YAML/Proofs/RoundTrip.lean). This is
the most visible missing guarantee and the last step of the
emit→scan→parse→content-eq cycle.

```lean
theorem emit_roundtrip_universal :
    ∀ v : YamlValue, Grammable v false →
      ∃ docs, parseYaml (emit v) = .ok docs ∧
              docs.size = 1 ∧
              contentEq v docs[0]!.value = true := sorry
```

**Blockers**: Completion of Capstone 6.8 (`emit_roundtrip_content_eq`
in [`EmitterScannability.lean`](../L4YAML/Proofs/EmitterScannability.lean),
15 sorries).

### Priority 2 — Grammar-derivation composition (Capstone 7.1)

[`StreamAccum.lean`](../L4YAML/Proofs/StreamAccum.lean) has 28
sorries clustering at 5 architectural boundaries:
`dispatchBlockEntry_full_prod`, `collectPlainScalarLoop_prod`,
`h_closable` construction in `PendingNode`, BOM preprocessing at
`col ≠ 0`, and plain-scalar `_prod`.

### Priority 3 — Scanner correctness closure (Capstone 2.1)

3 sorries in `ScannerCorrectness.lean`. Low count, high value —
closes the scanner side.

### Priority 4 — Value semantics closure (Capstone 5.1)

1 sorry in `Soundness.lean` for `toYamlValue_correct`.

### Priority 5 — Emitter round-trip (Capstones 6.8–6.9)

15 sorries in `EmitterScannability.lean`. Blocks Priority 1.

## Adversarial-instantiation gaps

Per [`04-capstones.md`](04-capstones.md), these capstones have no
adversarial-instantiation coverage:

- Group 4 (end-to-end): `parse_produces_valid_*` family.
- Group 5 (value semantics): `toYamlValue_correct`,
  `nodeToValue_total`, `nodeToValue_deterministic`.
- Group 6.10 (universal round-trip): natural, since it's only
  docstring-stated.
- Any of the 24 `parser_fuel_mono_succ` parts: **this is the gap
  that let Part 16's unsoundness through**.

**Recommended**: before proving or re-stating any of the above,
add an adversarial-instantiation suite that would refute a false
version. See [`06-discipline.md`](06-discipline.md).

## Discrepancies to reconcile

1. **Overview.lean metric**: "Zero sorry". See above.
2. **Architecture.lean scanner split**: mentions
   `Scanner/Whitespace.lean`, `Scanner/Scalar.lean`, etc. — these
   **do not exist**. Either remove from the doc or create them (per
   [`03-code-organization.md`](03-code-organization.md) Phase 2).
3. **Overview.lean theorem count**: "2,309 theorems". Last verified?
   If approximate, mark as such.
4. **Plan docs at repo root** (`PARSER_WELLBEHAVED_PLAN.md`,
   `EMITTER_SCANNABILITY_PLAN.md`, etc.): these are tactical plans.
   Once the blueprint is active, each plan should cite the
   capstone(s) it feeds and be marked "in service of capstone X.Y."
   Plans that don't feed a capstone are either noise or signal a
   missing capstone.

## Immediate next steps (proposed)

1. **Stop Part 16**; close [`PARSER_WELLBEHAVED_PLAN.md`](../PARSER_WELLBEHAVED_PLAN.md)
   with an audit-note ending and point to this blueprint.
2. **Delete Groups A and C** from `ParserWellBehaved.lean` (Option 2
   above). Net ~1,000 LoC removed, 28 sorries removed.
3. **Prove a specialized `parseFlowSequenceLoop_fuel_mono`** at the
   single needed call site — direct proof, no generic machinery.
4. **Reconcile Overview.lean**: update the "Zero sorry" claim to
   reflect reality.
5. **Adopt [`06-discipline.md`](06-discipline.md)** as the rule for
   any new theorem.

Steps 1–3 reduce ParserWellBehaved.lean from 8,045 lines to roughly
6,500–7,000 lines and eliminate 28 sorries without proving anything
new. That's the cheapest possible progress.
