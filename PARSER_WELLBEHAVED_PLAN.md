# ParserWellBehaved.lean — Remaining Work

## Status

**26 declaration-level `sorry`s remain** (12 zero cases + 6 step cases + 8
higher-level witnesses). The mutual-induction theorem has been refactored from
one large conjunction proof into 12 separate `_mono_step` theorems plus 12
`_mono_zero` theorems, with `parser_fuel_mono_succ` composing them via
induction — each remaining proof obligation is now a focused theorem that can
be worked on independently.

## Progress

- [x] Easy/medium balance-preservation sorries (5 eliminated, pre-2026-04-17).
- [x] **Step 1 scaffolding**: offset-all form `X (fuel+1) → X (fuel+2)`,
      outer induction on `fuel`, `content_mono` helper, wrapper extractors.
- [x] **Step 1, Part 1 succ** (parseNode) — 2026-04-19.
- [x] **Step 1, Part 2 succ** (parseFlowSequence) — 2026-04-19.
- [x] **Refactor**: split `parser_fuel_mono_succ` into 12 `_mono_step` + 12
      `_mono_zero` theorems + a composed main theorem — 2026-04-19.

## Plan

### Step 1 — Finish the 12 `_mono_step` + 12 `_mono_zero` theorems

Each parser/loop has two standalone theorems:
- `xxx_mono_zero : Xxx_succ 0` — proves `X 1 → X 2`.
- `xxx_mono_step (n) (ih_deps…) : Xxx_succ (n + 1)` — proves `(n+2) → (n+3)`
  given the IHs at fuel `n` for parsers it calls.

`parser_fuel_mono_succ` at
[ParserWellBehaved.lean:4875](L4YAML/Proofs/ParserWellBehaved.lean:4875)
composes these via `induction fuel with | zero => ⟨…zero lemmas…⟩ | succ n ih => ⟨…step lemmas…⟩`.
The wrappers `parseNode_fuel_mono_succ` and `parseSinglePairMapping_fuel_mono_succ`
below it project the relevant conjunct.

**Succ cases** (`xxx_mono_step`):

| # | Parser/loop                        | Deps                   | Location | Status |
| - | ---------------------------------- | ---------------------- | -------- | ------ |
| 1 | `parseNode`                        | ih_fs/fm/bs/bm/ibs     | :4626    | ✅     |
| 2 | `parseFlowSequence`                | ih_fsl                 | :4703    | ✅     |
| 3 | `parseFlowMapping`                 | ih_fml                 | :4719    | ✅     |
| 4 | `parseBlockSequence`               | ih_bsl                 | :4735    | ✅     |
| 5 | `parseBlockMapping`                | ih_bml                 | :4751    | ✅     |
| 6 | `parseImplicitBlockSequence`       | ih_ibsl                | :4769    | ✅     |
| 7 | `parseSinglePairMapping`           | ih_pn                  | :4797    | 🚧     |
| 8 | `parseFlowSequenceLoop`            | ih_pn, ih_sp           | :4845    | ⏳     |
| 9 | `parseFlowMappingLoop`             | ih_pn, ih_sp           | :4852    | ⏳     |
| 10| `parseBlockSequenceLoop`           | ih_pn                  | :4858    | ⏳     |
| 11| `parseBlockMappingLoop`            | ih_pn                  | :4863    | ⏳     |
| 12| `parseImplicitBlockSequenceLoop`   | ih_pn                  | :4868    | ⏳     |

**Zero cases** (`xxx_mono_zero`): 12 stubs at
[:4568-4601](L4YAML/Proofs/ParserWellBehaved.lean:4568). Each ~5-30 lines,
mirroring the succ case but with vacuity arguments at internal fuel=0.

Line-size estimates (succ cases): Parts 3-6 ≈ 12 lines each (done),
Part 7 ≈ 30 lines body (helpers done, wiring blocked),
Parts 8-12 ≈ 40-60 lines each (templates based on `parseFlowSequenceLoop_fuel_mono_succ`
below in the file).

**Legend**: ✅ proved · ⏳ not started · 🚧 attempted, blocked.

**Part 7 blocker** (updated 2026-04-19): `parseSinglePairMapping_mono_step` at
[:4797](L4YAML/Proofs/ParserWellBehaved.lean:4797) has helper lemmas
`key_step` and `val_step` **proven and checked in** (~40 lines as local `have`
statements). Both use `rcases` on `ps.peek?`, `cases tok`, `exact h` for
empty-token branches, `exact ih_pn _ _ _ h` for parseNode branches; `rw [h_peek]
at h` is load-bearing since `rcases` substitutes in the goal but not in hyps.

Remaining block is wiring the helpers into the do-block body. Two approaches
tried and rejected:

1. **`simp only [bind, Except.bind, emptyNode] + split at h_ok`**: simp merges
   the KEY_MATCH's inner `match ps.peek? with …` with the outer `Except.bind`
   via iota, producing a 4-arm top-level match. `split at h_ok` greedily also
   splits the `if consumed` inside each arm, yielding compound case names like
   `h_1.isTrue`. `first | alt_parseNode | alt_empty` enumeration mis-aligns.
2. **`generalize h_km : KEY_MATCH = km_in at h_ok` + `cases km_in`**: the clean
   alternative, but the literal KEY_MATCH term in h_ok has a shadowing
   `let ps := ps.advance`, so the generalize target needs zeta-reduction first.
   VAL_BIND has 8+ repetitions of `{ps_k with currentPath := …}.tryConsume`,
   making the second generalize target fragile.

**Concrete next steps** for a subsequent session with interactive Lean:
- After `intro ps kv h_ok`, add `unfold parseSinglePairMapping at h_ok ⊢;
  dsimp only at h_ok ⊢` to expose the body and zeta-reduce the `let ps :=
  ps.advance` shadow.
- Use `set ps_adv := ps.advance` and `set ps_tc := (…).tryConsume YamlToken.value`
  to give intermediate states short names.
- Then `generalize h_km : KEY_MATCH = km_in at h_ok` and `cases km_in`, handling
  the `.error`/`.ok` branches with `key_step` and rewrites.
- Repeat for VAL_BIND, with `by_cases` on `consumed = true` before the second
  `generalize` so the `if` collapses.

### Step 2 — Loop-level fuel monotonicity lemmas

- [ ] `parseFlowSequenceLoop_fuel_mono_succ`
      ([:4936](L4YAML/Proofs/ParserWellBehaved.lean:4936)):
      can now be written as a direct wrapper around `parseFlowSequenceLoop_mono_step`
      (Part 8 above), with a shim for the `fuel=0` edge case. ~10 lines.
- [ ] `parseFlowSequenceLoop_fuel_mono`
      ([:5024](L4YAML/Proofs/ParserWellBehaved.lean:5024)): generalize to
      any `fuel ≤ fuel'` by induction on `fuel' - fuel` applying `_succ`
      repeatedly. ~10 lines.

### Step 3 — `parseNodeProperties` forIn helper

- [ ] Single lemma `parseNodeProperties_break_on_non_tag`: when
      `ps.peek?` is not `.anchor _` or `.tag _ _`, the internal `for`-loop
      breaks immediately, returning `({}, ps)` unchanged. Closes 3 sorries
      in `parseNode_flowSeqStart_in_seq` at lines
      [:6450, :6460, :6465](L4YAML/Proofs/ParserWellBehaved.lean:6450).
      ~20-30 lines.

### Step 4 — `parseExplicitKey` helpers

- [ ] `parseExplicitKey_flowSeq`
      ([:5472](L4YAML/Proofs/ParserWellBehaved.lean:5472)): `?[...]` succeeds
      and advances past `]`. ~40-60 lines; follow template from
      `parseNode_flowSeqStart_in_seq`.
- [ ] `parseExplicitKey_flowMap`
      ([:5507](L4YAML/Proofs/ParserWellBehaved.lean:5507)): symmetric
      `?{...}` variant.

### Step 5 — Main witness theorems

- [ ] `parseFlowMappingValue_ok` remaining cases: flowSeqStart value,
      flowMapStart value (2 sorries). Depends on Step 4.
      ~60 lines each.
- [ ] `parseNode_flowMapStart_in_seq`
      ([:6234](L4YAML/Proofs/ParserWellBehaved.lean:6234)): copy
      `parseNode_flowSeqStart_in_seq` and adapt to Map-specific lemmas.
      ~80-100 lines.
- [ ] `parseEntry_in_flowMap`
      ([:6762](L4YAML/Proofs/ParserWellBehaved.lean:6762)): three key-shape
      subcases (scalar key, `[…]` key, `{…}` key), each chains through
      Step 4 helpers + `parseFlowMappingValue_ok`. ~60-80 lines.

## Reference

- **Canonical bracket-case template**: `parseNode_flowSeqStart_in_seq`
  ([:6050-:6365](L4YAML/Proofs/ParserWellBehaved.lean:6050)) — 315 lines
  covering all 7 output properties. Use as the starting point for Step 5.
- **Fuel budget**: parser proofs typically require `fuel ≥ 4*N + 6` where
  `N = tokens.size`; inner loops use `4*N + 4`; `parser_fuel_mono_succ`
  bridges the gap.
- **Bracket balance identity**: `[pos, pos+1) = +1`, `[pos+1, j) = 0`
  (from IH), `[j, j+1) = -1`; sum is 0.
- **State-field preservation obligations** in every main witness:
  `tokens` preserved, `trackPositions` preserved, `pos` advanced within
  bounds, `peek?` postcondition holds.
