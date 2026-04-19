# ParserWellBehaved.lean — Remaining Work

## Status

**8 top-level declarations still use `sorry`.** We follow one plan: finish the
infrastructure theorem bottom-up, derive the extractors, then discharge the
higher-level witnesses that depend on them. Earlier versions of this document
discussed alternative strategies (A/B/C) and tier-based groupings; both have
been retired in favor of the single linear sequence below.

## Progress

- [x] Easy/medium balance-preservation sorries (5 eliminated, pre-2026-04-17).
- [x] **Step 1 scaffolding**: `parser_fuel_mono_succ` restated in "offset-all"
      form (`X (fuel+1) → X (fuel+2)`), outer induction on `fuel`,
      `content_mono` helper, wrapper extractors. See
      [ParserWellBehaved.lean:4485](L4YAML/Proofs/ParserWellBehaved.lean:4485).
- [x] **Step 1, Part 1 succ** (parseNode) — 2026-04-19.
- [x] **Step 1, Part 2 succ** (parseFlowSequence) — 2026-04-19.

## Plan

### Step 1 — Finish `parser_fuel_mono_succ` (the main mutual-induction theorem)

One theorem, 12 conjuncts ("parts"), one per parser/loop in the mutual graph.
Each part claims `X ps (fuel+1) = .ok y → X ps (fuel+2) = .ok y`. The proof is
by outer induction on `fuel`: each succ case uses the IH at `fuel` to discharge
the internal calls (which occur at internal fuel `n+1 → n+2`). Location:
[ParserWellBehaved.lean:4485](L4YAML/Proofs/ParserWellBehaved.lean:4485).

**Succ cases** (fuel = n+1, prove `(n+2) → (n+3)`):

| # | Parser/loop                        | Pattern                                     | Status |
| - | ---------------------------------- | ------------------------------------------- | ------ |
| 1 | `parseNode`                        | alias OR bind chain w/ `content_mono`       | ✅     |
| 2 | `parseFlowSequence`                | advance + loop + peek? tail; use `ih_fsl`   | ✅     |
| 3 | `parseFlowMapping`                 | same template as Part 2; use `ih_fml`       | ✅     |
| 4 | `parseBlockSequence`               | same template as Part 2; use `ih_bsl`       | ✅     |
| 5 | `parseBlockMapping`                | same template as Part 2; use `ih_bml`       | ✅     |
| 6 | `parseImplicitBlockSequence`       | same template as Part 2; use `ih_ibsl`      | ✅     |
| 7 | `parseSinglePairMapping`           | two `parseNode` calls; use Part 1 IH        | 🚧     |
| 8 | `parseFlowSequenceLoop`            | full peek? split; use Parts 1 & 7 IH        | ⏳     |
| 9 | `parseFlowMappingLoop`             | full peek? split; use Parts 1 & 7 IH        | ⏳     |
| 10| `parseBlockSequenceLoop`           | full peek? split; use Part 1 IH             | ⏳     |
| 11| `parseBlockMappingLoop`            | full peek? split; use Part 1 IH             | ⏳     |
| 12| `parseImplicitBlockSequenceLoop`   | full peek? split; use Part 1 IH             | ⏳     |

**Base cases** (outer fuel = 0, prove `X 1 → X 2`): 12 stubs at lines
[:4544-4555](L4YAML/Proofs/ParserWellBehaved.lean:4544). Non-vacuous but
smaller than the succ cases; each ~5-30 lines depending on the parser's
fuel=1 behavior.

Line-size estimates (succ cases): Parts 3-6 ≈ 12 lines each (template),
Part 7 ≈ 30 lines, Parts 8-12 ≈ 40-60 lines each.

**Legend**: ✅ proved · ⏳ not started · 🚧 attempted, blocked.

**Part 7 blocker**: the body has two parseNode calls inside nested matches
(key-dispatch + value-dispatch) plus an `if consumed` around the value match.
Split-based destructuring runs into fragile anonymous-name ordering and
`rename_i` picks up hypotheses in an unexpected order. Helper lemmas
`key_shift` and `value_shift` (both straightforward: rcases on ps.peek?,
empty-branches use `exact h`, parseNode-branches apply `ih_pn`) are the
right abstraction, but wiring them through the main proof needs either
(a) explicit `case _ =>` labels instead of `rename_i`, or (b) `obtain`
patterns directly on split output.  Likely tractable with interactive
feedback on which hypotheses Lean introduces at each step.

### Step 2 — Loop-level fuel monotonicity lemmas

- [ ] `parseFlowSequenceLoop_fuel_mono_succ`
      ([:4700](L4YAML/Proofs/ParserWellBehaved.lean:4700)):
      extract from `parser_fuel_mono_succ` Part 8. ~10 lines with a shim for
      the `fuel=0` edge case.
- [ ] `parseFlowSequenceLoop_fuel_mono`
      ([:4809](L4YAML/Proofs/ParserWellBehaved.lean:4809)): generalize to
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
