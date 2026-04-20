# ParserWellBehaved.lean — Remaining Work

## Status

**20 declaration-level `sorry`s remain** (12 zero cases +
8 higher-level witnesses). The mutual-induction theorem has been refactored
from one large conjunction proof into 12 separate `_mono_step` theorems plus
12 `_mono_zero` theorems, with `parser_fuel_mono_succ` composing them via
induction — each remaining proof obligation is now a focused theorem that
can be worked on independently.

## Progress

- [x] Easy/medium balance-preservation sorries (5 eliminated, pre-2026-04-17).
- [x] **Step 1 scaffolding**: offset-all form `X (fuel+1) → X (fuel+2)`,
      outer induction on `fuel`, `content_mono` helper, wrapper extractors.
- [x] **Step 1, Part 1 succ** (parseNode) — 2026-04-19.
- [x] **Step 1, Part 2 succ** (parseFlowSequence) — 2026-04-19.
- [x] **Refactor**: split `parser_fuel_mono_succ` into 12 `_mono_step` + 12
      `_mono_zero` theorems + a composed main theorem — 2026-04-19.
- [x] **Step 1, Part 7 succ** (parseSinglePairMapping) — 2026-04-19.
- [x] **Step 1, Part 8 succ** (parseFlowSequenceLoop) — 2026-04-19.
- [x] **Step 1, Part 9 succ** (parseFlowMappingLoop) — 2026-04-19.
- [x] **Step 1, Part 10 succ** (parseBlockSequenceLoop) — 2026-04-19.
- [x] **Step 1, Part 11 succ** (parseBlockMappingLoop) — 2026-04-19. Main
      theorem fully proved; helper `handleBlockMappingKeyEntry_mono_step`
      lifted to top-level and also proved (2026-04-20) via
      `generalize peek? + rcases + simp [if_true, Bool.false_eq_true,
      if_false]`. Audited via `Tests/AdversarialInstantiation.lean`
      Priority 7.
- [x] **Step 1, Part 12 succ** (parseImplicitBlockSequenceLoop) —
      2026-04-20. Structurally analogous to Part 10 with 4 empty-entry
      cases (blockEntry/blockEnd/key/none) instead of 3. Signature updated
      to take `ih_ibsl` in addition to `ih_pn`; call site in
      `parser_fuel_mono_succ` updated.

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
| 7 | `parseSinglePairMapping`           | ih_pn                  | :4797    | ✅     |
| 8 | `parseFlowSequenceLoop`            | ih_pn, ih_sp, ih_fsl   | :4909    | ✅     |
| 9 | `parseFlowMappingLoop`             | ih_pn, ih_fml          | :4970    | ✅     |
| 10| `parseBlockSequenceLoop`           | ih_pn, ih_bsl          | :5107    | ✅     |
| 11| `parseBlockMappingLoop`            | ih_pn, ih_bml          | :5218    | ✅     |
| 12| `parseImplicitBlockSequenceLoop`   | ih_pn, ih_ibsl         | :5303    | ✅     |

Part 11 main theorem proved inline (2026-04-19) with helpers `h_bmv` and
`h_bmve`; the third helper `handleBlockMappingKeyEntry_mono_step` at :5144
was lifted to a top-level theorem and proved on 2026-04-20 via
`generalize peek? + rcases + simp [if_true, Bool.false_eq_true, if_false]`.
The proof uses the peek-substituted match iota-reduce to a literal bool,
then the `if` iota-reduces. Empty-key paths (false) bridge via `h_bmv`;
parseNode paths (true) bridge via `ih_pn` then `h_bmv`.

**Zero cases** (`xxx_mono_zero`): 12 stubs at
[:4568-4601](L4YAML/Proofs/ParserWellBehaved.lean:4568). Each ~5-30 lines,
mirroring the succ case but with vacuity arguments at internal fuel=0.

Line-size estimates (succ cases): Parts 3-6 ≈ 12 lines each (done),
Part 7 ≈ 60 lines body (done),
Part 8 ≈ 60 lines body (done),
Part 9 ≈ 100 lines body + 2 inline helpers (done),
Part 10 ≈ 25 lines body (done — confirmed simpler with no helpers needed),
Part 11 ≈ 90 lines body + 2 inline helpers + 1 lifted top-level helper
(done 2026-04-19 for main/inline, 2026-04-20 for `handleBlockMappingKeyEntry_mono_step`),
Part 12 ≈ 30-60 lines.

**Dependency note**: Each loop's `_mono_step` also needs its own self-IH
(e.g. Part 8 needs `ih_fsl`, Part 9 needs `ih_fml`, etc.) because the loop's
tail-recursive call at the inner fuel level needs monotonicity bridging. The
plan table above was updated on 2026-04-19 to reflect this.

**Legend**: ✅ proved · ⏳ not started · 🚧 attempted, blocked.

**Part 7 proof approach** (landed 2026-04-19): the winning strategy used
interactive `trace_state` + `sorry` checkpoints to see the exact form of
`h_ok` / goal after `unfold + dsimp`:

1. `unfold parseSinglePairMapping at h_ok ⊢; dsimp only at h_ok ⊢` reduces the
   outer fuel match and zeta-reduces the `let ps := ps.advance` shadow, leaving
   both h_ok and goal as a single `match ps.advance.peek? with ...` where the
   four-arm body is a `do let y ← KEY_RES; <VAL body using y>`.
2. `generalize h_peek_k : ps.advance.peek? = p_k at h_ok ⊢; cases p_k` splits
   into 24 peek? arms (1 `none` + 23 `some tok_k`), aligning h_ok and goal per
   arm.
3. Each arm is either an *empty* KEY arm (peek? ∈ {.value, .flowEntry,
   .flowSequenceEnd}) where KEY_RES = `.ok (emptyNode, ps.advance)`, or a
   *default* KEY arm where KEY_RES = `parseNode ps.advance fuel`.
4. For empty arms: `simp only [bind, Except.bind, emptyNode]` unfolds
   `emptyNode` so the `match emptyNode with | .scalar s => s.content | _ => "0"`
   in the `currentPath` reduces to `""`. Then `split at h_ok` peels the outer
   `if consumed then ... else ...`.
5. For default arms: `simp only [bind, Except.bind]` (no emptyNode), then
   `split at h_ok` on the `match parseNode … with | .error | .ok`, using
   `cases h_ok` in the error branch and `have h_pn' := ih_pn _ _ _ h_pn` +
   `rw [h_pn']` in the .ok branch. An extra `split at h_ok` is needed before
   the outer `if` because the `match v.fst with | .scalar s => s.content | _ =>
   "0"` in the record update gets split first.
6. In both cases, the inner VAL match (on `ps_tc.peek?`) follows the same
   pattern: direct `exact h_ok` for flowEntry / flowSequenceEnd / none arms
   (h_ok and goal are identical since no fuel is involved), and `split at h_ok
   + cases h_ok for .error + ih_pn bridge for .ok` in the default arm.

The `key_step` / `val_step` helpers drafted in earlier attempts turned out to
be unnecessary — `ih_pn` applied directly via `rw` handles every fuel shift.

**Part 9 proof approach** (landed 2026-04-19): mirrors Part 8 but the inner
key parser is `parseExplicitKey` (not `parseSinglePairMapping`) and the value
parser is `parseFlowMappingValue`. Both are non-recursive helpers that call
`parseNode`, so no new mutual IH is needed, but inline `have` lemmas are
required to bridge fuel `(n+1) → (n+2)` for each:

- `h_ek`: 4-arm split on `ps.peek?` (3 empty arms `exact h`, 1 default arm
  `exact ih_pn _ _ _ h`). ~10 lines.
- `h_fmv`: mirrors the if-consumed + inner-peek pattern from
  `parseFlowMappingValue`'s body; 4 peek arms (3 empty + 1 `parseNode`) + the
  `if consumed then/else` branch. ~20 lines.

**Destructuring quirk**: after `split at h_ok` on the key-parser `match`,
Lean leaves the introduced result variable as a pair `v : YamlValue ×
ParseState` without auto-destructuring. Subsequent `rw [h_ek']` / `rw
[h_fmv']` generates `(v.fst, v.snd)` terms that don't syntactically match
the goal's destructured form. Fix: `obtain ⟨key, ps_mid⟩ := v` immediately
after `rename_i`, which forces normalization.

**Part 8 proof approach** (landed 2026-04-19): Key insight — `split at h_ok`
on a `match` expression *auto-aligns the goal* when both h_ok and goal share
the same scrutinee (like `ps.peek?`), because split generalizes the scrutinee
to a common variable before case-splitting. But `split at h_ok` on an `if`
does *not* auto-align the goal (propositions don't iota-reduce from a
hypothesis alone), so the `if items_acc.size > 0` condition needs `split at
h_ok <;> split` (4 cross-cases, 2 closed by `omega` for items-size mismatch).
Inner peek matches use bare `split at h_ok`. For `parseSinglePairMapping` /
`parseNode` sub-calls, the pattern is `split at h_ok; cases h_ok / rename_i v
h_inner; have h' := ih_... _ _ h_inner; rw [h']; exact ih_fsl ...`.

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
