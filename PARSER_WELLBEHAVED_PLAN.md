# ParserWellBehaved.lean — Remaining Work

## Status

**22 `sorry`s across 17 declarations remain** after deleting the
unsound, unused `parseFlowSequenceLoop_fuel_mono_succ` (see 2026-04-20
audit note below). Breakdown:

- 10 `_mono_zero` stubs (step 1, parts 15–24).
- 1 `parseFlowSequenceLoop_fuel_mono` general-form sorry (step 2).
- 3 sorries inside `parseNode_flowSeqStart_in_seq`: needs
  `parseNodeProperties_skip` application (step 3).
- 2 `parseExplicitKey_flowSeq` / `parseExplicitKey_flowMap` sorries
  (step 4).
- 1 remaining `parseFlowMappingValue_ok` sorry, 1 sorry inside
  `parseEntry_in_flowMap`, 1 sorry inside `parseNode_flowMapStart_in_seq`
  (step 5).
- 3 "insufficient fuel" sorries in `flow_parser_ok_of_structure`
  (step 6).

The mutual-induction theorem has been refactored from one large conjunction
proof into 12 separate `_mono_step` theorems plus 12 `_mono_zero` theorems,
with `parser_fuel_mono_succ` composing them via induction — each remaining
proof obligation is now a focused theorem that can be worked on
independently.

## Audit notes

- **2026-04-20** — deleted `parseFlowSequenceLoop_fuel_mono_succ` (was at
  former line :5405). Its `fuel=0` case is *unprovable as stated*:
  `parseFlowSequenceLoop ps 0 items_acc` unconditionally returns
  `.ok (items_acc, ps)` (structural base case, not a real parse), but at
  `fuel=1` with e.g. `items_acc = #[]` and `ps.peek? = some .key` the loop
  errors via `parseSinglePairMapping ps 0`. Theorem was also unused
  outside the plan and a stale VERSION-0.4.7 historical note.
- **Outstanding audit**: every top-level theorem/lemma in
  `ParserWellBehaved.lean` with no inbound references elsewhere in the
  project should be reviewed before deletion. Track these in an "Unused /
  candidate for review" section below as they are discovered.

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
- [x] **Step 1, Part 13 zero** (parseNode_mono_zero) — 2026-04-21. Not
      purely vacuous: `parseNode ps 1 = .ok` succeeds on alias/scalar/empty
      paths, so the proof mirrors `parseNode_mono_step` with an auxiliary
      `content_zero : parseNodeContent ps_c 0 → parseNodeContent ps_c 1`.
      Sub-parser arms (block/flow sequence/mapping, implicit block
      sequence) are discharged by `simp [parseXxx] at h` using the fuel=0
      `.error` return. ~70 lines.
- [x] **Step 1, Part 14 zero** (parseFlowSequence_mono_zero) — 2026-04-21.
      Not vacuous: `parseFlowSequence ps 1 = .ok` succeeds when
      `ps.advance.peek? = some .flowSequenceEnd`, because
      `parseFlowSequenceLoop ps.advance 0 #[]` unconditionally returns
      `.ok (#[], ps.advance)` (structural base case) and the outer match
      then hits the `flowSequenceEnd` arm. Proof strategy: establish
      `h_loop_zero` (loop at fuel=0 returns empty) via `unfold; rfl`,
      substitute into h_ok via `simp only [bind, Except.bind, h_loop_zero]`
      to iota-reduce, split on peek, then establish `h_loop_one` (loop at
      fuel=1 returns same empty when peek=flowSequenceEnd) via
      `unfold; simp [h_peek]`, and bridge. ~12 lines.

## Plan

### Step 1 — Finish the 12 `_mono_step` + 12 `_mono_zero` theorems

Each parser/loop has two standalone theorems:
- `xxx_mono_zero : Xxx_succ 0` — proves `X 1 → X 2`.
- `xxx_mono_step (n) (ih_deps…) : Xxx_succ (n + 1)` — proves `(n+2) → (n+3)`
  given the IHs at fuel `n` for parsers it calls.

`parser_fuel_mono_succ` at
[ParserWellBehaved.lean:5346](L4YAML/Proofs/ParserWellBehaved.lean:5346)
composes these via `induction fuel with | zero => ⟨…zero lemmas…⟩ | succ n ih => ⟨…step lemmas…⟩`.
The wrappers `parseNode_fuel_mono_succ`
([:5382](L4YAML/Proofs/ParserWellBehaved.lean:5382)) and
`parseSinglePairMapping_fuel_mono_succ`
([:5392](L4YAML/Proofs/ParserWellBehaved.lean:5392)) below it project the
relevant conjunct.

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

**Zero cases** (`xxx_mono_zero`, parts 13–24): 12 stubs at
[:4568-4602](L4YAML/Proofs/ParserWellBehaved.lean:4568). Each ~5-30 lines,
mirroring the succ case but with vacuity arguments at internal fuel=0.

| #  | Parser/loop                        | Body style  | Location | Status |
| -- | ---------------------------------- | ----------- | -------- | ------ |
| 13 | `parseNode_mono_zero`              | mixed       | :4568    | ✅     |
| 14 | `parseFlowSequence_mono_zero`      | mixed       | :4644    | ✅     |
| 15 | `parseFlowMapping_mono_zero`       | mixed       | :4658    | ⏳     |
| 16 | `parseBlockSequence_mono_zero`     | mixed       | :4661    | ⏳     |
| 17 | `parseBlockMapping_mono_zero`      | mixed       | :4664    | ⏳     |
| 18 | `parseImplicitBlockSequence_mono_zero` | mixed   | :4667    | ⏳     |
| 19 | `parseSinglePairMapping_mono_zero` | mixed       | :4670    | ⏳     |
| 20 | `parseFlowSequenceLoop_mono_zero`  | mixed       | :4673    | ⏳     |
| 21 | `parseFlowMappingLoop_mono_zero`   | mixed       | :4676    | ⏳     |
| 22 | `parseBlockSequenceLoop_mono_zero` | mixed       | :4679    | ⏳     |
| 23 | `parseBlockMappingLoop_mono_zero`  | mixed       | :4682    | ⏳     |
| 24 | `parseImplicitBlockSequenceLoop_mono_zero` | mixed | :4685   | ⏳     |

**Body style**:
- *parsers* (parts 13–19, originally labelled "vacuous"): the outer fuel
  match at `fuel=1` takes the `fuel+1` branch with internal `fuel=0`, so
  sub-parser calls at fuel=0 error. But this is *not* always pure
  vacuity: part 13 (`parseNode`) has alias/scalar/empty-catch-all paths
  that succeed at fuel=0 (proved 2026-04-21, ~70 lines), and parts 14–17
  (`parseFlowSequence`, etc.) succeed on empty-collection inputs where
  the loop's structural base case (`.ok (#[], ps)`) composes with a
  direct end-token peek. Reassess each part before attempting — pure
  vacuity (`unfold + cases h_ok`) covers only the unreachable-at-fuel=0
  paths, not the full theorem.
- *loops* (parts 20–24, originally labelled "mixed"): `fuel=0` returns
  `.ok (items_acc, ps)` at the structural base case. At fuel=1 input, the
  body's internal calls use fuel=0 (which error for parsers). So the
  hypothesis only holds on the direct `.ok`-return paths: fuel=0 base,
  `.flowSequenceEnd` peek, or `items.size > 0` early-return. Each of
  those paths returns the same `(items, ps)` at fuel=2 trivially. ~20-30
  lines each.

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

### Step 2 — Loop-level fuel monotonicity lemma

Only one theorem remains in this step: the `_fuel_mono_succ` variant was
deleted on 2026-04-20 (unsound as stated at `fuel=0`, unused — see
Audit notes above).

- [ ] `parseFlowSequenceLoop_fuel_mono`
      ([:5404](L4YAML/Proofs/ParserWellBehaved.lean:5404)): generalize to
      any `fuel ≤ fuel'`. Used at
      [:7170](L4YAML/Proofs/ParserWellBehaved.lean:7170) with
      `fuel = 4*N+4`, `fuel' = m''` where `m'' ≥ 4*N+4`.
      Recommended strategy: induct on `fuel' - fuel`, each step applying
      `parseFlowSequenceLoop_mono_step` (Part 8, already proved) via the
      `parser_fuel_mono_succ` projection. Because real callers always have
      `fuel ≥ 4*N+4 ≥ 4`, restrict the signature to `fuel ≥ 1` (or use
      offset form `fuel+1 ≤ fuel'+1`) to sidestep the same fuel=0
      pathology that killed `_fuel_mono_succ`. ~15 lines after
      reformulation.

### Step 3 — Apply `parseNodeProperties_skip` to close 3 sorries

The lemma exists and is already proved: `parseNodeProperties_skip` at
[:5641](L4YAML/Proofs/ParserWellBehaved.lean:5641) — when `ps.peek?` is
not `.anchor _` or `.tag _ _`, the internal `for`-loop breaks immediately,
returning `({}, ps)` unchanged. (The plan previously referred to this as
`parseNodeProperties_break_on_non_tag`, which does not exist — reference
corrected 2026-04-20.)

- [ ] Rewrite 3 sorries inside `parseNode_flowSeqStart_in_seq` at
      [:7052](L4YAML/Proofs/ParserWellBehaved.lean:7052),
      [:7062](L4YAML/Proofs/ParserWellBehaved.lean:7062),
      [:7067](L4YAML/Proofs/ParserWellBehaved.lean:7067) to use
      `parseNodeProperties_skip` directly. Precondition matches
      (`peek? = some .flowSequenceStart`, which is neither
      `.anchor _` nor `.tag _ _`). ~5-10 lines each.

### Step 4 — `parseExplicitKey` helpers

- [ ] `parseExplicitKey_flowSeq`
      ([:6039](L4YAML/Proofs/ParserWellBehaved.lean:6039)): `?[...]` succeeds
      and advances past `]`. ~40-60 lines; follow template from
      `parseNode_flowSeqStart_in_seq`.
- [ ] `parseExplicitKey_flowMap`
      ([:6078](L4YAML/Proofs/ParserWellBehaved.lean:6078)): symmetric
      `?{...}` variant.

### Step 5 — Main witness theorems

- [ ] `parseFlowMappingValue_ok`
      ([:6222](L4YAML/Proofs/ParserWellBehaved.lean:6222)): 1 remaining
      sorry at
      [:6708](L4YAML/Proofs/ParserWellBehaved.lean:6708). Depends on
      Step 4. ~60 lines.
- [ ] `parseEntry_in_flowMap`
      ([:7368](L4YAML/Proofs/ParserWellBehaved.lean:7368)): sorry at
      [:6836](L4YAML/Proofs/ParserWellBehaved.lean:6836) (nested
      unfolding). Three key-shape subcases (scalar key, `[…]` key, `{…}`
      key), each chains through Step 4 helpers +
      `parseFlowMappingValue_ok`. ~60-80 lines.
- [ ] `parseNode_flowMapStart_in_seq`
      ([:7298](L4YAML/Proofs/ParserWellBehaved.lean:7298)): sorry at
      [:7364](L4YAML/Proofs/ParserWellBehaved.lean:7364). Copy
      `parseNode_flowSeqStart_in_seq` and adapt to Map-specific lemmas.
      ~80-100 lines.

### Step 6 — `flow_parser_ok_of_structure` fuel-bound edge cases

Three sorries in the main combined theorem
`flow_parser_ok_of_structure` at
[:7855](L4YAML/Proofs/ParserWellBehaved.lean:7855):

- [ ] [:7929](L4YAML/Proofs/ParserWellBehaved.lean:7929) — nested
      flowSequenceStart when `m < 4*N+6`.
- [ ] [:7936](L4YAML/Proofs/ParserWellBehaved.lean:7936) — nested
      flowMappingStart when `m < 4*N+6`.
- [ ] [:7948](L4YAML/Proofs/ParserWellBehaved.lean:7948) — mapping case
      `m < 4*N+6`.

Each needs either an inline proof for the small-`m` range
(`4*N+4 ≤ m < 4*N+6`) or a lemma showing `parseNode` / `parseEntry`
fails with `nestingDepthExceeded` in that range.

## Reference

- **Canonical bracket-case template**: `parseNode_flowSeqStart_in_seq`
  ([:6946](L4YAML/Proofs/ParserWellBehaved.lean:6946)) — covers all 7
  output properties. Use as the starting point for Step 5.
- **Fuel budget**: parser proofs typically require `fuel ≥ 4*N + 6` where
  `N = tokens.size`; inner loops use `4*N + 4`; `parser_fuel_mono_succ`
  ([:5346](L4YAML/Proofs/ParserWellBehaved.lean:5346)) bridges the gap.
- **Bracket balance identity**: `[pos, pos+1) = +1`, `[pos+1, j) = 0`
  (from IH), `[j, j+1) = -1`; sum is 0.
- **State-field preservation obligations** in every main witness:
  `tokens` preserved, `trackPositions` preserved, `pos` advanced within
  bounds, `peek?` postcondition holds.

## Unused / candidate for review

Theorems declared in `ParserWellBehaved.lean` with no inbound references
from other files (or from non-deleted callers in this file). Review each
before deletion.

- *(none currently flagged; audit pending — run
  `grep -rn "theorem_name"` across the project and sweep this file as a
  batch task.)*
