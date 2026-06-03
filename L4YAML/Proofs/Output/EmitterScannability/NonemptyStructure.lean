/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Proofs.Output.EmitterScannability.BlockProducers
import L4YAML.Proofs.Parser.FlowParserAcceptance

namespace L4YAML.Proofs.EmitterScannability

open L4YAML
open L4YAML.Emit
open L4YAML.Proofs.RoundTrip
open L4YAML.Scanner
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ParserGrammable
open L4YAML.Proofs.ParserWellBehaved
open L4YAML.Proofs.ScalarCoupling

-- ═══ Body token characterization lemmas ═══

-- The proofs require tracing per-step scanner dispatch: each `emit v` produces first
-- character `"`, `[`, or `{`, which dispatch to scanDoubleQuoted / scanFlowSequenceStart /
-- scanFlowMappingStart respectively. The comma separator `, ` dispatches to scanFlowEntry
-- followed by whitespace skip and then the next item's dispatch.
--
-- IMPORTANT: The flowEntry pattern (part 2) is restricted to OUTER-LEVEL flowEntries
-- (where flowBracketBalance from old_sz to k equals 0). Inner flowEntries inside nested
-- bracket groups (e.g., inside a nested mapping `{k1: v1, k2: v2}`) have `.key` after
-- them, not a content start. The parser loop only visits outer-level flowEntries because
-- `parseNode` consumes entire bracket groups, so this restriction is sufficient.

set_option maxHeartbeats 400000 in
/-- Body token characterization for `emitList` in flow context:
    (1) The first new filtered token (at position `old_sz`) is a content start.
    (2) After every OUTER-LEVEL `.flowEntry` (where bracket balance from `old_sz` to `k` is 0),
        the next filtered token is a content start.

    These follow from `emitList`'s structure: items separated by `", "` (comma + space).
    Each item starts with `emit v`, whose first character (`"`, `[`, or `{`) dispatches to
    `scanDoubleQuoted`, `scanFlowSequenceStart`, or `scanFlowMappingStart` — none of which
    emit `.flowEntry` or `.key` as their first filtered token. -/
theorem emitList_body_filtered_characterization
    (items : List YamlValue) (h_ne : items ≠ [])
    (h_all_block : ∀ v ∈ items, EmitScansInFlowBlock v)
    (s : ScannerState) (rest : List Char)
    (h_corr : ScannerSurfCorr s ⟨(emit.emitList items).toList ++ rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_fl : s.flowLevel > 0)
    (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_sync : s.simpleKeyStack.size = s.flowLevel) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    let old_sz := (s.tokens.filter p).size
    ∃ n s', ScanChain s n s'
    ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
    ∧ s'.flowLevel = s.flowLevel
    ∧ s'.directivesPresent = s.directivesPresent
    ∧ s'.indents = s.indents
    ∧ s'.explicitKeyLine = s.explicitKeyLine
    ∧ s'.col > 0
    ∧ s'.inFlow = true
    ∧ s'.currentIndent < 0
    ∧ s'.line = s.line
    ∧ AllTokensOnLine s' s'.line
    ∧ EndLineOnLine s'
    ∧ s'.simpleKeyStack = s.simpleKeyStack
    ∧ FlowMonoChain s.flowLevel s n s'
    -- (1) First new filtered token is a content start (scalar, flowSeqStart, or flowMapStart)
    ∧ (old_sz < (s'.tokens.filter p).size ∧
     (∀ (h : old_sz < (s'.tokens.filter p).size),
       ((∃ c sc, ((s'.tokens.filter p)[old_sz]'h).val = .scalar c sc) ∨
        ((s'.tokens.filter p)[old_sz]'h).val = .flowSequenceStart ∨
        ((s'.tokens.filter p)[old_sz]'h).val = .flowMappingStart)))
    -- (2) After every OUTER-LEVEL flowEntry, next is a content start
    ∧ (∀ (k : Nat), old_sz ≤ k → (h_hi : k < (s'.tokens.filter p).size) →
      ((s'.tokens.filter p)[k]'h_hi).val = .flowEntry →
      flowBracketBalance (s'.tokens.filter p) old_sz k = 0 →
      k + 1 < (s'.tokens.filter p).size ∧
      (∀ (h' : k + 1 < (s'.tokens.filter p).size),
        ((∃ c sc, ((s'.tokens.filter p)[k + 1]'h').val = .scalar c sc) ∨
         ((s'.tokens.filter p)[k + 1]'h').val = .flowSequenceStart ∨
         ((s'.tokens.filter p)[k + 1]'h').val = .flowMappingStart)))
    -- (3) [NEW] The body block is well-bracketed — outer balance is 0.  Threaded from
    --     the `WellBracketed block` the SafeBody producer already supplies (formerly
    --     discarded); converted to `flowBracketBalance` via `flowBracketBalance_eq_pbalance`.
    ∧ flowBracketBalance (s'.tokens.filter p) old_sz (s'.tokens.filter p).size = 0
    -- (4) [NEW] … and every prefix balance from `old_sz` is ≥ 0 (the Dyck condition the
    --     `flowBracketBalance_matching_close` locator consumes).
    ∧ (∀ (k : Nat), old_sz ≤ k → k ≤ (s'.tokens.filter p).size →
        flowBracketBalance (s'.tokens.filter p) old_sz k ≥ 0)
    -- (5) [NEW] The body block is `WellTyped` (typed-bracket matching — every `]` pops a `[`,
    --     every `}` pops a `{`).  Threaded from the `WellTyped block` the SafeBody producer now
    --     supplies (formerly discarded); the body block is exactly `drop old_sz` of the filtered
    --     list.  This is the type half the untyped balance (Parts 3/4) discarded.
    ∧ WellTyped ((s'.tokens.filter p).toList.drop old_sz)
    -- (6) [NEW] Value-end successor: a balanced-prefix end (`balance old_sz (k+1) = 0`) that is
    --     NOT a `.flowEntry` separator is an entry END — either the body close (`k+1 = size`) or
    --     immediately followed by a `.flowEntry`.  Threaded from the `SafeBodyUnit block` the
    --     producer now supplies (formerly discarded) via `SafeBodyUnit_array_succ` — the value-end
    --     DUAL of Part 2's `SafeBody_array_flowEntry`.  This is the `h_succ`/`scalar_succ` substrate
    --     the bracket conjuncts and the scalar-successor field of `SeqBodyProps` consume.
    ∧ (∀ (k : Nat), old_sz ≤ k → (h_hi : k < (s'.tokens.filter p).size) →
        flowBracketBalance (s'.tokens.filter p) old_sz (k + 1) = 0 →
        ((s'.tokens.filter p)[k]'h_hi).val ≠ .flowEntry →
        k + 1 = (s'.tokens.filter p).size ∨
        ∃ (h' : k + 1 < (s'.tokens.filter p).size),
          ((s'.tokens.filter p)[k + 1]'h').val = .flowEntry) := by
  -- Scan the body via the `.bridge.assemble` SafeBody producer.  The returned
  -- `SafeBody ContentStartTok block` subsumes BOTH parts of the characterization:
  -- `SafeBody.head_Q` gives the first-filtered-token content-start (Part 1), and
  -- `SafeBody_array_flowEntry` gives the post-`.flowEntry` content-start (Part 2).
  -- No `SavedKeyDoesntResolve` substrate and no two-chain reconciliation are needed.
  obtain ⟨n, s', block, h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, h_block_eq, h_wb, h_wt, h_sb, h_sbu⟩ :=
    emitList_scans_safebody items h_ne h_all_block s rest h_corr h_flow h_fl h_indent h_col
      h_ek h_atol h_endline h_sync
  -- The body block is exactly the `drop old_sz` of the final filtered token list.
  have h_drop : (s'.tokens.filter (fun t => t.val != .placeholder)).toList.drop
      (s.tokens.filter (fun t => t.val != .placeholder)).size = block := by
    rw [h_block_eq,
      show (s.tokens.filter (fun t => t.val != .placeholder)).size
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList.length
        from Array.length_toList.symm,
      List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
  refine ⟨n, s', h_chain.toScanChain, h_corr', h_fl', h_dp', h_ids', h_ek',
          h_col', h_inflow', h_indent', h_line', h_atol', h_endline',
          h_stack', h_fmc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Part 1: first new filtered token is a content start (`SafeBody.head_Q`)
    obtain ⟨hl, hQ⟩ := h_sb.head_Q
    have h_size : (s'.tokens.filter (fun t => t.val != .placeholder)).size
        = (s.tokens.filter (fun t => t.val != .placeholder)).size + block.length := by
      have h := congrArg List.length h_block_eq
      rw [List.length_append, Array.length_toList, Array.length_toList] at h
      exact h
    refine ⟨by omega, ?_⟩
    intro h_old_lt
    -- the element at `old_sz` is the SafeBody head `block[0]`
    have h0 : (0 : Nat) < ((s'.tokens.filter (fun t => t.val != .placeholder)).toList.drop
        (s.tokens.filter (fun t => t.val != .placeholder)).size).length := by
      rw [h_drop]; exact hl
    have h_elem : ((s'.tokens.filter (fun t => t.val != .placeholder))[
          (s.tokens.filter (fun t => t.val != .placeholder)).size]'h_old_lt) = block[0]'hl := by
      have e1 : ((s'.tokens.filter (fun t => t.val != .placeholder)).toList.drop
            (s.tokens.filter (fun t => t.val != .placeholder)).size)[0]'h0
          = (s'.tokens.filter (fun t => t.val != .placeholder))[
            (s.tokens.filter (fun t => t.val != .placeholder)).size]'h_old_lt := by
        simp only [List.getElem_drop, Array.getElem_toList, Nat.add_zero]
      rw [← e1]
      apply Option.some.inj
      rw [← List.getElem?_eq_getElem h0, ← List.getElem?_eq_getElem hl, h_drop]
    rw [h_elem]; exact hQ
  · -- Part 2: post-`.flowEntry` content start (`SafeBody_array_flowEntry`)
    intro k h_lo h_hi h_fe h_depth
    obtain ⟨hk1, hQ⟩ := SafeBody_array_flowEntry
      (s'.tokens.filter (fun t => t.val != .placeholder))
      (s.tokens.filter (fun t => t.val != .placeholder)).size
      (by rw [h_drop]; exact h_sb) k h_lo h_hi h_fe h_depth
    exact ⟨hk1, fun _ => hQ⟩
  · -- Part 3 [NEW]: outer bracket balance = 0, threaded from `WellBracketed block`.
    have h_sizeeq : (s'.tokens.filter (fun t => t.val != .placeholder)).size
        = (s.tokens.filter (fun t => t.val != .placeholder)).size + block.length := by
      have h := congrArg List.length h_block_eq
      rw [List.length_append, Array.length_toList, Array.length_toList] at h
      exact h
    rw [flowBracketBalance_eq_pbalance (s'.tokens.filter (fun t => t.val != .placeholder))
        (s.tokens.filter (fun t => t.val != .placeholder)).size
        (s'.tokens.filter (fun t => t.val != .placeholder)).size (by omega), h_drop,
      show (s'.tokens.filter (fun t => t.val != .placeholder)).size
          - (s.tokens.filter (fun t => t.val != .placeholder)).size = block.length from by omega,
      List.take_length]
    exact h_wb.1
  · -- Part 4 [NEW]: Dyck prefix-nonneg, threaded from `WellBracketed block`.
    intro k hk1 _hk2
    rw [flowBracketBalance_eq_pbalance (s'.tokens.filter (fun t => t.val != .placeholder))
        (s.tokens.filter (fun t => t.val != .placeholder)).size k hk1, h_drop]
    exact h_wb.2 (k - (s.tokens.filter (fun t => t.val != .placeholder)).size)
  · -- Part 5 [NEW]: WellTyped, threaded from `WellTyped block` (the body block is `drop old_sz`).
    rw [h_drop]; exact h_wt
  · -- Part 6 [NEW]: value-end successor (`SafeBodyUnit_array_succ`), the value-end DUAL of
    -- Part 2's `SafeBody_array_flowEntry`.  Feed the producer's `SafeBodyUnit block` (re-based to
    -- `drop old_sz` of the filtered list via `h_drop`) straight into the array wrapper.
    intro k h_lo h_hi h_bal h_nfe
    exact SafeBodyUnit_array_succ
      (s'.tokens.filter (fun t => t.val != .placeholder))
      (s.tokens.filter (fun t => t.val != .placeholder)).size
      (by rw [h_drop]; exact h_sbu) k h_lo h_hi h_bal h_nfe

/-- Body token characterization for `emitPairList` in flow context:
    (1) The chain has ≥ 3 steps (key handling + value indicator + value content).
    (2) The first new filtered token is `.key` (from `saveSimpleKey` + `scanValuePrepare`
        retroactively converting a placeholder when `: ` is scanned).
    (3) After every OUTER-LEVEL `.flowEntry` (where bracket balance from `old_sz` to `k` is 0),
        the next filtered token is `.key`.

    These follow from `emitPairList`'s structure: each pair produces `emit k ++ ": " ++ emit v`,
    with pairs separated by `", "`. The `: ` triggers `scanValuePrepare` which converts the
    placeholder (saved by `saveSimpleKey` before scanning `emit k`) to `.key`. After each
    comma separator, the next pair starts with `emit k` again, preceded by `saveSimpleKey`.

    IMPORTANT: The flowEntry pattern (part 3) is restricted to outer-level flowEntries
    (bracketBalance = 0). Inner flowEntries from nested sequences/mappings may be followed
    by content-start tokens rather than `.key`. The parser loop only visits outer-level
    flowEntries because `parseNode` consumes entire nested bracket groups. -/
theorem emitPairList_body_filtered_characterization
    (pairs : List (YamlValue × YamlValue)) (h_ne : pairs ≠ [])
    (h_all_k_block : ∀ p ∈ pairs, EmitScansInFlowSavedKeyBlock p.1)
    (h_all_v_block : ∀ p ∈ pairs, EmitScansInFlowBlock p.2)
    (s : ScannerState) (rest : List Char)
    (h_corr : ScannerSurfCorr s ⟨(emit.emitPairList pairs).toList ++ rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_fl : s.flowLevel > 0)
    (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_ska : s.simpleKeyAllowed = true)
    (h_sync : s.simpleKeyStack.size = s.flowLevel) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    let old_sz := (s.tokens.filter p).size
    ∃ n s', ScanChain s n s'
    ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
    ∧ s'.flowLevel = s.flowLevel
    ∧ s'.directivesPresent = s.directivesPresent
    ∧ s'.indents = s.indents
    ∧ s'.explicitKeyLine = s.explicitKeyLine
    ∧ s'.col > 0
    ∧ s'.inFlow = true
    ∧ s'.currentIndent < 0
    ∧ s'.line = s.line
    ∧ AllTokensOnLine s' s'.line
    ∧ EndLineOnLine s'
    ∧ s'.simpleKeyStack = s.simpleKeyStack
    ∧ FlowMonoChain s.flowLevel s n s'
    -- (1) At least 3 chain steps (key + value indicator + value)
    ∧ n ≥ 3
    -- (2) First new filtered token is .key
    ∧ (old_sz < (s'.tokens.filter p).size ∧
     (∀ (h : old_sz < (s'.tokens.filter p).size),
       ((s'.tokens.filter p)[old_sz]'h).val = .key))
    -- (3) After every OUTER-LEVEL flowEntry, next is .key
    ∧ (∀ (k : Nat), old_sz ≤ k → (h_hi : k < (s'.tokens.filter p).size) →
      ((s'.tokens.filter p)[k]'h_hi).val = .flowEntry →
      flowBracketBalance (s'.tokens.filter p) old_sz k = 0 →
      k + 1 < (s'.tokens.filter p).size ∧
      (∀ (h' : k + 1 < (s'.tokens.filter p).size),
        ((s'.tokens.filter p)[k + 1]'h').val = .key))
    -- (4) The body adds at least 3 filtered tokens (one pair scans to ≥ 3 steps,
    --     each strictly growing the filtered count: `.key`, value indicator, value).
    --     Carried directly from the strict-growth chain — no dependency on the
    --     loose `scanNextToken_filtered_grows`.
    ∧ old_sz + 3 ≤ (s'.tokens.filter p).size
    -- (5) [NEW] The body block is well-bracketed — outer balance is 0.  Threaded from the
    --     `WellBracketed block` the map SafeBody producer now supplies (formerly discarded);
    --     converted to `flowBracketBalance` via `flowBracketBalance_eq_pbalance`.
    ∧ flowBracketBalance (s'.tokens.filter p) old_sz (s'.tokens.filter p).size = 0
    -- (6) [NEW] … and every prefix balance from `old_sz` is ≥ 0 (the Dyck condition the
    --     `flowBracketBalance_matching_close` locator consumes).
    ∧ (∀ (k : Nat), old_sz ≤ k → k ≤ (s'.tokens.filter p).size →
        flowBracketBalance (s'.tokens.filter p) old_sz k ≥ 0)
    -- (7) [NEW] The body block is `WellTyped` (typed-bracket matching).  Threaded from the
    --     `WellTyped block` the map SafeBody producer now supplies; the type half the untyped
    --     balance (Parts 5/6) discarded.
    ∧ WellTyped ((s'.tokens.filter p).toList.drop old_sz) := by
  -- Scan the body via the `.bridge.assemble.map` SafeBody producer.  The returned
  -- `SafeBody (· = .key) block` subsumes BOTH non-trivial parts of the characterization:
  -- `SafeBody.head_Q` gives the first-filtered-token `.key` (Part 2) and
  -- `SafeBody_array_flowEntry` gives the post-outer-`.flowEntry` `.key` (Part 3); the
  -- `3 ≤ n` chain-length floor (Part 1) is carried alongside.  No `keyshape` producer
  -- and no two-chain reconciliation are needed.
  obtain ⟨n, s', block, h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, h_block_eq, h_wb, h_wt, h_sb, h_n_ge_3⟩ :=
    emitPairList_scans_safebody pairs h_ne h_all_k_block h_all_v_block s rest h_corr h_flow h_fl
      h_indent h_col h_ek h_atol h_endline h_ska h_sync
  -- The body block is exactly the `drop old_sz` of the final filtered token list.
  have h_drop : (s'.tokens.filter (fun t => t.val != .placeholder)).toList.drop
      (s.tokens.filter (fun t => t.val != .placeholder)).size = block := by
    rw [h_block_eq,
      show (s.tokens.filter (fun t => t.val != .placeholder)).size
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList.length
        from Array.length_toList.symm,
      List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
  refine ⟨n, s', h_chain.toScanChain, h_corr', h_fl', h_dp', h_ids', h_ek',
          h_col', h_inflow', h_indent', h_line', h_atol', h_endline',
          h_stack', h_fmc, h_n_ge_3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Part 2: first new filtered token is `.key` (`SafeBody.head_Q`)
    obtain ⟨hl, hQ⟩ := h_sb.head_Q
    have h_size : (s'.tokens.filter (fun t => t.val != .placeholder)).size
        = (s.tokens.filter (fun t => t.val != .placeholder)).size + block.length := by
      have h := congrArg List.length h_block_eq
      rw [List.length_append, Array.length_toList, Array.length_toList] at h
      exact h
    refine ⟨by omega, ?_⟩
    intro h_old_lt
    have h0 : (0 : Nat) < ((s'.tokens.filter (fun t => t.val != .placeholder)).toList.drop
        (s.tokens.filter (fun t => t.val != .placeholder)).size).length := by
      rw [h_drop]; exact hl
    have h_elem : ((s'.tokens.filter (fun t => t.val != .placeholder))[
          (s.tokens.filter (fun t => t.val != .placeholder)).size]'h_old_lt) = block[0]'hl := by
      have e1 : ((s'.tokens.filter (fun t => t.val != .placeholder)).toList.drop
            (s.tokens.filter (fun t => t.val != .placeholder)).size)[0]'h0
          = (s'.tokens.filter (fun t => t.val != .placeholder))[
            (s.tokens.filter (fun t => t.val != .placeholder)).size]'h_old_lt := by
        simp only [List.getElem_drop, Array.getElem_toList, Nat.add_zero]
      rw [← e1]
      apply Option.some.inj
      rw [← List.getElem?_eq_getElem h0, ← List.getElem?_eq_getElem hl, h_drop]
    rw [h_elem]; exact hQ
  · -- Part 3: post-outer-`.flowEntry` `.key` (`SafeBody_array_flowEntry`)
    intro k h_lo h_hi h_fe h_depth
    obtain ⟨hk1, hQ⟩ := SafeBody_array_flowEntry
      (s'.tokens.filter (fun t => t.val != .placeholder))
      (s.tokens.filter (fun t => t.val != .placeholder)).size
      (by rw [h_drop]; exact h_sb) k h_lo h_hi h_fe h_depth
    exact ⟨hk1, fun _ => hQ⟩
  · -- Part 4: filtered growth ≥ 3, read off the strict-growth chain + `3 ≤ n`.
    have hg := ScanChainGrew_filtered_grows h_chain
    omega
  · -- Part 5 [NEW]: outer bracket balance = 0, threaded from `WellBracketed block`.
    have h_sizeeq : (s'.tokens.filter (fun t => t.val != .placeholder)).size
        = (s.tokens.filter (fun t => t.val != .placeholder)).size + block.length := by
      have h := congrArg List.length h_block_eq
      rw [List.length_append, Array.length_toList, Array.length_toList] at h
      exact h
    rw [flowBracketBalance_eq_pbalance (s'.tokens.filter (fun t => t.val != .placeholder))
        (s.tokens.filter (fun t => t.val != .placeholder)).size
        (s'.tokens.filter (fun t => t.val != .placeholder)).size (by omega), h_drop,
      show (s'.tokens.filter (fun t => t.val != .placeholder)).size
          - (s.tokens.filter (fun t => t.val != .placeholder)).size = block.length from by omega,
      List.take_length]
    exact h_wb.1
  · -- Part 6 [NEW]: Dyck prefix-nonneg, threaded from `WellBracketed block`.
    intro k hk1 _hk2
    rw [flowBracketBalance_eq_pbalance (s'.tokens.filter (fun t => t.val != .placeholder))
        (s.tokens.filter (fun t => t.val != .placeholder)).size k hk1, h_drop]
    exact h_wb.2 (k - (s.tokens.filter (fun t => t.val != .placeholder)).size)
  · -- Part 7 [NEW]: WellTyped, threaded from `WellTyped block` (the body block is `drop old_sz`).
    rw [h_drop]; exact h_wt

/-- **Parametric `SeqBodyProps` assembler** (Phase J seed).  Given an arbitrary balanced
    flow-sequence subrange `[lo, hi)` — `tokens[hi]! = .flowSequenceEnd`, total balance `0`, Dyck
    prefixes, interior `WellTyped` — together with the three *primitive* per-subrange facts
    (content-start at `lo`; the value-end successor `h_body_succ`; the post-`.flowEntry` content-start
    `h_fe_pattern`), assemble the full `SeqBodyProps tokens lo hi`.

    This is the outer-span assembly inside `scanFiltered_emitSeq_nonempty_structure` (the former inline
    `_h_seq_body_props`) lifted off the fixed span `(2, tokens.size − 2)` to an arbitrary subrange:
    every `SeqBodyProps` field is a projection off these inputs — the bracket conjuncts via
    `seq_bracket_{seq,map}_conjunct`, and the value-close-guarded successor re-derived inline from
    `h_body_succ` + `h_tpe` (a value-CLOSE delta `-1` discharges the `≠ .flowEntry` guard; the
    body-close case routes through the boundary `h_tpe`).  The remaining Phase-J work is purely to
    *produce* the three primitives at every nested subrange (`WellTyped_subrange` already supplies the
    per-subrange `WellTyped`); this lemma is the joint the recursive producer calls once it has them. -/
theorem seqBodyProps_assemble (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_hi_sz : hi ≤ tokens.size)
    (h_tpe : tokens[hi]!.val = .flowSequenceEnd)
    (h_outer_bal : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt_interior : WellTyped ((tokens.toList.take hi).drop lo))
    (h_content_start : isFlowContentStart tokens[lo]!.val)
    (h_body_succ : ∀ k, lo ≤ k → k < hi →
      flowBracketBalance tokens lo (k + 1) = 0 →
      tokens[k]!.val ≠ .flowEntry →
      k + 1 = hi ∨ ∃ (_ : k + 1 < hi), tokens[k + 1]!.val = .flowEntry)
    (h_fe_pattern : ∀ k, lo ≤ k → k < hi →
      tokens[k]!.val = .flowEntry →
      flowBracketBalance tokens lo k = 0 →
      k + 1 ≤ hi ∧ isFlowContentStart tokens[k + 1]!.val) :
    SeqBodyProps tokens lo hi := by
  -- Value-close-guarded successor: re-express `h_body_succ` in the EXACT `h_succ` shape the bracket
  -- conjunct assemblers consume (a value-CLOSE delta `-1` discharges the `≠ .flowEntry` guard; the
  -- body-close case routes through the boundary `h_tpe`).
  have h_succ_guarded : ∀ j, lo ≤ j → j < hi →
      flowBracketDelta tokens[j]!.val = -1 →
      flowBracketBalance tokens lo (j + 1) = 0 →
      j + 1 ≤ hi ∧
      (tokens[j + 1]!.val = .flowEntry ∨
       (tokens[j + 1]!.val = .flowSequenceEnd ∧ j + 1 = hi)) := by
    intro j h_lo h_hi h_delta h_bal
    have h_nfe : tokens[j]!.val ≠ .flowEntry := by
      intro h_eq; rw [h_eq] at h_delta; exact absurd h_delta (by decide)
    rcases h_body_succ j h_lo h_hi h_bal h_nfe with h_end | ⟨h', h_fe⟩
    · exact ⟨Nat.le_of_eq h_end, Or.inr ⟨by rw [h_end]; exact h_tpe, h_end⟩⟩
    · exact ⟨Nat.le_of_lt h', Or.inl h_fe⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- content_start
    intro _; exact h_content_start
  · -- scalar_succ — derive the balance shift past the depth-0 scalar, then `h_body_succ`
    intro k h_lo h_hi h_bal_k h_scalar
    have h_k_sz : k < tokens.size := by omega
    have h_k_lt_list : k < tokens.toList.length := by rw [Array.length_toList]; exact h_k_sz
    obtain ⟨c, s, hcs⟩ := h_scalar
    have h_delta0 : flowBracketDelta tokens.toList[k].val = 0 := by
      have h_eq : tokens.toList[k]'h_k_lt_list = tokens[k]! := by
        rw [getElem!_pos tokens k h_k_sz, Array.getElem_toList]
      simp only [h_eq, hcs, flowBracketDelta]
    have h_bal_k1 : flowBracketBalance tokens lo (k + 1) = 0 := by
      have hc := flowBracketBalance_compose tokens lo k (k + 1) (by omega) (by omega)
      rw [flowBracketBalance_single tokens k h_k_lt_list, h_delta0] at hc
      omega
    have h_nfe : tokens[k]!.val ≠ .flowEntry := by rw [hcs]; simp
    rcases h_body_succ k h_lo h_hi h_bal_k1 h_nfe with h_end | ⟨h', h_fe⟩
    · exact ⟨Nat.le_of_eq h_end, Or.inr ⟨by rw [h_end]; exact h_tpe, h_end⟩⟩
    · exact ⟨Nat.le_of_lt h', Or.inl h_fe⟩
  · -- after_fe — `h_fe_pattern` gives `k+1 ≤ hi`; sharpen to `<` via `h_tpe`
    intro k h_lo h_hi h_bal_k h_fe
    obtain ⟨h_le, h_cs⟩ := h_fe_pattern k h_lo h_hi h_fe h_bal_k
    refine ⟨?_, h_cs⟩
    rcases Nat.lt_or_eq_of_le h_le with h | h
    · exact h
    · exfalso; rw [h, h_tpe] at h_cs; simp [isFlowContentStart] at h_cs
  · -- bracket_seq
    intro k h_lo h_hi h_bal_k h_open
    exact seq_bracket_seq_conjunct tokens lo hi k h_lo h_hi h_hi_sz
      h_bal_k h_open h_outer_bal h_dyck h_wt_interior
      (fun j hkj hjhi hd hb => h_succ_guarded j (by omega) hjhi hd hb)
  · -- bracket_map (a bracketed-map item still routes through the seq successor)
    intro k h_lo h_hi h_bal_k h_open
    exact seq_bracket_map_conjunct tokens lo hi k h_lo h_hi h_hi_sz
      h_bal_k h_open h_outer_bal h_dyck h_wt_interior
      (fun j hkj hjhi hd hb => h_succ_guarded j (by omega) hjhi hd hb)

/-! ### Recursive flow-SEQUENCE body deliverable (Phase J, seq side)

`RecSeqBody` is the recursive deliverable of the seq-side producer: a `SafeBody` over
`ContentStartTok` that ADDITIONALLY records, at each nested flow-sequence entry, the
recursive structure of its interior.  It is what the producer (`emitList_scans_safebody`
applied at every nesting level) supplies in one shot, and what the descent-locator
consumes to extract a windowed `SafeBody` at any nested guarded subrange.  The flat
`SafeBody`/`SafeBodyUnit ContentStartTok` that `seqBodyProps_of_windowed_safebody` already
consumes are PROJECTIONS of it (`toSafeBody`/`toSafeBodyUnit` below), so wiring `RecSeqBody`
as the producer's output type collapses the scattered "produce a flat windowed `SafeBody` at
every subrange" residual into the single typed boundary "produce one `RecSeqBody` of the
outer body" — the consumer-joint-before-producer reshape, one nesting level up.

A `RecSeqEntry` is one `emit v` block: a `scalar` leaf, an empty `[ ]`/`{ }` (`seqEmpty` /
the empty case of `map`), a nested flow-sequence `[ interior ]` whose `interior` recurses
(`seq`), or a nested flow-mapping `{ interior }` (`map`).  The mapping interior bottoms out
at its `WellBracketed` substrate here — its key/value recursion is a separate (map-side)
brick; the seq flat projections need only `WellBracketed` (via `wrap_{seq,map}_block`'s
`EntrySafe` / `EntryUnit_wrap`), so they hold regardless.  Empty interiors are carried by
`seqEmpty` (and `interior = []` in `map`), the `lo = hi` shape the empty-body leaf discharges
positionally; the recursive occurrence cannot sit under `Or`, hence the separate constructor. -/
mutual
  inductive RecSeqBody : List (Positioned YamlToken) → Prop where
    | single (e : List (Positioned YamlToken)) (h_ne : e ≠ [])
        (h_e : RecSeqEntry e) (h_head : ContentStartTok (e.head h_ne).val) : RecSeqBody e
    | cons (e : List (Positioned YamlToken)) (fe : Positioned YamlToken)
        (rest : List (Positioned YamlToken)) (h_ne : e ≠ [])
        (h_e : RecSeqEntry e) (h_head : ContentStartTok (e.head h_ne).val)
        (h_fe : fe.val = .flowEntry) (h_rest : RecSeqBody rest) :
        RecSeqBody (e ++ fe :: rest)
  inductive RecSeqEntry : List (Positioned YamlToken) → Prop where
    | scalar (t : Positioned YamlToken) (c : String) (s : ScalarStyle)
        (h : t.val = .scalar c s) : RecSeqEntry [t]
    | seqEmpty (op cl : Positioned YamlToken)
        (h_op : op.val = .flowSequenceStart) (h_cl : cl.val = .flowSequenceEnd) :
        RecSeqEntry (op :: ([] ++ [cl]))
    | seq (op cl : Positioned YamlToken) (interior : List (Positioned YamlToken))
        (h_op : op.val = .flowSequenceStart) (h_cl : cl.val = .flowSequenceEnd)
        (h_wb : WellBracketed interior) (h_rec : RecSeqBody interior) :
        RecSeqEntry (op :: (interior ++ [cl]))
    | map (op cl : Positioned YamlToken) (interior : List (Positioned YamlToken))
        (h_op : op.val = .flowMappingStart) (h_cl : cl.val = .flowMappingEnd)
        (h_wb : WellBracketed interior) :
        RecSeqEntry (op :: (interior ++ [cl]))
end

/-- A recursive seq entry is `EntrySafe` (the flat per-entry obligation `SafeBody` consumes). -/
theorem RecSeqEntry.toEntrySafe {e : List (Positioned YamlToken)}
    (h : RecSeqEntry e) : EntrySafe e := by
  cases h with
  | scalar t c s ht => exact EntrySafe_scalar t c s ht
  | seqEmpty op cl h_op h_cl => exact (wrap_seq_block op cl [] h_op h_cl WellBracketed_nil).2
  | seq op cl interior h_op h_cl h_wb _ => exact (wrap_seq_block op cl interior h_op h_cl h_wb).2
  | map op cl interior h_op h_cl h_wb => exact (wrap_map_block op cl interior h_op h_cl h_wb).2

/-- A recursive seq entry is `EntryUnit` (the unit refinement — one `emit v` is one unit). -/
theorem RecSeqEntry.toEntryUnit {e : List (Positioned YamlToken)}
    (h : RecSeqEntry e) : EntryUnit e := by
  cases h with
  | scalar t c s ht => exact EntryUnit_scalar t c s ht
  | seqEmpty op cl h_op h_cl =>
      exact EntryUnit_wrap op cl [] (h_op ▸ flowBracketDelta_flowSequenceStart)
        (h_cl ▸ flowBracketDelta_flowSequenceEnd) WellBracketed_nil
  | seq op cl interior h_op h_cl h_wb _ =>
      exact EntryUnit_wrap op cl interior (h_op ▸ flowBracketDelta_flowSequenceStart)
        (h_cl ▸ flowBracketDelta_flowSequenceEnd) h_wb
  | map op cl interior h_op h_cl h_wb =>
      exact EntryUnit_wrap op cl interior (h_op ▸ flowBracketDelta_flowMappingStart)
        (h_cl ▸ flowBracketDelta_flowMappingEnd) h_wb

/-- **Flat projection (seq side).**  A `RecSeqBody` is in particular a flat
    `SafeBody ContentStartTok` — exactly the windowed deliverable
    `seqBodyProps_of_windowed_safebody` consumes.  The recursive interiors are discarded;
    only the per-entry `EntrySafe` and content-start head are used, so the projection is
    robust to the map interior bottoming out. -/
theorem RecSeqBody.toSafeBody : {l : List (Positioned YamlToken)} →
    RecSeqBody l → SafeBody ContentStartTok l
  | _, .single e h_ne h_e h_head => SafeBody.single e h_ne h_e.toEntrySafe h_head
  | _, .cons e fe rest h_ne h_e h_head h_fe h_rest =>
      SafeBody.cons e fe rest h_ne h_e.toEntrySafe h_head h_fe h_rest.toSafeBody

/-- **Flat unit projection (seq side).**  A `RecSeqBody` is also a flat
    `SafeBodyUnit ContentStartTok` (each `emit v` entry is one unit) — the second windowed
    deliverable `seqBodyProps_of_windowed_safebody` consumes. -/
theorem RecSeqBody.toSafeBodyUnit : {l : List (Positioned YamlToken)} →
    RecSeqBody l → SafeBodyUnit ContentStartTok l
  | _, .single e h_ne h_e h_head => SafeBodyUnit.single e h_ne h_e.toEntryUnit h_head
  | _, .cons e fe rest h_ne h_e h_head h_fe h_rest =>
      SafeBodyUnit.cons e fe rest h_ne h_e.toEntryUnit h_head h_fe h_rest.toSafeBodyUnit

/-- Append-singleton injectivity (core Lean, no Mathlib): from `a ++ [x] = b ++ [y]` recover both
    `a = b` and `x = y`.  Used to read a bracket entry's interior off the constructor index when the
    descent matches a `seq`/`map` entry's `op :: (interior ++ [cl])` shape against `RecSeqEntry`. -/
theorem append_singleton_inj {a b : List (Positioned YamlToken)} {x y : Positioned YamlToken}
    (h : a ++ [x] = b ++ [y]) : a = b ∧ x = y := by
  have hr := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hr
  injection hr with hxy har
  exact ⟨List.reverse_inj.mp har, hxy⟩

/-- **Single-level seq descent** (Phase J, seq side — descent-locator core).  A nested
    flow-SEQUENCE entry `op :: (interior ++ [cl])` recorded inside the recursive deliverable
    (its `op` a `.flowSequenceStart`) has an interior that is EITHER empty (`interior = []`, the
    `lo = hi` shape `seqBodyProps_empty` discharges positionally) OR itself a `RecSeqBody` (the
    `lo < hi` shape the consumer joint `seqBodyProps_of_windowed_safebody` consumes after
    `RecSeqBody.toSafeBody`).  This is the irreducible "descend one nesting level" step of the
    descent-locator: the recursive `RecSeqEntry.seq.h_rec` is recovered structurally from a
    bracket-typed entry, and the empty/non-empty disjunction is EXACTLY the producer-contract
    split (Reflection 233 — the empty branch the `SafeBody`-keyed joint structurally cannot cover
    is the branch it is never asked to cover).  The `scalar` and `map` constructors are ruled out
    by the `.flowSequenceStart` head, `seqEmpty` is the empty witness. -/
theorem RecSeqEntry.seq_interior {e interior : List (Positioned YamlToken)}
    {op cl : Positioned YamlToken}
    (h : RecSeqEntry e) (h_eq : e = op :: (interior ++ [cl]))
    (h_op : op.val = .flowSequenceStart) :
    RecSeqBody interior ∨ interior = [] := by
  cases h with
  | scalar t c s ht =>
      -- `e = [t]`: the head matches but `interior ++ [cl] = []` is impossible.
      injection h_eq with _h1 h2; simp at h2
  | seqEmpty op' cl' h_op' h_cl' =>
      -- `e = op' :: ([] ++ [cl'])`: interior is forced empty.
      right
      injection h_eq with _h1 h2
      simp only [List.nil_append] at h2
      exact ((append_singleton_inj h2.symm).1)
  | seq op' cl' interior' h_op' h_cl' h_wb h_rec =>
      -- The recursive interior witness, transported across `interior' = interior`.
      left
      injection h_eq with _h1 h2
      exact (append_singleton_inj h2).1 ▸ h_rec
  | map op' cl' interior' h_op' h_cl' h_wb =>
      -- `op'.val = .flowMappingStart` clashes with the `.flowSequenceStart` head.
      exfalso
      injection h_eq with h1 _h2
      rw [h1, h_op] at h_op'
      exact absurd h_op' (by decide)

/-- **Single-level map descent** (Phase J, seq side — descent-locator core, map entries).  A nested
    flow-MAPPING entry `op :: (interior ++ [cl])` recorded inside the recursive deliverable (its
    `op` a `.flowMappingStart`) has a `WellBracketed` interior — the map interior bottoms out at its
    `WellBracketed` substrate in `RecSeqEntry.map` (its key/value recursion is a separate, map-side
    brick), so the descent into a nested *mapping* yields exactly the bracket fact the map consumer
    joint needs, no recursion.  The empty interior is covered too (`WellBracketed []`).  The
    `scalar`, `seqEmpty` and `seq` constructors are ruled out by the `.flowMappingStart` head. -/
theorem RecSeqEntry.map_interior {e interior : List (Positioned YamlToken)}
    {op cl : Positioned YamlToken}
    (h : RecSeqEntry e) (h_eq : e = op :: (interior ++ [cl]))
    (h_op : op.val = .flowMappingStart) :
    WellBracketed interior := by
  cases h with
  | scalar t c s ht =>
      injection h_eq with _h1 h2; simp at h2
  | seqEmpty op' cl' h_op' h_cl' =>
      exfalso
      injection h_eq with h1 _h2
      rw [h1, h_op] at h_op'
      exact absurd h_op' (by decide)
  | seq op' cl' interior' h_op' h_cl' h_wb h_rec =>
      exfalso
      injection h_eq with h1 _h2
      rw [h1, h_op] at h_op'
      exact absurd h_op' (by decide)
  | map op' cl' interior' h_op' h_cl' h_wb =>
      injection h_eq with _h1 h2
      exact (append_singleton_inj h2).1 ▸ h_wb

/-- **Empty-body leaf** (Phase J, seq side).  An empty nested flow-SEQUENCE body — `lo = hi`, the
    shape `emit (.sequence … #[]) = "[]"` scans to (`[` immediately followed by `]`, so the interior
    `[lo, hi)` is empty) — satisfies `SeqBodyProps` *vacuously*: `content_start` is guarded by
    `lo < hi` and every other field by `∀ k, lo ≤ k → k < hi`, all unsatisfiable when `lo = hi`.

    This is the `lo = hi` branch of the `FlowSubrangesOk.seq` producer, the complement of the
    `lo < hi` consumer joint `seqBodyProps_of_windowed_safebody`.  The split is essential: the
    consumer joint needs a `SafeBody`, which has **no `nil` constructor** and so cannot represent an
    empty body — and is correctly never required here, because an empty body's `SeqBodyProps` is
    vacuous.  So the empty case is sound to discharge separately, and the consumer-joint architecture
    (`SafeBody`-keyed) is sound precisely because it is only ever instantiated at `lo < hi`. -/
theorem seqBodyProps_empty (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h : lo = hi) : SeqBodyProps tokens lo hi := by
  subst h
  exact ⟨fun h => absurd h (by omega), fun k h1 h2 => (by omega : False).elim,
    fun k h1 h2 => (by omega : False).elim, fun k h1 h2 => (by omega : False).elim,
    fun k h1 h2 => (by omega : False).elim⟩

/-- **Empty-body leaf** (Phase J, map side).  The map mirror of `seqBodyProps_empty`: an empty nested
    flow-MAPPING body (`emit (.mapping … #[]) = "{}"`, interior `[lo, hi)` empty) satisfies
    `MapBodyProps tokens lo hi` vacuously — `key_start` is guarded by `lo < hi`, M2–M10 by
    `∀ k, lo ≤ k → k < hi`.  The `lo = hi` branch of `FlowSubrangesOk.map`. -/
theorem mapBodyProps_empty (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h : lo = hi) : MapBodyProps tokens lo hi := by
  subst h
  exact ⟨fun h => absurd h (by omega), fun k h1 h2 => (by omega : False).elim,
    fun k h1 h2 => (by omega : False).elim, fun k h1 h2 => (by omega : False).elim,
    fun k h1 h2 => (by omega : False).elim, fun k h1 h2 => (by omega : False).elim,
    fun k h1 h2 => (by omega : False).elim, fun k h1 h2 => (by omega : False).elim,
    fun k h1 h2 => (by omega : False).elim, fun k h1 h2 => (by omega : False).elim⟩

/-- **Windowed-`SafeBody` → `SeqBodyProps` consumer joint** (Phase J, seq side).  Given a guarded
    balanced flow-SEQUENCE subrange `[lo, hi)` (close `.flowSequenceEnd`, total balance `0`, Dyck
    prefixes, interior `WellTyped`) together with the recursive *deliverable* of the body producer —
    the windowed `SafeBody`/`SafeBodyUnit ContentStartTok ((tokens.toList.take hi).drop lo)` plus the
    content-start head at `lo` — assemble the full `SeqBodyProps tokens lo hi`.

    This consolidates the entire seq-side assembly into a single entry point keyed *only* on the
    windowed SafeBody facts.  It drives last session's windowed array wrappers
    (`SafeBody_array_flowEntry_window` → the `after_fe` primitive; `SafeBodyUnit_array_succ_window` →
    the value-end successor) into `seqBodyProps_assemble`.  The only glue is the
    `getElem!`↔`getElem` bridge (the wrappers speak `arr[k]'_`, the assembler primitives `tokens[k]!`)
    and the definitional `ContentStartTok = isFlowContentStart`.  So the seq-side residual now narrows
    to purely *producing* the windowed `SafeBody`/`SafeBodyUnit` at a nested guarded subrange (the
    recursive characterization of the nested flow-sequence body) — the bracket facts come from the
    typed locator + `WellTyped_subrange`, and `content_start` is `SafeBody.head_Q`. -/
theorem seqBodyProps_of_windowed_safebody (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_hi_sz : hi ≤ tokens.size)
    (h_tpe : tokens[hi]!.val = .flowSequenceEnd)
    (h_outer_bal : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt_interior : WellTyped ((tokens.toList.take hi).drop lo))
    (h_content_start : isFlowContentStart tokens[lo]!.val)
    (h_safe : SafeBody ContentStartTok ((tokens.toList.take hi).drop lo))
    (h_safe_unit : SafeBodyUnit ContentStartTok ((tokens.toList.take hi).drop lo)) :
    SeqBodyProps tokens lo hi := by
  refine seqBodyProps_assemble tokens lo hi h_hi_sz h_tpe h_outer_bal h_dyck h_wt_interior
    h_content_start ?_ ?_
  · -- h_body_succ ← `SafeBodyUnit_array_succ_window` (value-end successor)
    intro k h_lo h_klt h_bal h_nfe
    have hk_sz : k < tokens.size := Nat.lt_of_lt_of_le h_klt h_hi_sz
    rw [getElem!_pos tokens k hk_sz] at h_nfe
    rcases SafeBodyUnit_array_succ_window tokens lo hi h_hi_sz h_safe_unit k h_lo h_klt h_bal h_nfe with
      h_end | ⟨hk1, h_fe⟩
    · exact Or.inl h_end
    · refine Or.inr ⟨hk1, ?_⟩
      have hk1_sz : k + 1 < tokens.size := Nat.lt_of_lt_of_le hk1 h_hi_sz
      rw [getElem!_pos tokens (k + 1) hk1_sz]
      exact h_fe
  · -- h_fe_pattern ← `SafeBody_array_flowEntry_window` (post-`.flowEntry` content-start)
    intro k h_lo h_klt h_fe h_bal
    have hk_sz : k < tokens.size := Nat.lt_of_lt_of_le h_klt h_hi_sz
    rw [getElem!_pos tokens k hk_sz] at h_fe
    obtain ⟨hk1, hQ⟩ :=
      SafeBody_array_flowEntry_window tokens lo hi h_hi_sz h_safe k h_lo h_klt h_fe h_bal
    have hk1_sz : k + 1 < tokens.size := Nat.lt_of_lt_of_le hk1 h_hi_sz
    refine ⟨Nat.le_of_lt hk1, ?_⟩
    rw [getElem!_pos tokens (k + 1) hk1_sz]
    exact hQ

/-- **Interior-window identity** (Phase J, seq side — descent-locator positional bridge, slice half).
    When the array window `[lo, hi]` (positions `lo … hi`, captured as the list slice
    `(tokens.toList.take (hi+1)).drop lo`) equals a bracket entry's interior-plus-close
    `interior ++ [cl]`, the `interior` alone is the inner window `[lo, hi)` —
    `(tokens.toList.take hi).drop lo`.  Pure list/array slicing (no balance reasoning): peel the
    last element `tokens[hi]` off `take (hi+1)` via `List.take_add_one`, then
    `List.drop_append_of_le_length` (`lo ≤ hi = |take hi|`) moves the `drop` inside, leaving
    `(take hi).drop lo ++ [tokens[hi]] = interior ++ [cl]`, and `append_singleton_inj` reads off
    `interior = (take hi).drop lo` (and `cl = tokens[hi]`).  This is the slice half of the
    descent-locator's positional bridge — it turns the recursive deliverable's structural `interior`
    (a `List`, the `RecSeqEntry.seq.h_rec` argument) into the *positionally windowed* form
    `(tokens.toList.take hi).drop lo` that `seqBodyProps_of_windowed_safebody` is keyed on; the
    remaining half (which `RecSeqEntry` of the windowed body a guarded balanced subrange selects, via
    its `tokens[lo-1]` opener) is the locator's structural front end. -/
theorem interior_window_eq (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (interior : List (Positioned YamlToken)) (cl : Positioned YamlToken)
    (h_lo_hi : lo ≤ hi) (h_hi_sz : hi < tokens.size)
    (h_window : (tokens.toList.take (hi + 1)).drop lo = interior ++ [cl]) :
    interior = (tokens.toList.take hi).drop lo := by
  have h_hi_len : hi < tokens.toList.length := by rw [Array.length_toList]; exact h_hi_sz
  have h_ts : tokens.toList.take (hi + 1)
      = tokens.toList.take hi ++ [tokens.toList[hi]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h_hi_len]; rfl
  rw [h_ts] at h_window
  have h_len : lo ≤ (tokens.toList.take hi).length := by
    rw [List.length_take]; omega
  rw [List.drop_append_of_le_length h_len] at h_window
  exact ((append_singleton_inj h_window).1).symm

/-- **Located-`RecSeqBody` → `SeqBodyProps` consumer joint** (Phase J, seq side).  Combines the
    descent-locator's deliverable with the consumer joint in one step: given a guarded balanced
    flow-SEQUENCE subrange `[lo, hi)` (the bracket facts `h_tpe`/`h_outer_bal`/`h_dyck`/
    `h_wt_interior` + the content-start head, exactly as `seqBodyProps_of_windowed_safebody`) whose
    array window `(tokens.toList.take (hi+1)).drop lo` is a bracket entry's `interior ++ [cl]`, AND
    the descent has handed back that `interior`'s recursive structure `RecSeqBody interior` (the
    `RecSeqEntry.seq_interior` non-empty disjunct), assemble `SeqBodyProps tokens lo hi`.

    The window identity `interior_window_eq` rewrites the structural `interior` into the positionally
    windowed `(tokens.toList.take hi).drop lo`, so `RecSeqBody.toSafeBody`/`.toSafeBodyUnit` deliver
    exactly the windowed `SafeBody`/`SafeBodyUnit ContentStartTok` that
    `seqBodyProps_of_windowed_safebody` consumes — closing the back half of the descent-locator:
    *once an entry's interior is located as `RecSeqBody`, its `SeqBodyProps` at the absolute window
    follows with no further structural work.*  `content_start` is taken positionally here (the front
    end supplies it; it is also `(toSafeBody).head_Q`).  What remains upstream is purely the locate
    itself — pairing a guarded subrange's `tokens[lo-1]` opener to its `RecSeqEntry`, then descending
    via `seq_interior` (empty branch → `seqBodyProps_empty`, this lemma's non-empty branch otherwise). -/
theorem seqBodyProps_of_recseqbody_window (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (interior : List (Positioned YamlToken)) (cl : Positioned YamlToken)
    (h_lo_hi : lo ≤ hi) (h_hi_sz : hi < tokens.size)
    (h_tpe : tokens[hi]!.val = .flowSequenceEnd)
    (h_outer_bal : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt_interior : WellTyped ((tokens.toList.take hi).drop lo))
    (h_content_start : isFlowContentStart tokens[lo]!.val)
    (h_window : (tokens.toList.take (hi + 1)).drop lo = interior ++ [cl])
    (h_rec : RecSeqBody interior) :
    SeqBodyProps tokens lo hi := by
  have h_eq : interior = (tokens.toList.take hi).drop lo :=
    interior_window_eq tokens lo hi interior cl h_lo_hi h_hi_sz h_window
  exact seqBodyProps_of_windowed_safebody tokens lo hi (Nat.le_of_lt h_hi_sz) h_tpe
    h_outer_bal h_dyck h_wt_interior h_content_start (h_eq ▸ h_rec.toSafeBody)
    (h_eq ▸ h_rec.toSafeBodyUnit)

/-- **Parametric `MapBodyProps` assembler** (Phase J seed, map side).  The map-side mirror of
    `seqBodyProps_assemble`: given an arbitrary balanced flow-MAPPING subrange `[lo, hi)` —
    `tokens[hi]! = .flowMappingEnd`, total balance `0`, Dyck prefixes, interior `WellTyped` — together
    with the per-subrange *primitive* facts for the depth-0 key/value alternation, assemble the full
    ten-field `MapBodyProps tokens lo hi`.

    Six fields are direct projections of their primitive (M1 `key_start`, M2 `after_fe`, M3
    `key_content`, M4 `key_scalar_value`, M6 `value_content`, M7 `value_scalar_succ`).  The two
    bracket-content fields are assembled by the already-proven typed-locator conjuncts: M5
    `key_bracket_value` via `map_key_bracket_conjunct` and M8 `value_bracket_succ` via
    `map_value_bracket_conjunct`, each fed the bracket facts plus the value-CLOSE-guarded successor
    primitive (`h_key_bracket_succ` / `h_value_bracket_succ`; the `flowBracketDelta = -1` guard ranges
    the quantifier over bracket-close positions only).  The two raw matching fields (M9 `bracket_seq`,
    M10 `bracket_map`) are *exactly* the typed-locator outputs `flowBracketBalance_matching_close_{seq,
    map}` — no successor wrapper, unlike the seq body whose close carries `.flowSequenceEnd`.  The
    depth-0 fact `balance (k+1) = 0` the M5/M8 conjuncts need is re-derived inline from `balance k = 0`
    and `flowBracketDelta .key = flowBracketDelta .value = 0`; `k + 1 < hi` from the boundary `h_tpe`
    (an opener at `k+1 = hi` would be `.flowMappingEnd`).  As on the seq side, the remaining Phase-J
    work is purely to *produce* these primitives at every nested subrange — this lemma is the joint the
    recursive producer calls once it has them.  Note a map pair `.key … .value …` has an interior
    depth-0 `.value`, so the whole pair is NOT an `EntryUnit`: the alternation lives in the primitives,
    not in a single per-item successor as on the seq side. -/
theorem mapBodyProps_assemble (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_hi_sz : hi ≤ tokens.size)
    (h_tpe : tokens[hi]!.val = .flowMappingEnd)
    (h_outer_bal : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt_interior : WellTyped ((tokens.toList.take hi).drop lo))
    (h_key_start : lo < hi → tokens[lo]!.val = .key)
    (h_after_fe : ∀ k, lo ≤ k → k < hi →
      flowBracketBalance tokens lo k = 0 →
      tokens[k]!.val = .flowEntry →
      k + 1 ≤ hi ∧ tokens[k + 1]!.val = .key)
    (h_key_content : ∀ k, lo ≤ k → k < hi →
      flowBracketBalance tokens lo k = 0 →
      tokens[k]!.val = .key →
      k + 1 < hi ∧ isFlowContentStart tokens[k + 1]!.val)
    (h_key_scalar_value : ∀ k, lo ≤ k → k < hi →
      flowBracketBalance tokens lo k = 0 →
      tokens[k]!.val = .key →
      (∃ c s, tokens[k + 1]!.val = .scalar c s) →
      k + 2 < hi ∧ tokens[k + 2]!.val = .value)
    (h_value_content : ∀ k, lo ≤ k → k < hi →
      flowBracketBalance tokens lo k = 0 →
      tokens[k]!.val = .value →
      k + 1 < hi ∧ isFlowContentStart tokens[k + 1]!.val)
    (h_value_scalar_succ : ∀ k, lo ≤ k → k < hi →
      flowBracketBalance tokens lo k = 0 →
      tokens[k]!.val = .value →
      (∃ c s, tokens[k + 1]!.val = .scalar c s) →
      k + 2 ≤ hi ∧
      (tokens[k + 2]!.val = .flowEntry ∨
       (tokens[k + 2]!.val = .flowMappingEnd ∧ k + 2 = hi)))
    (h_key_bracket_succ : ∀ k j, lo ≤ k → k < hi →
      flowBracketBalance tokens lo k = 0 →
      tokens[k]!.val = .key →
      k + 1 < j → j < hi →
      flowBracketDelta tokens[j]!.val = -1 →
      flowBracketBalance tokens lo (j + 1) = 0 →
      j + 1 < hi ∧ tokens[j + 1]!.val = .value)
    (h_value_bracket_succ : ∀ k j, lo ≤ k → k < hi →
      flowBracketBalance tokens lo k = 0 →
      tokens[k]!.val = .value →
      k + 1 < j → j < hi →
      flowBracketDelta tokens[j]!.val = -1 →
      flowBracketBalance tokens lo (j + 1) = 0 →
      j + 1 ≤ hi ∧
      (tokens[j + 1]!.val = .flowEntry ∨
       (tokens[j + 1]!.val = .flowMappingEnd ∧ j + 1 = hi))) :
    MapBodyProps tokens lo hi := by
  -- A depth-0 `.key`/`.value` at `k` (balance 0, delta 0) keeps balance 0 at `k+1`, and the opener
  -- that follows cannot sit at `hi` (that slot is `.flowMappingEnd` by `h_tpe`).  Both M5 and M8
  -- need exactly these two facts before calling their conjunct, so factor them as a local lemma.
  have h_step : ∀ k, lo ≤ k → k < hi → flowBracketBalance tokens lo k = 0 →
      flowBracketDelta tokens[k]!.val = 0 →
      (tokens[k + 1]!.val = .flowSequenceStart ∨ tokens[k + 1]!.val = .flowMappingStart) →
      flowBracketBalance tokens lo (k + 1) = 0 ∧ k + 1 < hi := by
    intro k h_lo h_hi h_bal h_delta h_open
    have h_k_sz : k < tokens.size := by omega
    have h_k_lt_list : k < tokens.toList.length := by rw [Array.length_toList]; exact h_k_sz
    have h_delta0 : flowBracketDelta tokens.toList[k].val = 0 := by
      have h_eq : tokens.toList[k]'h_k_lt_list = tokens[k]! := by
        rw [getElem!_pos tokens k h_k_sz, Array.getElem_toList]
      rw [h_eq]; exact h_delta
    have h_bal1 : flowBracketBalance tokens lo (k + 1) = 0 := by
      have hc := flowBracketBalance_compose tokens lo k (k + 1) h_lo (by omega)
      rw [flowBracketBalance_single tokens k h_k_lt_list, h_delta0] at hc
      omega
    refine ⟨h_bal1, ?_⟩
    have h_ne : k + 1 ≠ hi := by
      intro h; rw [h, h_tpe] at h_open
      rcases h_open with h1 | h1 <;> exact absurd h1 (by decide)
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- M1 key_start
    exact h_key_start
  · -- M2 after_fe
    exact h_after_fe
  · -- M3 key_content
    exact h_key_content
  · -- M4 key_scalar_value
    exact h_key_scalar_value
  · -- M5 key_bracket_value — depth-shift + `map_key_bracket_conjunct`
    intro k h_lo h_hi h_bal h_key h_open
    have h_delta : flowBracketDelta tokens[k]!.val = 0 := by rw [h_key]; rfl
    obtain ⟨h_k1_depth, h_k1_hi⟩ := h_step k h_lo h_hi h_bal h_delta h_open
    exact map_key_bracket_conjunct tokens lo hi k (by omega) h_k1_hi h_hi_sz
      h_k1_depth h_open h_outer_bal h_dyck h_wt_interior
      (fun j hkj hjhi hd hb => h_key_bracket_succ k j h_lo h_hi h_bal h_key hkj hjhi hd hb)
  · -- M6 value_content
    exact h_value_content
  · -- M7 value_scalar_succ
    exact h_value_scalar_succ
  · -- M8 value_bracket_succ — depth-shift + `map_value_bracket_conjunct`
    intro k h_lo h_hi h_bal h_val h_open
    have h_delta : flowBracketDelta tokens[k]!.val = 0 := by rw [h_val]; rfl
    obtain ⟨h_k1_depth, h_k1_hi⟩ := h_step k h_lo h_hi h_bal h_delta h_open
    exact map_value_bracket_conjunct tokens lo hi k (by omega) h_k1_hi h_hi_sz
      h_k1_depth h_open h_outer_bal h_dyck h_wt_interior
      (fun j hkj hjhi hd hb => h_value_bracket_succ k j h_lo h_hi h_bal h_val hkj hjhi hd hb)
  · -- M9 bracket_seq — exactly the typed locator
    intro k h_lo h_hi h_bal h_open
    exact flowBracketBalance_matching_close_seq tokens lo k hi h_lo h_hi h_hi_sz
      h_bal h_open h_outer_bal h_dyck h_wt_interior
  · -- M10 bracket_map — exactly the typed locator
    intro k h_lo h_hi h_bal h_open
    exact flowBracketBalance_matching_close_map tokens lo k hi h_lo h_hi h_hi_sz
      h_bal h_open h_outer_bal h_dyck h_wt_interior

/-- **Windowed-`SafeBody` → `MapBodyProps` consumer joint** (Phase J, map side).  The map-side
    analog of `seqBodyProps_of_windowed_safebody`.  Given a guarded balanced flow-MAPPING subrange
    `[lo, hi)` (close `.flowMappingEnd`, total balance `0`, Dyck prefixes, interior `WellTyped`)
    together with the map producer's *deliverable* — the windowed `SafeBody (· = .key)
    ((tokens.toList.take hi).drop lo)` (`emitPairList_scans_safebody` emits exactly this: a body of
    `.key`-headed pair entries separated by depth-0 `.flowEntry`) — plus the six inner pair-level
    primitives of the depth-0 key/value alternation, assemble the full `MapBodyProps tokens lo hi`.

    Unlike the seq side there is no `SafeBodyUnit`: a map *pair* `.key … .value …` carries an
    interior depth-0 `.value`, so the whole pair is NOT an `EntryUnit` and the windowed `SafeBody`
    constrains only the *outer* (pair-boundary) structure.  It therefore discharges exactly the two
    boundary primitives `mapBodyProps_assemble` keys on the body shape: **M1 `key_start`** via
    `SafeBody.head_Q` (the windowed body's head is a `.key`) and **M2 `after_fe`** via
    `SafeBody_array_flowEntry_window` at `Q := (· = .key)` (a depth-0 `.flowEntry` separator is
    followed by a `.key`).  The remaining six (M3 `key_content`, M4 `key_scalar_value`, M6
    `value_content`, M7 `value_scalar_succ`, M5 `key_bracket_succ`, M8 `value_bracket_succ`) are the
    pair-INTERIOR alternation, invisible to the `.key`-headed `SafeBody`, so they remain inputs — the
    map-side analog of "produce the windowed `SafeBody` + content-start head" reduced to "produce the
    windowed `SafeBody (· = .key)` + the six interior pair primitives".  The glue is the same as on
    the seq side: the `getElem!`↔`getElem` bridge and the windowed-slice head index `((·).drop lo)[0]
    = tokens[lo]`. -/
theorem mapBodyProps_of_windowed_safebody (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_hi_sz : hi ≤ tokens.size)
    (h_tpe : tokens[hi]!.val = .flowMappingEnd)
    (h_outer_bal : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt_interior : WellTyped ((tokens.toList.take hi).drop lo))
    (h_safe : SafeBody (fun t => t = .key) ((tokens.toList.take hi).drop lo))
    (h_key_content : ∀ k, lo ≤ k → k < hi →
      flowBracketBalance tokens lo k = 0 →
      tokens[k]!.val = .key →
      k + 1 < hi ∧ isFlowContentStart tokens[k + 1]!.val)
    (h_key_scalar_value : ∀ k, lo ≤ k → k < hi →
      flowBracketBalance tokens lo k = 0 →
      tokens[k]!.val = .key →
      (∃ c s, tokens[k + 1]!.val = .scalar c s) →
      k + 2 < hi ∧ tokens[k + 2]!.val = .value)
    (h_value_content : ∀ k, lo ≤ k → k < hi →
      flowBracketBalance tokens lo k = 0 →
      tokens[k]!.val = .value →
      k + 1 < hi ∧ isFlowContentStart tokens[k + 1]!.val)
    (h_value_scalar_succ : ∀ k, lo ≤ k → k < hi →
      flowBracketBalance tokens lo k = 0 →
      tokens[k]!.val = .value →
      (∃ c s, tokens[k + 1]!.val = .scalar c s) →
      k + 2 ≤ hi ∧
      (tokens[k + 2]!.val = .flowEntry ∨
       (tokens[k + 2]!.val = .flowMappingEnd ∧ k + 2 = hi)))
    (h_key_bracket_succ : ∀ k j, lo ≤ k → k < hi →
      flowBracketBalance tokens lo k = 0 →
      tokens[k]!.val = .key →
      k + 1 < j → j < hi →
      flowBracketDelta tokens[j]!.val = -1 →
      flowBracketBalance tokens lo (j + 1) = 0 →
      j + 1 < hi ∧ tokens[j + 1]!.val = .value)
    (h_value_bracket_succ : ∀ k j, lo ≤ k → k < hi →
      flowBracketBalance tokens lo k = 0 →
      tokens[k]!.val = .value →
      k + 1 < j → j < hi →
      flowBracketDelta tokens[j]!.val = -1 →
      flowBracketBalance tokens lo (j + 1) = 0 →
      j + 1 ≤ hi ∧
      (tokens[j + 1]!.val = .flowEntry ∨
       (tokens[j + 1]!.val = .flowMappingEnd ∧ j + 1 = hi))) :
    MapBodyProps tokens lo hi := by
  refine mapBodyProps_assemble tokens lo hi h_hi_sz h_tpe h_outer_bal h_dyck h_wt_interior
    ?_ ?_ h_key_content h_key_scalar_value h_value_content h_value_scalar_succ
    h_key_bracket_succ h_value_bracket_succ
  · -- M1 `key_start` ← `SafeBody.head_Q` (the windowed body's head is a `.key`)
    intro h_lo_hi
    have h_lo_sz : lo < tokens.size := Nat.lt_of_lt_of_le h_lo_hi h_hi_sz
    obtain ⟨hl, hQ⟩ := h_safe.head_Q
    rw [getElem!_pos tokens lo h_lo_sz]
    have h_get : (((tokens.toList.take hi).drop lo)[0]'hl).val = (tokens[lo]'h_lo_sz).val := by
      rw [List.getElem_drop, List.getElem_take, Array.getElem_toList]
      congr 2
    rw [← h_get]; exact hQ
  · -- M2 `after_fe` ← `SafeBody_array_flowEntry_window` at `Q := (· = .key)`
    intro k h_lo h_klt h_bal h_fe
    have hk_sz : k < tokens.size := Nat.lt_of_lt_of_le h_klt h_hi_sz
    rw [getElem!_pos tokens k hk_sz] at h_fe
    obtain ⟨hk1, hQ⟩ :=
      SafeBody_array_flowEntry_window tokens lo hi h_hi_sz h_safe k h_lo h_klt h_fe h_bal
    have hk1_sz : k + 1 < tokens.size := Nat.lt_of_lt_of_le hk1 h_hi_sz
    refine ⟨Nat.le_of_lt hk1, ?_⟩
    rw [getElem!_pos tokens (k + 1) hk1_sz]
    exact hQ

/-- Token structure of `scanFiltered ("[" ++ emitList items ++ "]")` for non-empty items.
    Establishes boundary tokens, body token patterns, and `parseNode` success within
    the flow sequence body.

    Requires `EmitScansInFlow` for each item to construct the scanner chain. -/
theorem scanFiltered_emitSeq_nonempty_structure
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w) :
    tokens.size ≥ 5 ∧
    tokens[0]!.val = .streamStart ∧
    tokens[tokens.size - 1]!.val = .streamEnd ∧
    tokens[1]!.val = .flowSequenceStart ∧
    tokens[tokens.size - 2]!.val = .flowSequenceEnd ∧
    ((∃ c s, tokens[2]!.val = .scalar c s) ∨
     tokens[2]!.val = .flowSequenceStart ∨
     tokens[2]!.val = .flowMappingStart) ∧
    (∀ k, 2 ≤ k → k < tokens.size - 2 →
        tokens[k]!.val = .flowEntry →
        flowBracketBalance tokens 2 k = 0 →
        k + 1 ≤ tokens.size - 2 ∧
        ((∃ c s, tokens[k + 1]!.val = .scalar c s) ∨
         tokens[k + 1]!.val = .flowSequenceStart ∨
         tokens[k + 1]!.val = .flowMappingStart)) ∧
    -- [NEW] Bracket structure of the body, threaded from `WellBracketed block`: the
    -- inclusive interior `[2, tokens.size-2)` is balanced (outer balance 0) and every
    -- prefix from 2 is ≥ 0 (Dyck) — the two hypotheses the dispatcher instantiation and
    -- `flowBracketBalance_matching_close` consume to produce `FlowSubrangesOk`.
    flowBracketBalance tokens 2 (tokens.size - 2) = 0 ∧
    (∀ k, 2 ≤ k → k ≤ tokens.size - 2 → flowBracketBalance tokens 2 k ≥ 0) ∧
    -- [NEW] Typed-bracket matching of the interior `[2, tokens.size-2)` (every `]` pops a `[`,
    -- every `}` pops a `{`) — threaded from `WellTyped block`.  The type half the untyped
    -- balance above discarded; the typed locator (next brick) consumes it for `bracket_seq`.
    WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2) ∧
    L4YAML.Proofs.ParserWellBehaved.ParseNodeFlowSeqOk tokens (tokens.size - 2) (4 * tokens.size + 4) 2 := by
  -- Step 1: Boundary tokens from scanFiltered_boundary_tokens
  obtain ⟨h_sz2, h_t0, h_tlast⟩ := scanFiltered_boundary_tokens _ _ h_scan
  -- ═══ Chain replay: reconstruct s₁ (after '['), s₂ (after body), s₃ (after ']') ═══
  let input := "[" ++ emit.emitList items.toList ++ "]"
  have h_toList : input.toList = '[' :: (emit.emitList items.toList).toList ++ [']'] := by
    simp only [input, String.toList_append]; rfl
  -- Open bracket → s₁
  obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
          h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, h_sk₁, h_filt₁,
          h_sync₁, _h_ska₁, _h_ssv₁⟩ :=
    scanNextToken_flow_open_init input
      ((emit.emitList items.toList).toList ++ [']']) h_toList
  -- Body scanning → s₂ (with filtered token characterization, via the SafeBody producer)
  obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂,
          h_ek₂, h_col₂, h_inflow₂, h_indent₂, _, _, _, h_stack₂, h_fmc₂,
          ⟨h_body_sz_raw, h_body_cs_raw⟩, h_body_fe_next_raw,
          h_body_outer_bal_raw, h_body_dyck_raw, h_body_wt_raw, h_body_succ_raw⟩ :=
    emitList_body_filtered_characterization items.toList h_ne
      (fun w hw => h_all_block w hw) s₁ [']']
      h_corr₁ h_inflow₁ (by rw [h_fl₁]; omega) h_indent₁ (by rw [h_col₁]; omega)
      h_ek₁ (h_line₁ ▸ h_atol₁) h_endline₁ h_sync₁
  -- Close bracket → s₃ (using _ext to get filtered token info + indents)
  obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃, h_ids₃, ⟨tok_fse, h_tok_fse_val, h_filt₃⟩⟩ :=
    scanNextToken_flow_close_seq_outermost_ext s₂ h_corr₂ h_inflow₂ h_indent₂ h_col₂
      (by rw [h_fl₂, h_fl₁]) (by rw [h_dp₂, h_dp₁])
  -- EOF + chain composition
  have h_eof : scanNextToken s₃ = .ok none := scanNextToken_eof s₃ h_peek₃
  have h_chain_all := (ScanChain.single h_snt₁).trans
    (h_chain₂.trans (ScanChain.single h_snt₃))
  -- BOM check
  have h_no_bom : (ScannerState.mk' input).peek? ≠ some '\uFEFF' := by
    have h_chars := chars_from_zero_toList input
    rw [h_toList] at h_chars
    have h_corr := initial_corr _ _ h_chars
    have ⟨h_pk, _⟩ := peek_of_chars_cons _ '['
      ((emit.emitList items.toList).toList ++ [']']) 0 h_corr
    rw [h_pk]; decide
  -- Indents chain: s₃.indents = s₀.indents = #[] (default from mk')
  have h_indents_small : s₃.indents.size ≤ 1 := by
    rw [h_ids₃, h_ids₂, h_ids₁]
    unfold ScannerState.emit ScannerState.mk'
    dsimp only []
    decide
  -- ═══ Token equation: tokens = (s₃.emit .streamEnd).tokens.filter p ═══
  let p := fun (t : Positioned YamlToken) => t.val != .placeholder
  have h_tok_eq : Scanner.scanFiltered input =
      .ok ((s₃.emit .streamEnd).tokens.filter p) :=
    scanFiltered_tokens_eq_of_chain_short_stack input _ s₃ _ rfl h_no_bom
      h_chain_all h_eof h_fl₃ h_dp₃
      (ScanChain.fuel_bound _ _ _ _ rfl h_chain_all h_eof)
      h_indents_small
  -- Extract: tokens = (s₃.emit .streamEnd).tokens.filter p
  have h_tokens_eq : tokens = (s₃.emit .streamEnd).tokens.filter p := by
    have : Scanner.scanFiltered input = .ok tokens := h_scan
    rw [h_tok_eq] at this; exact (Except.ok.inj this).symm
  -- ═══ Decompose filtered token array as: s₂_filtered ++ [flowSeqEnd, streamEnd] ═══
  -- s₃.tokens.filter p = (s₂.tokens.filter p).push tok_fse  (from _ext)
  -- (s₃.emit .streamEnd).tokens.filter p = s₃.tokens.filter p ++ [streamEnd]
  have h_emit_se_tokens : (s₃.emit .streamEnd).tokens =
      s₃.tokens.push { pos := s₃.currentPos, val := .streamEnd } := by
    unfold ScannerState.emit; rfl
  have h_final_filter : (s₃.emit .streamEnd).tokens.filter p =
      (s₃.tokens.filter p).push { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_emit_se_tokens, Array.filter_push]; rfl
  -- Combine: tokens = (s₂.filter p) ++ [tok_fse] ++ [streamEnd]
  -- i.e. tokens = ((s₂.filter p).push tok_fse).push streamEnd
  have h_tokens_decomp : tokens = ((s₂.tokens.filter p).push tok_fse).push
      { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_tokens_eq, h_final_filter, h_filt₃]
  -- ═══ Tier 1 derivations ═══
  -- h_tpe: tokens[tokens.size - 2] = tok_fse, which has val = .flowSequenceEnd
  have h_tpe : tokens[tokens.size - 2]!.val = .flowSequenceEnd := by
    rw [h_tokens_decomp]
    have h_outer_sz : (((s₂.tokens.filter p).push tok_fse).push
        { pos := s₃.currentPos, val := YamlToken.streamEnd }).size =
        (s₂.tokens.filter p).size + 2 := by simp [Array.size_push]
    rw [h_outer_sz, show (s₂.tokens.filter p).size + 2 - 2 = (s₂.tokens.filter p).size from by omega]
    rw [getElem!_pos _ _ (by omega)]
    rw [Array.getElem_push_lt (show (s₂.tokens.filter p).size <
        ((s₂.tokens.filter p).push tok_fse).size from by simp [Array.size_push])]
    rw [Array.getElem_push_eq]
    exact h_tok_fse_val
  -- ═══ Filtered prefix preservation (via ScanChain infrastructure) ═══
  -- h_filt₁ : (s₁.tokens.filter p).map (·.val) = #[.streamStart, .flowSequenceStart]
  -- Extract filtered prefix size and element values
  have h_filt₁_sz : (s₁.tokens.filter p).size = 2 := by
    have : ((s₁.tokens.filter p).map (·.val)).size = 2 := by rw [h_filt₁]; rfl
    simpa [Array.size_map] using this
  have h_filt₁_val1 : ((s₁.tokens.filter p)[1]'(by omega)).val = YamlToken.flowSequenceStart := by
    have h_len : (s₁.tokens.filter p).toList.length = 2 := by
      rw [Array.length_toList]; exact h_filt₁_sz
    have h_vals : (s₁.tokens.filter p).toList.map (·.val) =
        [YamlToken.streamStart, YamlToken.flowSequenceStart] := by
      have := congrArg Array.toList h_filt₁; simpa [Array.toList_map] using this
    obtain ⟨a, b, h_ab⟩ : ∃ a b, (s₁.tokens.filter p).toList = [a, b] := by
      match (s₁.tokens.filter p).toList, h_len with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    show (s₁.tokens.filter p).toList[1].val = YamlToken.flowSequenceStart
    simp only [h_ab, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [h_ab] at h_vals; simp at h_vals; exact h_vals.2
  -- Body chain preserves filtered prefix and grows by ≥ n₂
  obtain ⟨suffix, h_suffix⟩ : ∃ suffix, (s₂.tokens.filter p).toList =
      (s₁.tokens.filter p).toList ++ suffix :=
    ScanChain_filtered_prefix h_fmc₂ h_sk₁ (by omega) (by
      intro j hj hjsz; rw [h_sync₁] at hjsz; rw [h_fl₁] at hj; omega)
  -- n₂ ≥ 1 (body is non-empty: s₁ sees body chars, s₂ sees [']'])
  have h_n₂_pos : n₂ ≥ 1 := by
    match n₂, h_chain₂ with
    | 0, h_zero =>
      exfalso
      have h_s1_eq_s2 : s₁ = s₂ := by cases h_zero; rfl
      rw [h_s1_eq_s2] at h_corr₁
      have h_chars_eq := CharsFromOffset_unique h_corr₁.chars_from h_corr₂.chars_from
      have h_len := congrArg List.length h_chars_eq
      simp only [List.length_append] at h_len
      have h_nil : (emit.emitList items.toList).toList = [] := by
        match h_list : (emit.emitList items.toList).toList with
        | [] => rfl
        | _ :: _ => simp [h_list] at h_len
      match h_items : items.toList with
      | [] => exact absurd h_items h_ne
      | v :: vs =>
          rw [h_items] at h_nil; exact absurd h_nil (emitList_toList_ne_nil v vs)
    | _ + 1, _ => omega
  -- (s₂.tokens.filter p).size ≥ 3 — directly from the body's strict-growth witness
  -- (`h_body_sz_raw : (s₁.filter).size < (s₂.filter).size`) plus `(s₁.filter).size = 2`.
  have h_s2_filt_sz : (s₂.tokens.filter p).size ≥ 3 := by
    have hb : (s₁.tokens.filter p).size < (s₂.tokens.filter p).size := h_body_sz_raw
    rw [h_filt₁_sz] at hb; omega
  -- h_t1: peel two pushes to reach (s₂.tokens.filter p)[1], then use prefix
  have h_t1 : tokens[1]!.val = .flowSequenceStart := by
    rw [h_tokens_decomp]
    rw [getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show 1 < ((s₂.tokens.filter p).push tok_fse).size
        from by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show 1 < (s₂.tokens.filter p).size from by omega)]
    -- Goal: (s₂.tokens.filter p)[1]'_.val = .flowSequenceStart
    -- Show filtered[1] is preserved from s₁ to s₂ via ScanChain prefix
    have h1_lt_s1 : 1 < (s₁.tokens.filter p).size := by rw [h_filt₁_sz]; omega
    have h_eq : (s₂.tokens.filter p)[1]'(by omega) = (s₁.tokens.filter p)[1]'h1_lt_s1 := by
      show (s₂.tokens.filter p).toList[1]'(by rw [Array.length_toList]; omega) =
          (s₁.tokens.filter p).toList[1]'(by rw [Array.length_toList]; omega)
      simp only [h_suffix]
      exact List.getElem_append_left (by rw [Array.length_toList]; omega)
    calc ((s₂.tokens.filter p)[1]'(by omega)).val
        = ((s₁.tokens.filter p)[1]'h1_lt_s1).val := congrArg Positioned.val h_eq
      _ = .flowSequenceStart := h_filt₁_val1
  -- h_sz5: tokens.size = (s₂.filter p).size + 2 ≥ 3 + 2 = 5
  have h_sz5 : tokens.size ≥ 5 := by
    rw [h_tokens_decomp]; simp [Array.size_push]; omega
  -- ═══ Body token characterization (now from combined theorem) ═══
  -- Rename _raw variables to match expected names
  have h_body_sz := h_body_sz_raw; have h_body_cs := h_body_cs_raw
  have h_body_fe_next := h_body_fe_next_raw
  rw [h_filt₁_sz] at h_body_sz h_body_cs h_body_fe_next h_body_outer_bal_raw h_body_dyck_raw h_body_wt_raw h_body_succ_raw
  -- Helper: tokens[k]! for k < tokens.size - 2 equals (s₂.filter p)[k]
  have h_tokens_sz_eq : tokens.size - 2 = (s₂.tokens.filter p).size := by
    rw [h_tokens_decomp]; simp [Array.size_push]
  have h_tok_body (k : Nat) (h_lt : k < (s₂.tokens.filter p).size) :
      tokens[k]! = ((s₂.tokens.filter p)[k]'h_lt) := by
    rw [h_tokens_decomp, getElem!_pos _ k (by simp [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show k < ((s₂.tokens.filter p).push tok_fse).size
        from by simp [Array.size_push]; omega)]
    rw [Array.getElem_push_lt h_lt]
  have h_content0 : (∃ c s, tokens[2]!.val = .scalar c s) ∨
      tokens[2]!.val = .flowSequenceStart ∨
      tokens[2]!.val = .flowMappingStart := by
    have h_body := h_body_cs (by omega)
    rw [h_tok_body 2 (by omega)]
    exact h_body
  have h_fe_pattern : ∀ k, 2 ≤ k → k < tokens.size - 2 →
      tokens[k]!.val = .flowEntry →
      flowBracketBalance tokens 2 k = 0 →
      k + 1 ≤ tokens.size - 2 ∧
      ((∃ c s, tokens[k + 1]!.val = .scalar c s) ∨
       tokens[k + 1]!.val = .flowSequenceStart ∨
       tokens[k + 1]!.val = .flowMappingStart) := by
    intro k h_lo h_hi h_fe h_depth
    have h_k_lt : k < (s₂.tokens.filter p).size := by omega
    rw [h_tok_body k h_k_lt] at h_fe
    -- Convert flowBracketBalance from tokens to s₂.tokens.filter p
    have h_depth' : flowBracketBalance (s₂.tokens.filter p) 2 k = 0 := by
      rw [← h_tokens_sz_eq] at h_k_lt
      have : flowBracketBalance tokens 2 k = flowBracketBalance (s₂.tokens.filter p) 2 k := by
        rw [h_tokens_decomp]
        rw [flowBracketBalance_push _ _ 2 k (by simp [Array.size_push]; omega)]
        rw [flowBracketBalance_push _ _ 2 k (by omega)]
      rw [this] at h_depth; exact h_depth
    obtain ⟨h_next_lt, h_next_cs⟩ := h_body_fe_next k (by omega) h_k_lt h_fe h_depth'
    exact ⟨by omega,
           by rw [h_tok_body (k+1) (by omega)]; exact h_next_cs (by omega)⟩
  -- ═══ [NEW] Tokens-level bracket structure (push-converted from the body facts) ═══
  -- For `k ≤ (s₂.filter p).size`, the two trailing pushes (`tok_fse`, `streamEnd`) don't
  -- affect the balance on `[2, k)`, so it agrees with the body's `(s₂.filter p)` balance.
  have h_conv : ∀ k, k ≤ (s₂.tokens.filter p).size →
      flowBracketBalance tokens 2 k = flowBracketBalance (s₂.tokens.filter p) 2 k := by
    intro k hk
    rw [h_tokens_decomp]
    rw [flowBracketBalance_push _ _ 2 k (by simp [Array.size_push]; omega)]
    rw [flowBracketBalance_push _ _ 2 k (by omega)]
  have h_outer_bal : flowBracketBalance tokens 2 (tokens.size - 2) = 0 := by
    rw [h_tokens_sz_eq, h_conv (s₂.tokens.filter p).size (Nat.le_refl _)]
    exact h_body_outer_bal_raw
  have h_dyck : ∀ k, 2 ≤ k → k ≤ tokens.size - 2 → flowBracketBalance tokens 2 k ≥ 0 := by
    intro k _hk1 hk2
    rw [h_tokens_sz_eq] at hk2
    rw [h_conv k hk2]
    exact h_body_dyck_raw k _hk1 hk2
  -- [NEW] Tokens-level `WellTyped` of the interior `[2, tokens.size-2)`.  The interior slice is
  -- exactly the body block `(s₂.filter p).toList.drop 2` (the two trailing pushes `tok_fse`,
  -- `streamEnd` are dropped by `take (tokens.size - 2)`), so the body's `h_body_wt_raw` transfers.
  have h_take_eq : tokens.toList.take (tokens.size - 2) = (s₂.tokens.filter p).toList := by
    have h_sz : tokens.size - 2 = (s₂.tokens.filter p).toList.length := by
      rw [h_tokens_sz_eq, Array.length_toList]
    rw [h_sz, h_tokens_decomp, Array.toList_push, Array.toList_push, List.append_assoc,
      List.take_left]
  have h_wt_interior : WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2) := by
    rw [h_take_eq]; exact h_body_wt_raw
  -- [NEW] Tokens-level value-end successor (Part 6), push-converted from the body fact
  -- `h_body_succ_raw` exactly as `h_dyck` was from `h_body_dyck_raw`: `h_tok_body` carries the
  -- token values across the two trailing pushes (`tok_fse`, `streamEnd`) and `h_conv` carries the
  -- prefix balance.  A balanced-prefix end that is NOT a `.flowEntry` separator is an entry END —
  -- the body close (`k+1 = tokens.size - 2`) or a `.flowEntry` next.  This is the `h_succ`/
  -- `SeqBodyProps.scalar_succ` substrate the future `h_pnok` proof feeds the bracket conjuncts and
  -- the scalar-successor field.  Bound here as enablement (next sub-brick consumes it).
  have _h_body_succ : ∀ k, 2 ≤ k → k < tokens.size - 2 →
      flowBracketBalance tokens 2 (k + 1) = 0 →
      tokens[k]!.val ≠ .flowEntry →
      k + 1 = tokens.size - 2 ∨
      ∃ (h' : k + 1 < tokens.size - 2), tokens[k + 1]!.val = .flowEntry := by
    intro k h_lo h_hi h_bal h_nfe
    have h_k_lt : k < (s₂.tokens.filter p).size := by rw [← h_tokens_sz_eq]; exact h_hi
    rw [h_tok_body k h_k_lt] at h_nfe
    have h_bal' : flowBracketBalance (s₂.tokens.filter p) 2 (k + 1) = 0 := by
      rw [← h_conv (k + 1) (by omega)]; exact h_bal
    rcases h_body_succ_raw k h_lo h_k_lt h_bal' h_nfe with h_end | ⟨h', h_fe⟩
    · left; rw [h_tokens_sz_eq]; exact h_end
    · right
      refine ⟨by rw [h_tokens_sz_eq]; exact h', ?_⟩
      rw [h_tok_body (k + 1) h']; exact h_fe
  -- [NEW] Assemble the outer `SeqBodyProps tokens 2 (tokens.size - 2)` via the parametric assembler
  -- `seqBodyProps_assemble`: the outer span is the `lo = 2, hi = tokens.size - 2` instance of the
  -- universal `FlowSubrangesOk.seq`.  Every field is a projection the assembler performs off the
  -- in-scope primitives — content-start (`h_content0`, definitionally `isFlowContentStart`), the
  -- value-end successor (`_h_body_succ`), and the post-`.flowEntry` content-start (`h_fe_pattern`) —
  -- plus the bracket facts (`h_outer_bal`/`h_dyck`/`h_wt_interior`).  The value-close-guarded
  -- successor the bracket conjuncts need is re-derived inside the assembler from `_h_body_succ` +
  -- `h_tpe`.  The full Phase-J producer lifts those three primitives to every nested balanced
  -- subrange; here they hold at the outer span, so this stands as the seed/witness that the outer
  -- span itself meets the structural shape `flow_parser_ok_of_structure` consumes.
  have _h_seq_body_props : SeqBodyProps tokens 2 (tokens.size - 2) :=
    seqBodyProps_assemble tokens 2 (tokens.size - 2) (by omega) h_tpe h_outer_bal h_dyck
      h_wt_interior h_content0 _h_body_succ h_fe_pattern
  -- ═══ [NEW] Dispatcher wiring: parser-acceptance ← structural `FlowSubrangesOk` ═══
  -- `flow_parser_ok_of_structure` (the span strong-induction dispatcher in `FlowParserAcceptance`,
  -- previously a verified-but-unconsumed leaf module) turns the universal structural fact
  -- `FlowSubrangesOk tokens` — every nested balanced subrange has `SeqBodyProps`/`MapBodyProps` —
  -- into `ParseNodeFlowSeqOk`/`ParseEntryFlowMapOk` at every subrange.  Instantiating its seq half at
  -- the outer span `(2, tokens.size - 2)` discharges `h_pnok` directly from `h_subranges`, so the
  -- seq sorry no longer states a parser-EXECUTION obligation: it is now the pure STRUCTURAL residual
  -- `FlowSubrangesOk tokens` (Phase J — generalize `_h_seq_body_props` above to all subranges via the
  -- typed-locator + `WellTyped_subrange` infrastructure).  `_h_seq_body_props` is exactly its
  -- `(2, tokens.size - 2)` seq instance; the bridge from structure to parse is now fully proven.
  have h_subranges : FlowSubrangesOk tokens := sorry
  have h_pnok : L4YAML.Proofs.ParserWellBehaved.ParseNodeFlowSeqOk
      tokens (tokens.size - 2) (4 * tokens.size + 4) 2 :=
    (L4YAML.Proofs.ParserWellBehaved.flow_parser_ok_of_structure
        tokens (4 * tokens.size + 4) h_subranges).1
      2 (tokens.size - 2) (by omega) (by omega) h_tpe h_outer_bal h_t1
  exact ⟨h_sz5, h_t0, h_tlast, h_t1, h_tpe, h_content0, h_fe_pattern,
         h_outer_bal, h_dyck, h_wt_interior, h_pnok⟩

/-- Token structure of `scanFiltered ("{" ++ emitPairList pairs ++ "}")` for non-empty pairs.
    Establishes boundary tokens, body token patterns, and `parseExplicitKey`/`parseFlowMappingValue`
    success within the flow mapping body. -/
theorem scanFiltered_emitMap_nonempty_structure
    (pairs : Array (YamlValue × YamlValue)) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}") = .ok tokens)
    (h_ne : pairs.toList ≠ [])
    (h_all_k_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowSavedKeyBlock p.1)
    (h_all_v_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowBlock p.2) :
    tokens.size ≥ 7 ∧
    tokens[0]!.val = .streamStart ∧
    tokens[tokens.size - 1]!.val = .streamEnd ∧
    tokens[1]!.val = .flowMappingStart ∧
    tokens[tokens.size - 2]!.val = .flowMappingEnd ∧
    tokens[2]!.val = .key ∧
    (∀ k, 2 ≤ k → k < tokens.size - 2 →
        tokens[k]!.val = .flowEntry →
        flowBracketBalance tokens 2 k = 0 →
        k + 1 ≤ tokens.size - 2 ∧ tokens[k + 1]!.val = .key) ∧
    -- [NEW] Bracket structure of the body, threaded from `WellBracketed block`: the
    -- inclusive interior `[2, tokens.size-2)` is balanced (outer balance 0) and every
    -- prefix from 2 is ≥ 0 (Dyck) — the two hypotheses the dispatcher instantiation and
    -- `flowBracketBalance_matching_close` consume to produce `FlowSubrangesOk`.
    flowBracketBalance tokens 2 (tokens.size - 2) = 0 ∧
    (∀ k, 2 ≤ k → k ≤ tokens.size - 2 → flowBracketBalance tokens 2 k ≥ 0) ∧
    -- [NEW] Typed-bracket matching of the interior `[2, tokens.size-2)` — threaded from
    -- `WellTyped block`; the type half the untyped balance above discarded.
    WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2) ∧
    L4YAML.Proofs.ParserWellBehaved.ParseEntryFlowMapOk tokens (tokens.size - 2) (4 * tokens.size + 4) 2 := by
  -- Step 1: Boundary tokens from scanFiltered_boundary_tokens
  obtain ⟨h_sz2, h_t0, h_tlast⟩ := scanFiltered_boundary_tokens _ _ h_scan
  -- ═══ Chain replay: reconstruct s₁ (after '{'), s₂ (after body), s₃ (after '}') ═══
  let input := "{" ++ emit.emitPairList pairs.toList ++ "}"
  have h_toList : input.toList = '{' :: (emit.emitPairList pairs.toList).toList ++ ['}'] := by
    simp only [input, String.toList_append]; rfl
  -- Open brace → s₁
  obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
          h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, h_sk₁, h_filt₁,
          h_sync₁, h_ska₁, h_ssv₁⟩ :=
    scanNextToken_flow_open_mapping_init input
      ((emit.emitPairList pairs.toList).toList ++ ['}']) h_toList
  -- Body scanning → s₂ (with filtered token characterization)
  obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂,
          h_ek₂, h_col₂, h_inflow₂, h_indent₂, _, _, _, h_stack₂, h_fmc₂,
          h_n₂_ge3, ⟨h_body_sz_raw, h_body_key_raw⟩, h_body_fe_next_raw, h_body_grow,
          h_body_outer_bal_raw, h_body_dyck_raw, h_body_wt_raw⟩ :=
    emitPairList_body_filtered_characterization pairs.toList h_ne
      (fun p hp => h_all_k_block p hp) (fun p hp => h_all_v_block p hp)
      s₁ ['}']
      h_corr₁ h_inflow₁ (by rw [h_fl₁]; omega) h_indent₁ (by rw [h_col₁]; omega)
      h_ek₁ (h_line₁ ▸ h_atol₁) h_endline₁ h_ska₁ h_sync₁
  -- Close brace → s₃ (using _ext to get filtered token info + indents)
  obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃, h_ids₃, ⟨tok_fme, h_tok_fme_val, h_filt₃⟩⟩ :=
    scanNextToken_flow_close_mapping_outermost_ext s₂ h_corr₂ h_inflow₂ h_indent₂ h_col₂
      (by rw [h_fl₂, h_fl₁]) (by rw [h_dp₂, h_dp₁])
  -- EOF + chain composition
  have h_eof : scanNextToken s₃ = .ok none := scanNextToken_eof s₃ h_peek₃
  have h_chain_all := (ScanChain.single h_snt₁).trans
    (h_chain₂.trans (ScanChain.single h_snt₃))
  -- BOM check
  have h_no_bom : (ScannerState.mk' input).peek? ≠ some '\uFEFF' := by
    have h_chars := chars_from_zero_toList input
    rw [h_toList] at h_chars
    have h_corr := initial_corr _ _ h_chars
    have ⟨h_pk, _⟩ := peek_of_chars_cons _ '{'
      ((emit.emitPairList pairs.toList).toList ++ ['}']) 0 h_corr
    rw [h_pk]; decide
  -- Indents chain: s₃.indents = s₀.indents = #[] (default from mk')
  have h_indents_small : s₃.indents.size ≤ 1 := by
    rw [h_ids₃, h_ids₂, h_ids₁]
    unfold ScannerState.emit ScannerState.mk'
    dsimp only []
    decide
  -- ═══ Token equation: tokens = (s₃.emit .streamEnd).tokens.filter p ═══
  let p := fun (t : Positioned YamlToken) => t.val != .placeholder
  have h_tok_eq : Scanner.scanFiltered input =
      .ok ((s₃.emit .streamEnd).tokens.filter p) :=
    scanFiltered_tokens_eq_of_chain_short_stack input _ s₃ _ rfl h_no_bom
      h_chain_all h_eof h_fl₃ h_dp₃
      (ScanChain.fuel_bound _ _ _ _ rfl h_chain_all h_eof)
      h_indents_small
  -- Extract: tokens = (s₃.emit .streamEnd).tokens.filter p
  have h_tokens_eq : tokens = (s₃.emit .streamEnd).tokens.filter p := by
    have : Scanner.scanFiltered input = .ok tokens := h_scan
    rw [h_tok_eq] at this; exact (Except.ok.inj this).symm
  -- ═══ Decompose filtered token array as: s₂_filtered ++ [flowMapEnd, streamEnd] ═══
  have h_emit_se_tokens : (s₃.emit .streamEnd).tokens =
      s₃.tokens.push { pos := s₃.currentPos, val := .streamEnd } := by
    unfold ScannerState.emit; rfl
  have h_final_filter : (s₃.emit .streamEnd).tokens.filter p =
      (s₃.tokens.filter p).push { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_emit_se_tokens, Array.filter_push]; rfl
  have h_tokens_decomp : tokens = ((s₂.tokens.filter p).push tok_fme).push
      { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_tokens_eq, h_final_filter, h_filt₃]
  -- ═══ Tier 1 derivations ═══
  -- h_tpe: tokens[tokens.size - 2] = tok_fme, which has val = .flowMappingEnd
  have h_tpe : tokens[tokens.size - 2]!.val = .flowMappingEnd := by
    rw [h_tokens_decomp]
    have h_outer_sz : (((s₂.tokens.filter p).push tok_fme).push
        { pos := s₃.currentPos, val := YamlToken.streamEnd }).size =
        (s₂.tokens.filter p).size + 2 := by simp [Array.size_push]
    rw [h_outer_sz, show (s₂.tokens.filter p).size + 2 - 2 = (s₂.tokens.filter p).size from by omega]
    rw [getElem!_pos _ _ (by omega)]
    rw [Array.getElem_push_lt (show (s₂.tokens.filter p).size <
        ((s₂.tokens.filter p).push tok_fme).size from by simp [Array.size_push])]
    rw [Array.getElem_push_eq]
    exact h_tok_fme_val
  -- ═══ Filtered prefix preservation (via ScanChain infrastructure) ═══
  have h_filt₁_sz : (s₁.tokens.filter p).size = 2 := by
    have : ((s₁.tokens.filter p).map (·.val)).size = 2 := by rw [h_filt₁]; rfl
    simpa [Array.size_map] using this
  have h_filt₁_val1 : ((s₁.tokens.filter p)[1]'(by omega)).val = YamlToken.flowMappingStart := by
    have h_len : (s₁.tokens.filter p).toList.length = 2 := by
      rw [Array.length_toList]; exact h_filt₁_sz
    have h_vals : (s₁.tokens.filter p).toList.map (·.val) =
        [YamlToken.streamStart, YamlToken.flowMappingStart] := by
      have := congrArg Array.toList h_filt₁; simpa [Array.toList_map] using this
    obtain ⟨a, b, h_ab⟩ : ∃ a b, (s₁.tokens.filter p).toList = [a, b] := by
      match (s₁.tokens.filter p).toList, h_len with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    show (s₁.tokens.filter p).toList[1].val = YamlToken.flowMappingStart
    simp only [h_ab, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [h_ab] at h_vals; simp at h_vals; exact h_vals.2
  obtain ⟨suffix, h_suffix⟩ : ∃ suffix, (s₂.tokens.filter p).toList =
      (s₁.tokens.filter p).toList ++ suffix :=
    ScanChain_filtered_prefix h_fmc₂ h_sk₁ (by omega) (by
      intro j hj hjsz; rw [h_sync₁] at hjsz; rw [h_fl₁] at hj; omega)
  -- n₂ ≥ 1 (from n₂ ≥ 3)
  have h_n₂_pos : n₂ ≥ 1 := by omega
  -- Body adds ≥ 3 filtered tokens (Part 4 of the characterization, read off the
  -- strict-growth chain) ⟹ filtered size ≥ 5, with `(s₁.filter).size = 2`.  This
  -- replaces the former `ScanChain_filtered_grows` route, which depended on the
  -- (RESERVED-directive-unsound) `scanNextToken_filtered_grows`.
  have h_body_ge5 : (s₂.tokens.filter p).size ≥ 5 := by
    have hg : (s₁.tokens.filter p).size + 3 ≤ (s₂.tokens.filter p).size := h_body_grow
    rw [h_filt₁_sz] at hg; omega
  have h_s2_filt_sz : (s₂.tokens.filter p).size ≥ 3 := by omega
  have h_t1 : tokens[1]!.val = .flowMappingStart := by
    rw [h_tokens_decomp]
    rw [getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show 1 < ((s₂.tokens.filter p).push tok_fme).size
        from by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show 1 < (s₂.tokens.filter p).size from by omega)]
    -- Show filtered[1] is preserved from s₁ to s₂ via ScanChain prefix
    have h1_lt_s1 : 1 < (s₁.tokens.filter p).size := by rw [h_filt₁_sz]; omega
    have h_eq : (s₂.tokens.filter p)[1]'(by omega) = (s₁.tokens.filter p)[1]'h1_lt_s1 := by
      show (s₂.tokens.filter p).toList[1]'(by rw [Array.length_toList]; omega) =
          (s₁.tokens.filter p).toList[1]'(by rw [Array.length_toList]; omega)
      simp only [h_suffix]
      exact List.getElem_append_left (by rw [Array.length_toList]; omega)
    calc ((s₂.tokens.filter p)[1]'(by omega)).val
        = ((s₁.tokens.filter p)[1]'h1_lt_s1).val := congrArg Positioned.val h_eq
      _ = .flowMappingStart := h_filt₁_val1
  -- h_sz7: for map, need n₂ ≥ 5 filtered tokens (prefix 2 + suffix ≥ 3)
  -- Non-empty pair list has ≥ 1 pair. Each pair scanning produces ≥ 3 scanNextToken
  -- steps (key, value indicator, value scalar). Combined with n₂ ≥ 1, this gives
  -- filtered size ≥ 2 + n₂. For n₂ ≥ 5 we need the pair structure decomposition.
  -- ═══ Body token characterization (now from combined theorem) ═══
  -- Rename _raw variables to match expected names
  have h_body_sz := h_body_sz_raw; have h_body_key := h_body_key_raw
  have h_body_fe_next := h_body_fe_next_raw
  rw [h_filt₁_sz] at h_body_sz h_body_key h_body_fe_next h_body_outer_bal_raw h_body_dyck_raw h_body_wt_raw
  -- tokens.size - 2 = (s₂.filter p).size
  have h_tokens_sz_eq : tokens.size - 2 = (s₂.tokens.filter p).size := by
    rw [h_tokens_decomp]; simp [Array.size_push]
  -- Helper: tokens[k]! for k < tokens.size - 2 equals (s₂.filter p)[k]
  have h_tok_body (k : Nat) (h_lt : k < (s₂.tokens.filter p).size) :
      tokens[k]! = ((s₂.tokens.filter p)[k]'h_lt) := by
    rw [h_tokens_decomp, getElem!_pos _ k (by simp [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show k < ((s₂.tokens.filter p).push tok_fme).size
        from by simp [Array.size_push]; omega)]
    rw [Array.getElem_push_lt h_lt]
  have h_sz7 : tokens.size ≥ 7 := by
    rw [h_tokens_decomp]; simp [Array.size_push]
    -- tokens.size = (s₂.filter).size + 2, and (s₂.filter).size ≥ 5 (h_body_ge5)
    omega
  have h_t2_key : tokens[2]!.val = .key := by
    rw [h_tok_body 2 (by omega)]; exact h_body_key (by omega)
  have h_fe_pattern : ∀ k, 2 ≤ k → k < tokens.size - 2 →
      tokens[k]!.val = .flowEntry →
      flowBracketBalance tokens 2 k = 0 →
      k + 1 ≤ tokens.size - 2 ∧ tokens[k + 1]!.val = .key := by
    intro k h_lo h_hi h_fe h_depth
    have h_k_lt : k < (s₂.tokens.filter p).size := by omega
    rw [h_tok_body k h_k_lt] at h_fe
    -- Convert flowBracketBalance from tokens to s₂.tokens.filter p
    have h_depth' : flowBracketBalance (s₂.tokens.filter p) 2 k = 0 := by
      rw [← h_tokens_sz_eq] at h_k_lt
      have : flowBracketBalance tokens 2 k = flowBracketBalance (s₂.tokens.filter p) 2 k := by
        rw [h_tokens_decomp]
        rw [flowBracketBalance_push _ _ 2 k (by simp [Array.size_push]; omega)]
        rw [flowBracketBalance_push _ _ 2 k (by omega)]
      rw [this] at h_depth; exact h_depth
    obtain ⟨h_next_lt, h_next_key⟩ := h_body_fe_next k (by omega) h_k_lt h_fe h_depth'
    exact ⟨by omega, by rw [h_tok_body (k+1) (by omega)]; exact h_next_key (by omega)⟩
  -- Convert the body outer-balance + Dyck (at filtered `old_sz = 2`) to the tokens level:
  -- the trailing `tok_fme`/`streamEnd` pushes leave the `[2, k)` window untouched
  -- (mirrors `h_depth'` above and the seq-side `scanFiltered_emitSeq_nonempty_structure`).
  have h_conv : ∀ k, k ≤ (s₂.tokens.filter p).size →
      flowBracketBalance tokens 2 k = flowBracketBalance (s₂.tokens.filter p) 2 k := by
    intro k hk
    rw [h_tokens_decomp]
    rw [flowBracketBalance_push _ _ 2 k (by simp [Array.size_push]; omega)]
    rw [flowBracketBalance_push _ _ 2 k (by omega)]
  have h_outer_bal : flowBracketBalance tokens 2 (tokens.size - 2) = 0 := by
    rw [h_tokens_sz_eq, h_conv (s₂.tokens.filter p).size (Nat.le_refl _)]
    exact h_body_outer_bal_raw
  have h_dyck : ∀ k, 2 ≤ k → k ≤ tokens.size - 2 → flowBracketBalance tokens 2 k ≥ 0 := by
    intro k _hk1 hk2
    rw [h_tokens_sz_eq] at hk2
    rw [h_conv k hk2]
    exact h_body_dyck_raw k _hk1 hk2
  -- [NEW] Tokens-level `WellTyped` of the interior `[2, tokens.size-2)` — the interior slice
  -- equals the body block `(s₂.filter p).toList.drop 2`, so `h_body_wt_raw` transfers (mirrors
  -- the seq side).
  have h_take_eq : tokens.toList.take (tokens.size - 2) = (s₂.tokens.filter p).toList := by
    have h_sz : tokens.size - 2 = (s₂.tokens.filter p).toList.length := by
      rw [h_tokens_sz_eq, Array.length_toList]
    rw [h_sz, h_tokens_decomp, Array.toList_push, Array.toList_push, List.append_assoc,
      List.take_left]
  have h_wt_interior : WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2) := by
    rw [h_take_eq]; exact h_body_wt_raw
  -- ═══ [NEW] Dispatcher wiring (map side): parser-acceptance ← structural `FlowSubrangesOk` ═══
  -- Mirror of the seq-side reduction (commit `79350657`, Reflection 225): the span strong-induction
  -- dispatcher `flow_parser_ok_of_structure`'s `.map` half turns the universal structural fact
  -- `FlowSubrangesOk tokens` — every nested balanced subrange has `SeqBodyProps`/`MapBodyProps` —
  -- into `ParseEntryFlowMapOk` at every subrange.  Instantiating at the outer span `(2, tokens.size - 2)`
  -- discharges `h_pnok` directly from `h_subranges`, so the map sorry no longer states a
  -- parser-EXECUTION obligation: it is now the SAME pure STRUCTURAL residual `FlowSubrangesOk tokens`
  -- the seq side already carries (Phase J — produce the per-subrange `SeqBodyProps`/`MapBodyProps`).
  -- With both structure sorries now this single residual, one Phase-J producer closes both at once.
  have h_subranges : FlowSubrangesOk tokens := sorry
  have h_pnok : L4YAML.Proofs.ParserWellBehaved.ParseEntryFlowMapOk
      tokens (tokens.size - 2) (4 * tokens.size + 4) 2 :=
    (L4YAML.Proofs.ParserWellBehaved.flow_parser_ok_of_structure
        tokens (4 * tokens.size + 4) h_subranges).2
      2 (tokens.size - 2) (by omega) (by omega) h_tpe h_outer_bal h_t1
  exact ⟨h_sz7, h_t0, h_tlast, h_t1, h_tpe, h_t2_key, h_fe_pattern,
         h_outer_bal, h_dyck, h_wt_interior, h_pnok⟩


end L4YAML.Proofs.EmitterScannability
