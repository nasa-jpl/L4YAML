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
      2 (tokens.size - 2) (by omega) (by omega) h_tpe h_outer_bal
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
      2 (tokens.size - 2) (by omega) (by omega) h_tpe h_outer_bal
  exact ⟨h_sz7, h_t0, h_tlast, h_t1, h_tpe, h_t2_key, h_fe_pattern,
         h_outer_bal, h_dyck, h_wt_interior, h_pnok⟩


end L4YAML.Proofs.EmitterScannability
