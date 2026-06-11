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

/-- **Balance projection (seq side, entry level).**  A `RecSeqEntry` is in particular
    `WellBracketed` — its bracket balance returns to `0` at the end and stays `≥ 0` throughout.
    The mirror of `RecSeqEntry.toEntrySafe` reading `wrap_{seq,map}_block`'s `.1` (the
    `WellBracketed` half) instead of `.2` (the `EntrySafe` half); the `scalar` leaf is the
    delta-`0` singleton.  This is the navigation invariant the *locate* needs: matching a guarded
    balanced subrange to an entry is a balance argument (the matching close of a depth-0 opener is
    the entry's last token), and the descent into a nested entry's interior needs that interior's
    own `WellBracketed` — which only the deliverable's structure can supply per sub-part, never a
    single global hypothesis. -/
theorem RecSeqEntry.toWellBracketed {e : List (Positioned YamlToken)}
    (h : RecSeqEntry e) : WellBracketed e := by
  cases h with
  | scalar t c s ht => exact WellBracketed_singleton_delta_zero t (ht ▸ flowBracketDelta_scalar c s)
  | seqEmpty op cl h_op h_cl => exact (wrap_seq_block op cl [] h_op h_cl WellBracketed_nil).1
  | seq op cl interior h_op h_cl h_wb _ => exact (wrap_seq_block op cl interior h_op h_cl h_wb).1
  | map op cl interior h_op h_cl h_wb => exact (wrap_map_block op cl interior h_op h_cl h_wb).1

/-- **Balance projection (seq side, body level).**  A `RecSeqBody` is in particular
    `WellBracketed`: each entry is `WellBracketed` (`RecSeqEntry.toWellBracketed`) and the
    depth-`0` `.flowEntry` separators carry delta `0`, so `WellBracketed_append` +
    `WellBracketed_cons_delta_zero` chain the segments.  Term-mode structural recursion on the
    `RecSeqBody` argument, exactly as `RecSeqBody.toSafeBody`; completes the projection family
    (`SafeBody` / `SafeBodyUnit` / `WellBracketed`), so the descent-locator can recover the
    untyped-balance invariant at *any* sub-body it descends into, not just the outer one. -/
theorem RecSeqBody.toWellBracketed : {l : List (Positioned YamlToken)} →
    RecSeqBody l → WellBracketed l
  | _, .single e _ h_e _ => h_e.toWellBracketed
  | _, .cons e fe rest _ h_e _ h_fe h_rest =>
      WellBracketed_append e (fe :: rest) h_e.toWellBracketed
        (WellBracketed_cons_delta_zero fe rest (h_fe ▸ flowBracketDelta_flowEntry)
          h_rest.toWellBracketed)

/-- **Entry-descend LEAF** — `(i'-b-B2c-nested-project)`, the matched-entry extraction of the
    position-keyed root-`RecSeqBody` projection.  When a recursive seq entry `e` is shaped as a
    flow sequence `op :: (interior ++ [cl])` whose opener is a `.flowSequenceStart` and whose
    `interior` is nonempty, the entry MUST be the `seq` constructor (not `scalar`, `seqEmpty`, or
    `map`), so its stored `h_rec : RecSeqBody interior` is recoverable directly.

    This is the leaf of `rec_seq_body_nested_project`'s two-dimensional descent: the spine-walk
    (templated on `SafeBody_flowEntry_zero_balance`'s `pbalance`-`take` trichotomy) locates the
    entry whose token span is the located nested seq `[p, j]`; THIS lemma reads off that entry's
    interior body.  The three non-`seq` constructors are ruled out structurally:
    * `scalar` — `e = [t]` has length `1`, but `op :: (interior ++ [cl])` has length `≥ 2`;
    * `seqEmpty` — its `interior` is `[]`, contradicting `h_int_ne`;
    * `map` — its opener is `.flowMappingStart`, contradicting `.flowSequenceStart`.
    The shape match uses cons-injectivity (`op = op'`) and append-singleton injectivity
    (`interior = int'`, via reversal). -/
theorem recseqentry_seq_extract {e : List (Positioned YamlToken)}
    (h : RecSeqEntry e) (op cl : Positioned YamlToken) (interior : List (Positioned YamlToken))
    (h_shape : e = op :: (interior ++ [cl]))
    (h_open : op.val = .flowSequenceStart) (h_int_ne : interior ≠ []) :
    RecSeqBody interior := by
  cases h with
  | scalar t c s ht =>
      -- `e = [t]` has length 1; the shape forces length `≥ 2`.
      exfalso
      have hlen : ([t] : List (Positioned YamlToken)).length = (op :: (interior ++ [cl])).length :=
        congrArg List.length h_shape
      simp [List.length_append] at hlen
  | seqEmpty op' cl' h_op' h_cl' =>
      -- `interior` would be `[]`, contradicting `h_int_ne`.
      exfalso
      -- `h_shape : op' :: ([] ++ [cl']) = op :: (interior ++ [cl])`.
      have h_tail : ([] : List (Positioned YamlToken)) ++ [cl'] = interior ++ [cl] :=
        (List.cons.inj h_shape).2
      have hr : cl' :: ([] : List (Positioned YamlToken)).reverse = cl :: interior.reverse := by
        simpa [List.reverse_append] using congrArg List.reverse h_tail
      exact h_int_ne (List.reverse_inj.mp (List.cons.inj hr).2.symm)
  | seq op' cl' int' h_op' h_cl' h_wb' h_rec' =>
      -- The `seq` case: match the interiors and return the stored `h_rec`.
      -- `h_shape : op' :: (int' ++ [cl']) = op :: (interior ++ [cl])`.
      have h_tail : int' ++ [cl'] = interior ++ [cl] := (List.cons.inj h_shape).2
      have hr : cl' :: int'.reverse = cl :: interior.reverse := by
        simpa [List.reverse_append] using congrArg List.reverse h_tail
      have h_int : interior = int' := (List.reverse_inj.mp (List.cons.inj hr).2).symm
      rw [h_int]; exact h_rec'
  | map op' cl' int' h_op' h_cl' h_wb' =>
      -- The opener would be `.flowMappingStart`, contradicting `h_open`.
      exfalso
      have h_op_eq : op' = op := (List.cons.inj h_shape).1
      rw [← h_op_eq, h_op'] at h_open
      exact absurd h_open (by simp)

/-- **Head-entry slice fact** — the pure `List` core of the emission-spine-walk locator's LEAF
    (`(i'-b-B2c-nested-fbc-emission-locator)`, R350).  Given the navigator's offset-slice invariant
    `(L.take H).drop off = e ++ rest` (the current body is `tokens` sliced at base `off`, with the head
    entry `e` a prefix) and the fit bound `off + e.length ≤ H`, the head-entry window
    `(L.take (off + e.length)).drop off` equals `e` exactly.  No balance — `List.take_take` re-bases the
    outer cut to `H`, `List.drop_take` swaps the order, and `List.take_append_of_le_length` reads off the
    prefix.  This is the `(take (b+1)).drop lo = op :: (interior ++ [cl])` window identity the assembler
    `nestedSeq_safeBodyUnit_of_locator` consumes, with `lo = off`, `b + 1 = off + e.length`. -/
theorem head_entry_slice (L : List (Positioned YamlToken)) (off H : Nat)
    (e rest : List (Positioned YamlToken))
    (h_body : (L.take H).drop off = e ++ rest) (h_le : off + e.length ≤ H) :
    (L.take (off + e.length)).drop off = e := by
  have h1 : L.take (off + e.length) = (L.take H).take (off + e.length) := by
    rw [List.take_take]; congr 1; omega
  rw [h1, List.drop_take, h_body, List.take_append_of_le_length (by omega)]; simp

/-- **LEAF case of the emission-spine-walk locator** — `(i'-b-B2c-nested-fbc-emission-locator-author)`,
    R350.  The single move of the bottom-up `body.length` navigator that PRODUCES the deliverable (the
    descend/advance moves only re-base and recurse).  When the navigator's current `RecSeqBody body` is
    sliced from `tokens` at base offset `off` (`body = (take H).drop off`, fitting the window via
    `off + body.length ≤ H`) and its HEAD entry is a nested seq block `op :: (interior ++ [cl])` — so the
    target interior window `[off+1, b]` IS this entry (the LEAF fires at `a = off+1`) — produce the
    `locator` existential `nestedSeq_safeBodyUnit_of_locator` consumes: the entry `RecSeqEntry`, its
    opener, nonempty interior, and the window identity `(take (b+1)).drop off = op :: (interior ++ [cl])`.
    The `RecSeqEntry` is `h_entry` directly; the window identity is `head_entry_slice` (a `List` slice
    fact, no balance — balance is demoted to which-entry CORRECTNESS, R350); the bounds `lo+1 = a` and
    `a ≤ b` are pure length arithmetic (`e.length = interior.length + 2 ≥ 2`).  Verified-but-unconsumed
    until the `Nat.strongRecOn` wrapper threads the descend/advance re-base steps into it. -/
theorem nestedSeq_recseqentry_locate_leaf
    (tokens : Array (Positioned YamlToken))
    (body rest interior : List (Positioned YamlToken))
    (op cl : Positioned YamlToken)
    (off H a b : Nat)
    (h_slice : body = (tokens.toList.take H).drop off)
    (h_bound : off + body.length ≤ H)
    (h_prefix : body = (op :: (interior ++ [cl])) ++ rest)
    (h_entry : RecSeqEntry (op :: (interior ++ [cl])))
    (h_open : op.val = .flowSequenceStart)
    (h_int_ne : interior ≠ [])
    (h_a : a = off + 1)
    (h_b : b = off + (op :: (interior ++ [cl])).length - 1) :
    ∃ lo op' cl' interior', lo + 1 = a ∧ a ≤ b ∧
      RecSeqEntry (op' :: (interior' ++ [cl'])) ∧
      op'.val = .flowSequenceStart ∧ interior' ≠ [] ∧
      (tokens.toList.take (b + 1)).drop lo = op' :: (interior' ++ [cl']) := by
  refine ⟨off, op, cl, interior, by omega, ?_, h_entry, h_open, h_int_ne, ?_⟩
  · -- a ≤ b : `e.length = interior.length + 2 ≥ 2`, pure length arithmetic
    simp only [List.length_cons, List.length_append, List.length_cons, List.length_nil] at h_b
    omega
  · -- window identity via `head_entry_slice`
    have h_ebody : (op :: (interior ++ [cl])).length ≤ body.length := by
      rw [h_prefix, List.length_append]; omega
    have h_le : off + (op :: (interior ++ [cl])).length ≤ H := by omega
    have h_body' : (tokens.toList.take H).drop off = (op :: (interior ++ [cl])) ++ rest := by
      rw [← h_slice, h_prefix]
    have h_slc := head_entry_slice tokens.toList off H (op :: (interior ++ [cl])) rest h_body' h_le
    have h_bplus1 : b + 1 = off + (op :: (interior ++ [cl])).length := by
      simp only [List.length_cons, List.length_append, List.length_cons, List.length_nil] at h_b ⊢
      omega
    rw [h_bplus1]; exact h_slc

/-- **DESCEND re-base of the emission-spine-walk locator** — `(i'-b-B2c-nested-fbc-emission-locator-
    descend)`, R353.  When the navigator's current `RecSeqBody body` (sliced from `tokens` at base `off`
    with `body = (take H).drop off`) has a nested-seq HEAD entry `op :: (interior ++ [cl])` and the
    target window start `a` lands strictly INSIDE it (`off+1 < a < off + e.length`), the recursion
    DESCENDS into the entry's stored interior `RecSeqBody interior` (the `seq.h_rec` field) at the new
    base `off+1`.  This lemma re-establishes the navigator's slice invariant at the descended base: the
    interior re-slices to the window `[off+1, off+1+interior.length)`, with the new right cut shrunk to
    the interior's far edge.  PURE drop-algebra (no balance): drop one more past the opener
    (`List.drop_drop`) re-bases the parent tail to `interior ++ ([cl] ++ rest)`, then `head_entry_slice`
    re-cuts to the interior exactly.  The fit bound `off+1+interior.length ≤ H` comes from `h_bound`
    (`off + body.length ≤ H` with `body.length = interior.length + 2 + rest.length`).
    Verified-but-unconsumed until the `Nat.strongRecOn` wrapper threads it into the recursion. -/
theorem nestedSeq_recseqentry_locate_descend
    (tokens : Array (Positioned YamlToken))
    (body rest interior : List (Positioned YamlToken))
    (op cl : Positioned YamlToken)
    (off H : Nat)
    (h_slice : body = (tokens.toList.take H).drop off)
    (h_bound : off + body.length ≤ H)
    (h_prefix : body = (op :: (interior ++ [cl])) ++ rest) :
    interior = (tokens.toList.take (off + 1 + interior.length)).drop (off + 1) := by
  -- Re-base the parent tail one step past the opener: drop (off+1) = interior ++ ([cl] ++ rest).
  have h_body : (tokens.toList.take H).drop (off + 1) = interior ++ ([cl] ++ rest) := by
    rw [← List.drop_drop, ← h_slice, h_prefix]; simp [List.append_assoc]
  -- The fit bound at the descended base, from `h_bound` and the prefix length.
  have h_le : off + 1 + interior.length ≤ H := by
    rw [h_prefix] at h_bound
    simp only [List.length_cons, List.length_append, List.length_cons, List.length_nil] at h_bound
    omega
  -- `head_entry_slice` re-cuts the interior exactly (no balance).
  exact (head_entry_slice tokens.toList (off + 1) H interior ([cl] ++ rest) h_body h_le).symm

/-- **ADVANCE re-base of the emission-spine-walk locator** — `(i'-b-B2c-nested-fbc-emission-locator-
    advance)`, R353.  When the navigator's current `RecSeqBody body = e ++ fe :: rest` (a `cons` node,
    sliced at base `off`) has its target window start `a` PAST the head entry (`off + e.length < a`),
    the recursion ADVANCES to the tail `RecSeqBody rest` (the `cons.h_rest` field) at the new base
    `off + e.length + 1` — the `+1` skips the depth-`0` `.flowEntry` separator `fe`.  This lemma
    re-establishes the slice invariant at the advanced base, keeping the SAME right cut `H` (the tail is
    still bounded by the enclosing close).  PURE drop-algebra (no balance): drop `e.length + 1` past the
    entry-plus-separator (`List.drop_drop` + `List.drop_append_of_le_length`) lands exactly on `rest`.
    Verified-but-unconsumed until the `Nat.strongRecOn` wrapper threads it into the recursion. -/
theorem nestedSeq_recseqentry_locate_advance
    (tokens : Array (Positioned YamlToken))
    (body rest e : List (Positioned YamlToken))
    (fe : Positioned YamlToken)
    (off H : Nat)
    (h_slice : body = (tokens.toList.take H).drop off)
    (h_prefix : body = e ++ fe :: rest) :
    rest = (tokens.toList.take H).drop (off + e.length + 1) := by
  have h1 : (tokens.toList.take H).drop (off + e.length + 1)
      = ((tokens.toList.take H).drop off).drop (e.length + 1) := by
    rw [List.drop_drop, Nat.add_assoc]
  rw [h1, ← h_slice, h_prefix,
      show (e ++ fe :: rest).drop (e.length + 1)
          = ((e ++ fe :: rest).drop e.length).drop 1 from by rw [List.drop_drop],
      List.drop_append_of_le_length (Nat.le_refl _)]
  simp

/-- **Opener-headed entry interior floor** — every `RecSeqEntry` keeps its prefix balance `≥ 1`
    strictly inside the entry: for `1 ≤ m < e.length`, `pbalance (e.take m) ≥ 1`.  Each constructor
    is a SINGLE bracket pair (so the opener's `+1` is never cancelled before the entry's own matching
    close, the last token) or a `scalar` (whose `1 ≤ m < 1` range is vacuous).  This is the
    structural floor `recseqbody_head_seq_project` needs to MATCH a located close `j` to the head
    entry's span by uniqueness — the located floor pins `j` from outside, this pins the entry's close
    from inside, and the two coincide.  No head hypothesis is needed: the property holds for ALL four
    constructors (the `scalar` range is empty, `seqEmpty`'s only interior cut is the lone opener). -/
theorem recseqentry_opener_interior_floor {e : List (Positioned YamlToken)}
    (h_e : RecSeqEntry e) :
    ∀ m, 1 ≤ m → m < e.length → pbalance (e.take m) ≥ 1 := by
  cases h_e with
  | scalar t c s ht =>
      intro m h1 h2
      simp only [List.length_cons, List.length_nil] at h2
      omega
  | seqEmpty op cl h_op h_cl =>
      intro m h1 h2
      simp only [List.nil_append, List.length_cons, List.length_nil] at h2
      have hm : m = 1 := by omega
      subst hm
      have h1op : (op :: ([] ++ [cl])).take 1 = [op] := by simp
      rw [h1op, pbalance_singleton, h_op]
      decide
  | seq op cl interior h_op h_cl h_wb h_rec =>
      intro m h1 h2
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hm' : m' ≤ interior.length := by
        simp only [List.length_cons, List.length_append, List.length_nil] at h2; omega
      rw [List.take_succ_cons, pbalance_cons, h_op, flowBracketDelta_flowSequenceStart,
          List.take_append_of_le_length hm']
      have := h_wb.2 m'
      omega
  | map op cl interior h_op h_cl h_wb =>
      intro m h1 h2
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hm' : m' ≤ interior.length := by
        simp only [List.length_cons, List.length_append, List.length_nil] at h2; omega
      rw [List.take_succ_cons, pbalance_cons, h_op, flowBracketDelta_flowMappingStart,
          List.take_append_of_le_length hm']
      have := h_wb.2 m'
      omega

/-- A `RecSeqBody` exposes its HEAD entry: a nonempty `RecSeqEntry` prefix with a content-start
    head, shared by both constructors (`single`/`cons`).  Collapses the body case split for the
    head-keyed projection — the head entry `e` is the same `l.take e.length` either way. -/
theorem recseqbody_head_entry {l : List (Positioned YamlToken)} (h : RecSeqBody l) :
    ∃ (e : List (Positioned YamlToken)) (h_ne : e ≠ []),
      RecSeqEntry e ∧ ContentStartTok (e.head h_ne).val ∧ e = l.take e.length := by
  cases h with
  | single _ent h_ne h_e h_head =>
      -- the body window `l` IS the single entry (its bare-var index unified with `l`).
      refine ⟨l, h_ne, h_e, h_head, ?_⟩; rw [List.take_length]
  | cons ent fe rest h_ne h_e h_head h_fe h_rest =>
      refine ⟨ent, h_ne, h_e, h_head, ?_⟩; rw [List.take_left]

/-- **Direct-head seq projection** — `(i'-b-B2c-nested-project)`, the DESCENT-FREE base case (the
    `[[1, 2], 9]` move, R330) of the position-keyed root-`RecSeqBody` projection.  When the located
    enclosing seq opener `p` coincides with the window base `lo` (the located seq IS the head entry),
    the head entry's stored interior `RecSeqBody` is recoverable WITHOUT any spine-walk or recursion.

    The proof matches the located close `j` to the head entry `e`'s structural span by a TWO-SIDED
    bracket-matching uniqueness: the located floor (`h_floor`, `≥ 1` over `(lo, j]`) forbids the
    balance dropping to `0` before `j`, and the entry's own interior floor
    (`recseqentry_opener_interior_floor`, `≥ 1` strictly inside `e`) forbids it before the structural
    close — so the unique first-return `j + 1 = lo + e.length` (`h_uniq`).  Then `e` is the token
    slice `[lo, j]`, its stored interior is exactly `(tokens.toList.take j).drop (lo + 1)` (pure
    `take`/`drop` algebra), and the non-`seq` constructors fall to length (`scalar`/`seqEmpty`) or the
    `.flowSequenceStart` head (`map`).  Verified-but-unconsumed leaf (R225): the recursion's ADVANCE
    and DESCEND arms re-base `lo` and recurse on `rest` / the entry's stored interior, bottoming out
    here; the matching template is `recseqentry_seq_extract` (R329), the measure `body.length` with a
    trivial `decreasing_by` (R330). -/
theorem recseqbody_head_seq_project
    (tokens : Array (Positioned YamlToken)) (lo H j : Nat)
    (h_body : RecSeqBody ((tokens.toList.take H).drop lo))
    (h_open : tokens[lo]!.val = .flowSequenceStart)
    (h_lo1_j : lo + 1 < j) (h_j_H : j < H) (h_H_sz : H ≤ tokens.size)
    (h_jclose : tokens[j]!.val = .flowSequenceEnd)
    (h_inner : flowBracketBalance tokens (lo + 1) j = 0)
    (h_floor : ∀ i, lo < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) :
    RecSeqBody ((tokens.toList.take j).drop (lo + 1)) := by
  -- Size facts.
  have h_tl_len : tokens.toList.length = tokens.size := Array.length_toList
  have h_lo_lt_j : lo < j := by omega
  have h_lo_sz : lo < tokens.size := by omega
  have h_j_sz : j < tokens.size := by omega
  have h_lo_len : lo < tokens.toList.length := by rw [h_tl_len]; exact h_lo_sz
  have h_j_len : j < tokens.toList.length := by rw [h_tl_len]; exact h_j_sz
  -- Head entry `e` of the body window.
  obtain ⟨e, h_ne, h_e, _h_head, h_prefix0⟩ := recseqbody_head_entry h_body
  have h_e_ne_len : 0 < e.length := List.length_pos_iff.mpr h_ne
  -- `e` is the leading `e.length` tokens of the window — drop the outer `take H` truncation.
  have h_body_len : ((tokens.toList.take H).drop lo).length = H - lo := by
    rw [List.length_drop, List.length_take, h_tl_len, Nat.min_eq_left h_H_sz]
  have h_elen_le : e.length ≤ H - lo := by
    have hc := congrArg List.length h_prefix0
    rw [List.length_take, h_body_len] at hc; omega
  have h_eslice : e = (tokens.toList.drop lo).take e.length := by
    have h1 : ((tokens.toList.take H).drop lo).take e.length
        = (tokens.toList.drop lo).take e.length := by
      rw [List.drop_take, List.take_take, Nat.min_eq_left h_elen_le]
    exact h_prefix0.trans h1
  -- Bridge: window prefix balance = `pbalance` of the head-entry prefix.
  have balstruct : ∀ m, m ≤ e.length →
      flowBracketBalance tokens lo (lo + m) = pbalance (e.take m) := by
    intro m hm
    rw [flowBracketBalance_eq_pbalance tokens lo (lo + m) (by omega)]
    congr 1
    rw [show lo + m - lo = m from by omega]
    have h2 : e.take m = (tokens.toList.drop lo).take m := by
      rw [h_eslice, List.take_take, Nat.min_eq_left hm]
    rw [h2]
  -- Located drop facts: `balance lo (j+1) = 0` (opener `1` + balanced interior `0` + close `-1`).
  have h_lo_val : tokens[lo]! = tokens.toList[lo]'h_lo_len := by
    rw [getElem!_pos tokens lo h_lo_sz, Array.getElem_toList]
  have h_j_val : tokens[j]! = tokens.toList[j]'h_j_len := by
    rw [getElem!_pos tokens j h_j_sz, Array.getElem_toList]
  have h_open_delta : flowBracketDelta tokens[lo]!.val = 1 := by
    rw [h_open]; exact flowBracketDelta_flowSequenceStart
  have h_close_delta : flowBracketDelta tokens[j]!.val = -1 := by
    rw [h_jclose]; exact flowBracketDelta_flowSequenceEnd
  have h_lo1_bal : flowBracketBalance tokens lo (lo + 1) = 1 := by
    rw [flowBracketBalance_single tokens lo h_lo_len, ← h_lo_val, h_open_delta]
  have h_lo_j_bal : flowBracketBalance tokens lo j = 1 := by
    have hc := flowBracketBalance_compose tokens lo (lo + 1) j (by omega) (by omega)
    rw [h_lo1_bal, h_inner] at hc; omega
  have h_j1_bal : flowBracketBalance tokens lo (j + 1) = 0 := by
    have hc := flowBracketBalance_compose tokens lo j (j + 1) (by omega) (Nat.le_succ j)
    rw [h_lo_j_bal, flowBracketBalance_single tokens j h_j_len, ← h_j_val, h_close_delta] at hc
    omega
  -- Structural: `balance lo (lo + e.length) = 0` (whole entry balances) + interior floor.
  have h_bal_eL : flowBracketBalance tokens lo (lo + e.length) = 0 := by
    rw [balstruct e.length (Nat.le_refl _), List.take_length]; exact h_e.toWellBracketed.1
  have h_floor_struct := recseqentry_opener_interior_floor h_e
  -- Uniqueness: the located close coincides with the head entry's structural close.
  have h_uniq : j + 1 = lo + e.length := by
    rcases Nat.lt_trichotomy (j + 1) (lo + e.length) with hlt | heq | hgt
    · exfalso
      have hm_lt : j + 1 - lo < e.length := by omega
      have hbs := balstruct (j + 1 - lo) (Nat.le_of_lt hm_lt)
      rw [show lo + (j + 1 - lo) = j + 1 from by omega] at hbs
      have hfl := h_floor_struct (j + 1 - lo) (by omega) hm_lt
      rw [hbs] at h_j1_bal; omega
    · exact heq
    · exfalso
      have hfl := h_floor (lo + e.length) (by omega) (by omega)
      rw [h_bal_eL] at hfl; omega
  -- Extract the head entry's stored interior, ruling out the three non-`seq` shapes.
  cases h_e with
  | scalar t c s ht =>
      exfalso; simp only [List.length_cons, List.length_nil] at h_uniq; omega
  | seqEmpty op cl h_op h_cl =>
      exfalso
      simp only [List.nil_append, List.length_cons, List.length_nil] at h_uniq; omega
  | map op cl interior h_op h_cl h_wb =>
      exfalso
      have hlen : (op :: (interior ++ [cl])).length = interior.length + 1 + 1 := by
        simp [List.length_append]
      rw [hlen, List.drop_eq_getElem_cons h_lo_len, List.take_succ_cons] at h_eslice
      have h_op_eq : op = tokens.toList[lo]'h_lo_len := (List.cons.inj h_eslice).1
      have h_val : tokens[lo]!.val = .flowMappingStart := by rw [h_lo_val, ← h_op_eq, h_op]
      rw [h_open] at h_val; exact absurd h_val (by simp)
  | seq op cl interior h_op h_cl h_wb h_rec =>
      have hlen : (op :: (interior ++ [cl])).length = interior.length + 1 + 1 := by
        simp [List.length_append]
      rw [hlen] at h_eslice h_uniq
      rw [List.drop_eq_getElem_cons h_lo_len, List.take_succ_cons] at h_eslice
      have h_tail : interior ++ [cl] = (tokens.toList.drop (lo + 1)).take (interior.length + 1) :=
        (List.cons.inj h_eslice).2
      have key : (tokens.toList.take j).drop (lo + 1) = interior := by
        rw [List.drop_take, show j - (lo + 1) = interior.length from by omega]
        calc (tokens.toList.drop (lo + 1)).take interior.length
            = ((tokens.toList.drop (lo + 1)).take (interior.length + 1)).take interior.length := by
                rw [List.take_take, Nat.min_eq_left (by omega)]
          _ = (interior ++ [cl]).take interior.length := by rw [← h_tail]
          _ = interior := List.take_left
      rw [key]; exact h_rec

/-- **Leaf close-pin** — `(i'-b-B2c-nested-fbc-emission-locator-leaf-pin)`, R358.  Exposes the
    close-matching uniqueness `recseqbody_head_seq_project` buries internally (its `h_uniq`), in the
    `.seq`-decomposed form the emission-spine-walk LEAF arm needs.  Given the navigator's current
    `RecSeqBody` window sliced at base `lo`, a located close `j` at depth `0`
    (`h_inner`: `flowBracketBalance (lo+1) j = 0`) under the located floor (`h_floor`: `≥ 1` over
    `(lo, j]`), with the head opener a `.flowSequenceStart`, the head entry is a NESTED SEQ
    `op :: (interior ++ [cl])` whose structural close coincides with `j` (`j + 1 = lo + e.length`).

    This is exactly the `h_b` pin the leaf brick `nestedSeq_recseqentry_locate_leaf` consumes
    (`b = off + e.length - 1` from `j + 1 = lo + e.length` with `j = b`, `lo = off`), together with the
    `.seq` decomposition (opener, nonempty interior, `RecSeqEntry`) and the head-window identity
    (`e = body.take e.length`, from which `body = e ++ rest` gives the brick's `h_prefix`).  The
    uniqueness is the two-sided bracket match: the located floor forbids an earlier close, the entry's
    own interior floor (`recseqentry_opener_interior_floor`) forbids a later one — identical to
    `recseqbody_head_seq_project`'s internal `h_uniq`, here RETURNED rather than consumed to produce the
    descended interior.  `e.length ≥ 3` (from `lo + 1 < j`) rules out `scalar` (length `1`) and
    `seqEmpty` (length `2`); the `.flowSequenceStart` head rules out `map`.  Verified-but-unconsumed
    until the `Nat.strongRecOn` wrapper threads it into the LEAF arm. -/
theorem recseqentry_close_pin
    (tokens : Array (Positioned YamlToken)) (lo H j : Nat)
    (h_body : RecSeqBody ((tokens.toList.take H).drop lo))
    (h_open : tokens[lo]!.val = .flowSequenceStart)
    (h_lo1_j : lo + 1 < j) (h_j_H : j < H) (h_H_sz : H ≤ tokens.size)
    (h_jclose : tokens[j]!.val = .flowSequenceEnd)
    (h_inner : flowBracketBalance tokens (lo + 1) j = 0)
    (h_floor : ∀ i, lo < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) :
    ∃ op cl interior,
      RecSeqEntry (op :: (interior ++ [cl])) ∧
      op.val = .flowSequenceStart ∧ interior ≠ [] ∧
      (op :: (interior ++ [cl]))
        = ((tokens.toList.take H).drop lo).take (op :: (interior ++ [cl])).length ∧
      j + 1 = lo + (op :: (interior ++ [cl])).length := by
  -- Size facts.
  have h_tl_len : tokens.toList.length = tokens.size := Array.length_toList
  have h_lo_lt_j : lo < j := by omega
  have h_lo_sz : lo < tokens.size := by omega
  have h_j_sz : j < tokens.size := by omega
  have h_lo_len : lo < tokens.toList.length := by rw [h_tl_len]; exact h_lo_sz
  have h_j_len : j < tokens.toList.length := by rw [h_tl_len]; exact h_j_sz
  -- Head entry `e` of the body window.
  obtain ⟨e, h_ne, h_e, _h_head, h_prefix0⟩ := recseqbody_head_entry h_body
  have h_e_ne_len : 0 < e.length := List.length_pos_iff.mpr h_ne
  have h_body_len : ((tokens.toList.take H).drop lo).length = H - lo := by
    rw [List.length_drop, List.length_take, h_tl_len, Nat.min_eq_left h_H_sz]
  have h_elen_le : e.length ≤ H - lo := by
    have hc := congrArg List.length h_prefix0
    rw [List.length_take, h_body_len] at hc; omega
  have h_eslice : e = (tokens.toList.drop lo).take e.length := by
    have h1 : ((tokens.toList.take H).drop lo).take e.length
        = (tokens.toList.drop lo).take e.length := by
      rw [List.drop_take, List.take_take, Nat.min_eq_left h_elen_le]
    exact h_prefix0.trans h1
  have balstruct : ∀ m, m ≤ e.length →
      flowBracketBalance tokens lo (lo + m) = pbalance (e.take m) := by
    intro m hm
    rw [flowBracketBalance_eq_pbalance tokens lo (lo + m) (by omega)]
    congr 1
    rw [show lo + m - lo = m from by omega]
    have h2 : e.take m = (tokens.toList.drop lo).take m := by
      rw [h_eslice, List.take_take, Nat.min_eq_left hm]
    rw [h2]
  have h_lo_val : tokens[lo]! = tokens.toList[lo]'h_lo_len := by
    rw [getElem!_pos tokens lo h_lo_sz, Array.getElem_toList]
  have h_j_val : tokens[j]! = tokens.toList[j]'h_j_len := by
    rw [getElem!_pos tokens j h_j_sz, Array.getElem_toList]
  have h_open_delta : flowBracketDelta tokens[lo]!.val = 1 := by
    rw [h_open]; exact flowBracketDelta_flowSequenceStart
  have h_close_delta : flowBracketDelta tokens[j]!.val = -1 := by
    rw [h_jclose]; exact flowBracketDelta_flowSequenceEnd
  have h_lo1_bal : flowBracketBalance tokens lo (lo + 1) = 1 := by
    rw [flowBracketBalance_single tokens lo h_lo_len, ← h_lo_val, h_open_delta]
  have h_lo_j_bal : flowBracketBalance tokens lo j = 1 := by
    have hc := flowBracketBalance_compose tokens lo (lo + 1) j (by omega) (by omega)
    rw [h_lo1_bal, h_inner] at hc; omega
  have h_j1_bal : flowBracketBalance tokens lo (j + 1) = 0 := by
    have hc := flowBracketBalance_compose tokens lo j (j + 1) (by omega) (Nat.le_succ j)
    rw [h_lo_j_bal, flowBracketBalance_single tokens j h_j_len, ← h_j_val, h_close_delta] at hc
    omega
  have h_bal_eL : flowBracketBalance tokens lo (lo + e.length) = 0 := by
    rw [balstruct e.length (Nat.le_refl _), List.take_length]; exact h_e.toWellBracketed.1
  have h_floor_struct := recseqentry_opener_interior_floor h_e
  have h_uniq : j + 1 = lo + e.length := by
    rcases Nat.lt_trichotomy (j + 1) (lo + e.length) with hlt | heq | hgt
    · exfalso
      have hm_lt : j + 1 - lo < e.length := by omega
      have hbs := balstruct (j + 1 - lo) (Nat.le_of_lt hm_lt)
      rw [show lo + (j + 1 - lo) = j + 1 from by omega] at hbs
      have hfl := h_floor_struct (j + 1 - lo) (by omega) hm_lt
      rw [hbs] at h_j1_bal; omega
    · exact heq
    · exfalso
      have hfl := h_floor (lo + e.length) (by omega) (by omega)
      rw [h_bal_eL] at hfl; omega
  -- Decompose `e` into the `.seq` shape: `e.length ≥ 3` rules out scalar/seqEmpty; head rules out map.
  cases h_e with
  | scalar t c s ht =>
      exfalso; simp only [List.length_cons, List.length_nil] at h_uniq; omega
  | seqEmpty op cl h_op h_cl =>
      exfalso
      simp only [List.nil_append, List.length_cons, List.length_nil] at h_uniq; omega
  | map op cl interior h_op h_cl h_wb =>
      exfalso
      have hlen : (op :: (interior ++ [cl])).length = interior.length + 1 + 1 := by
        simp [List.length_append]
      rw [hlen, List.drop_eq_getElem_cons h_lo_len, List.take_succ_cons] at h_eslice
      have h_op_eq : op = tokens.toList[lo]'h_lo_len := (List.cons.inj h_eslice).1
      have h_val : tokens[lo]!.val = .flowMappingStart := by rw [h_lo_val, ← h_op_eq, h_op]
      rw [h_open] at h_val; exact absurd h_val (by simp)
  | seq op cl interior h_op h_cl h_wb h_rec =>
      refine ⟨op, cl, interior, RecSeqEntry.seq op cl interior h_op h_cl h_wb h_rec,
        h_op, ?_, h_prefix0, h_uniq⟩
      -- interior ≠ [] : `(op::(interior++[cl])).length = interior.length + 2 ≥ 3` (from `lo+1 < j`).
      intro h_int_nil
      subst h_int_nil
      simp only [List.nil_append, List.length_cons, List.length_nil] at h_uniq
      omega

/-- **Head-or-cons split** — `(i'-b-B2c-nested-project)`, the structural dispatch that exposes the
    `cons` tail (`rest`, `h_rest`) the ADVANCE arm recurses on.  `recseqbody_head_entry` discards the
    tail; this richer sibling returns it, as a disjunction over the two `RecSeqBody` constructors:
    `single` (the window IS one entry, `l = e`) or `cons` (`l = e ++ fe :: rest`, with the stored
    separator `h_fe`, tail `h_rest`).  Both disjuncts carry the head entry's `RecSeqEntry`/content-head
    so the consumer never re-derives them.  `single`'s bare-var index keeps the target `l` under
    `cases` (R331 gotcha), so `l = e` is `rfl` with `e := l`. -/
theorem recseqbody_head_or_cons {l : List (Positioned YamlToken)} (h : RecSeqBody l) :
    (∃ (e : List (Positioned YamlToken)) (h_ne : e ≠ []),
        RecSeqEntry e ∧ ContentStartTok (e.head h_ne).val ∧ l = e)
    ∨ (∃ (e : List (Positioned YamlToken)) (fe : Positioned YamlToken)
         (rest : List (Positioned YamlToken)) (h_ne : e ≠ []),
        RecSeqEntry e ∧ ContentStartTok (e.head h_ne).val ∧
        fe.val = .flowEntry ∧ RecSeqBody rest ∧ l = e ++ fe :: rest) := by
  cases h with
  | single _ent h_ne h_e h_head => exact Or.inl ⟨l, h_ne, h_e, h_head, rfl⟩
  | cons ent fe rest h_ne h_e h_head h_fe h_rest =>
      exact Or.inr ⟨ent, fe, rest, h_ne, h_e, h_head, h_fe, h_rest, rfl⟩

/-- **One ADVANCE step** — `(i'-b-B2c-nested-project)`, the spine-walk arm of the root-`RecSeqBody`
    projection recursion (R330's `[1, [2, 3]]` advance-then-head move).  When the located seq opener
    `p` is at the body window's TOP level past its head (`flowBracketBalance lo p = 0 ∧ lo < p`), the
    head entry `e` is a complete balanced entry whose close precedes `p`; this peels `e` plus its
    `.flowEntry` separator and re-bases the window to `lo' = lo + e.length + 1`, preserving the
    dispatch invariant (`flowBracketBalance lo' p = 0`, `lo' ≤ p`) and strictly shrinking the body
    length — the `decreasing_by omega` fact the wrapping recursion rests on.

    The proof keeps the dispatch on the window-absolute `flowBracketBalance lo p` (never `e.length`,
    which is internal): `recseqbody_head_or_cons` exposes `e`/`rest`; the `single` case is impossible
    (the lone entry would span the whole window, so `p` strictly inside ⇒ interior floor `≥ 1`,
    contra `= 0`); in `cons`, the same interior floor (`recseqentry_opener_interior_floor`) forces
    `p ≥ lo + e.length`, and the `.flowEntry` separator's `flowBracketDelta = 0` (so
    `flowBracketBalance lo (lo + e.length + 1) = 0`) excludes `p = lo + e.length` — the located opener
    has `flowBracketDelta = +1`, contradicting the separator's `0`.  Slice algebra
    (`take_append`/`drop_left`/`drop_drop`) re-bases `rest = (toList.take H).drop lo'`.  The token at
    the separator is NOT extracted — its delta is sourced structurally from `h_fe` through
    `pbalance (e ++ [fe]) = 0`. -/
theorem recseqbody_advance (tokens : Array (Positioned YamlToken)) (lo H p : Nat)
    (h_body : RecSeqBody ((tokens.toList.take H).drop lo))
    (h_H_sz : H ≤ tokens.size)
    (h_lo_p : lo < p) (h_p_H : p < H)
    (h_p_open : tokens[p]!.val = .flowSequenceStart)
    (h_bal0 : flowBracketBalance tokens lo p = 0) :
    ∃ lo', lo < lo' ∧ lo' ≤ p ∧
      flowBracketBalance tokens lo' p = 0 ∧
      RecSeqBody ((tokens.toList.take H).drop lo') ∧
      ((tokens.toList.take H).drop lo').length < ((tokens.toList.take H).drop lo).length := by
  -- Size facts.
  have h_tl_len : tokens.toList.length = tokens.size := Array.length_toList
  have h_lo_sz : lo < tokens.size := by omega
  have h_p_sz : p < tokens.size := by omega
  have h_lo_len : lo < tokens.toList.length := by rw [h_tl_len]; exact h_lo_sz
  have h_p_len : p < tokens.toList.length := by rw [h_tl_len]; exact h_p_sz
  have h_body_len : ((tokens.toList.take H).drop lo).length = H - lo := by
    rw [List.length_drop, List.length_take, h_tl_len, Nat.min_eq_left h_H_sz]
  -- Located opener delta = +1.
  have h_p_val : tokens[p]! = tokens.toList[p]'h_p_len := by
    rw [getElem!_pos tokens p h_p_sz, Array.getElem_toList]
  have h_p_delta : flowBracketDelta tokens[p]!.val = 1 := by
    rw [h_p_open]; exact flowBracketDelta_flowSequenceStart
  rcases recseqbody_head_or_cons h_body with
    ⟨e, _h_ne, h_e, _h_head, h_eq⟩ | ⟨e, fe, rest, h_ne, h_e, _h_head, h_fe, h_rest, h_eq⟩
  · -- SINGLE: the whole window is one entry; `p` strictly inside ⇒ balance ≥ 1, contra `h_bal0`.
    exfalso
    have h_pref : e = ((tokens.toList.take H).drop lo).take e.length := by
      rw [h_eq]; exact (List.take_length).symm
    have h_elen_eq : e.length = H - lo := by rw [← h_body_len, h_eq]
    have h_eslice : e = (tokens.toList.drop lo).take e.length := by
      have h1 : ((tokens.toList.take H).drop lo).take e.length
          = (tokens.toList.drop lo).take e.length := by
        rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega : e.length ≤ H - lo)]
      exact h_pref.trans h1
    have balstruct : flowBracketBalance tokens lo p = pbalance (e.take (p - lo)) := by
      rw [flowBracketBalance_eq_pbalance tokens lo p (by omega)]
      congr 1
      have h2 : e.take (p - lo) = (tokens.toList.drop lo).take (p - lo) := by
        rw [h_eslice, List.take_take, Nat.min_eq_left (by omega : p - lo ≤ e.length)]
      rw [h2]
    have hfl := recseqentry_opener_interior_floor h_e (p - lo) (by omega) (by omega)
    rw [balstruct] at h_bal0
    omega
  · -- CONS: advance past head entry `e` + separator `fe`.
    have h_pref : e = ((tokens.toList.take H).drop lo).take e.length := by
      rw [h_eq]; exact (List.take_left).symm
    have h_cons_len : ((tokens.toList.take H).drop lo).length = e.length + 1 + rest.length := by
      rw [h_eq, List.length_append, List.length_cons]; omega
    have h_elen_le : e.length ≤ H - lo := by rw [← h_body_len, h_cons_len]; omega
    have h_eslice : e = (tokens.toList.drop lo).take e.length := by
      have h1 : ((tokens.toList.take H).drop lo).take e.length
          = (tokens.toList.drop lo).take e.length := by
        rw [List.drop_take, List.take_take, Nat.min_eq_left h_elen_le]
      exact h_pref.trans h1
    have balstruct : ∀ m, m ≤ e.length →
        flowBracketBalance tokens lo (lo + m) = pbalance (e.take m) := by
      intro m hm
      rw [flowBracketBalance_eq_pbalance tokens lo (lo + m) (by omega)]
      congr 1
      rw [show lo + m - lo = m from by omega]
      have h2 : e.take m = (tokens.toList.drop lo).take m := by
        rw [h_eslice, List.take_take, Nat.min_eq_left hm]
      rw [h2]
    -- `p` is at or past the head entry's structural close.
    have h_p_ge : lo + e.length ≤ p := by
      rcases Nat.lt_or_ge p (lo + e.length) with hlt | hge
      · exfalso
        have hbs := balstruct (p - lo) (by omega)
        rw [show lo + (p - lo) = p from by omega] at hbs
        have hfl := recseqentry_opener_interior_floor h_e (p - lo) (by omega) (by omega)
        rw [hbs] at h_bal0; omega
      · exact hge
    -- Whole entry balances to 0, and the `.flowEntry` separator keeps it: `balance lo (lo+|e|+1) = 0`.
    have h_bal_sep : flowBracketBalance tokens lo (lo + e.length + 1) = 0 := by
      have hle : e.length + 1 ≤ H - lo := by omega
      have h_take_sep : (tokens.toList.drop lo).take (e.length + 1) = e ++ [fe] := by
        have h1 : ((tokens.toList.take H).drop lo).take (e.length + 1)
            = (tokens.toList.drop lo).take (e.length + 1) := by
          rw [List.drop_take, List.take_take, Nat.min_eq_left hle]
        rw [← h1, h_eq, List.take_append, List.take_of_length_le (by omega),
            show e.length + 1 - e.length = 1 from by omega]
        simp
      have h_pbsep : pbalance (e ++ [fe]) = (0 : Int) := by
        rw [pbalance_append, h_e.toWellBracketed.1, pbalance_singleton, h_fe,
            flowBracketDelta_flowEntry]; rfl
      rw [flowBracketBalance_eq_pbalance tokens lo (lo + e.length + 1) (by omega),
          show lo + e.length + 1 - lo = e.length + 1 from by omega, h_take_sep, h_pbsep]
    -- `p` is strictly past the separator (it is an opener `+1`, not the `.flowEntry` `0`).
    have h_p_gt : lo + e.length < p := by
      rcases Nat.lt_or_ge (lo + e.length) p with hgt | hle
      · exact hgt
      · exfalso
        have hpe : p = lo + e.length := by omega
        have hc := flowBracketBalance_compose tokens lo p (p + 1) (by omega) (Nat.le_succ p)
        rw [flowBracketBalance_single tokens p h_p_len, ← h_p_val, h_p_delta, h_bal0] at hc
        rw [hpe, h_bal_sep] at hc
        omega
    refine ⟨lo + e.length + 1, by omega, by omega, ?_, ?_, ?_⟩
    · -- balance at the new base preserved.
      have hc := flowBracketBalance_compose tokens lo (lo + e.length + 1) p (by omega) (by omega)
      rw [h_bal_sep, h_bal0] at hc; omega
    · -- the re-based window body is exactly `rest`.
      have h_rest_eq : (tokens.toList.take H).drop (lo + e.length + 1) = rest := by
        have hd : ((tokens.toList.take H).drop lo).drop (e.length + 1)
            = (tokens.toList.take H).drop (lo + e.length + 1) := by
          rw [List.drop_drop]; congr 1
        rw [← hd, h_eq]; simp [List.drop_append]
      rw [h_rest_eq]; exact h_rest
    · -- measure strictly decreases.
      rw [h_body_len, List.length_drop, List.length_take, h_tl_len, Nat.min_eq_left h_H_sz]
      omega

/-- **General ADVANCE step** — `(i'-b-B2c-nested-project)`, the BALANCE-FREE advance arm of the
    root-`RecSeqBody` projection recursion, the sibling of `recseqbody_advance` (R332) the driver
    actually iterates.  R333 found `recseqbody_advance`'s `flowBracketBalance lo p = 0` guard covers
    ONLY a `p` at the window's top level past the head; a `p` NESTED inside a LATER entry has
    `flowBracketBalance lo p ≥ 1` yet is still past the head entry — so the dispatch splits on
    `p ≥ lo + e.length` (the structural past-head condition), NOT on balance.  This arm takes the
    head's `cons` decomposition explicitly (the driver has it from `recseqbody_head_or_cons`, and the
    `single` body is impossible here — its lone entry spans the whole window so
    `lo + e.length = H > p`) and the past-head bound `h_p_ge : lo + e.length ≤ p`, peels the head
    entry `e` plus its `.flowEntry` separator, and re-bases to `lo' = lo + e.length + 1` with body
    `rest`, strictly shrinking the body length — no balance machinery, no
    `flowBracketBalance lo' p = 0` output (the next step's DESCEND floor is reconstructed from
    `recseqentry_opener_interior_floor`, never threaded).

    The only positional fact needed is `lo + e.length ≠ p` (the separator is a `.flowEntry`, `p` a
    `.flowSequenceStart`), giving `lo + e.length < p` so `lo' ≤ p`.  The separator token is read off
    `h_eq` via the non-dependent `getElem?` slice algebra (`getElem?_drop`/`getElem?_take`/
    `getElem?_append_right`); slice re-basing mirrors `recseqbody_advance`'s `cons` tail. -/
theorem recseqbody_advance_general (tokens : Array (Positioned YamlToken)) (lo H p : Nat)
    (e rest : List (Positioned YamlToken)) (fe : Positioned YamlToken) (h_ne : e ≠ [])
    (h_fe : fe.val = .flowEntry) (h_rest : RecSeqBody rest)
    (h_eq : (tokens.toList.take H).drop lo = e ++ fe :: rest)
    (h_H_sz : H ≤ tokens.size) (h_p_H : p < H)
    (h_p_open : tokens[p]!.val = .flowSequenceStart)
    (h_p_ge : lo + e.length ≤ p) :
    ∃ lo', lo < lo' ∧ lo' ≤ p ∧
      RecSeqBody ((tokens.toList.take H).drop lo') ∧
      ((tokens.toList.take H).drop lo').length < ((tokens.toList.take H).drop lo).length := by
  have h_tl_len : tokens.toList.length = tokens.size := Array.length_toList
  have h_e_ne_len : 0 < e.length := List.length_pos_iff.mpr h_ne
  have h_sepH : lo + e.length < H := by omega
  have h_sep_sz : lo + e.length < tokens.size := by omega
  -- The separator token at window position `lo + e.length` is `fe` (a `.flowEntry`).
  have h_sep_q : tokens.toList[lo + e.length]? = some fe := by
    have hstep : ((tokens.toList.take H).drop lo)[e.length]? = tokens.toList[lo + e.length]? := by
      rw [List.getElem?_drop, List.getElem?_take, if_pos h_sepH]
    rw [← hstep, h_eq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have h_sep_val : tokens[lo + e.length]!.val = .flowEntry := by
    have hg := List.getElem?_eq_getElem (l := tokens.toList) (i := lo + e.length)
      (by rw [h_tl_len]; exact h_sep_sz)
    rw [hg] at h_sep_q
    have hcl : tokens.toList[lo + e.length]'(by rw [h_tl_len]; exact h_sep_sz) = fe :=
      Option.some.inj h_sep_q
    rw [getElem!_pos tokens (lo + e.length) h_sep_sz, ← Array.getElem_toList, hcl, h_fe]
  -- `p ≠ lo + e.length` (opener vs separator), so `p` is strictly past the separator.
  have h_p_gt : lo + e.length < p := by
    rcases Nat.lt_or_ge (lo + e.length) p with hgt | hle
    · exact hgt
    · exfalso
      have hpe : p = lo + e.length := by omega
      rw [hpe, h_sep_val] at h_p_open; simp at h_p_open
  have h_body_len : ((tokens.toList.take H).drop lo).length = H - lo := by
    rw [List.length_drop, List.length_take, h_tl_len, Nat.min_eq_left h_H_sz]
  refine ⟨lo + e.length + 1, by omega, by omega, ?_, ?_⟩
  · -- the re-based window body is exactly `rest`.
    have h_rest_eq : (tokens.toList.take H).drop (lo + e.length + 1) = rest := by
      have hd : ((tokens.toList.take H).drop lo).drop (e.length + 1)
          = (tokens.toList.take H).drop (lo + e.length + 1) := by
        rw [List.drop_drop]; congr 1
      rw [← hd, h_eq]; simp [List.drop_append]
    rw [h_rest_eq]; exact h_rest
  · -- measure strictly decreases.
    rw [h_body_len, List.length_drop, List.length_take, h_tl_len, Nat.min_eq_left h_H_sz]
    omega

/-- **One DESCEND step** — `(i'-b-B2c-nested-project)`, the bracket-level-down arm of the
    root-`RecSeqBody` projection recursion (R330's `[[[1, 2]]]` descend-into-interior move), the
    mirror of `recseqbody_advance` one bracket level IN.  When the located seq opener `p` is NESTED
    strictly inside the body's head entry — the window-absolute floor
    `∀ i ∈ (lo, p], flowBracketBalance lo i ≥ 1` forbids the balance returning to `0` before `p`, so
    `p` cannot be past the head entry (whose own close drops the balance to `0` at `lo + e.length`) —
    and that head opener is itself a `.flowSequenceStart` (`h_lo_open`: the driver's seq-axis
    dispatch; a `.flowMappingStart` head routes to the map mirror), the head entry is a `.seq` whose
    stored interior `RecSeqBody` is the descended window.  This re-bases `lo := lo + 1` (the interior
    starts just past the opener) and `H := lo + 1 + interior.length` (just before the entry's own
    close), keeping `p` inside the new window and strictly shrinking the body length — the
    `decreasing_by omega` fact the wrapping recursion rests on.

    The proof mirrors `recseqbody_head_seq_project`'s seq-case slice algebra, but the head entry's
    close is read off `e`'s OWN structure (`interior ++ [cl]`), not a handed-in located `j` — so no
    two-sided uniqueness is needed.  The floor forces `p < lo + e.length` (the whole entry balances to
    `0` at `lo + e.length`, which the floor forbids if `≤ p`); the located opener fact
    `h_p_open : tokens[p]! = .flowSequenceStart` excludes the degenerate shapes (`scalar` by length;
    the entry close at `p` would be a `.flowSequenceEnd`) and pins `p` strictly before the close
    (`p < H'`); `h_lo_open` excludes the `.map` head.  `cases h_e` then exposes the `.seq` interior
    `h_rec`, with `interior = (tokens.toList.take H').drop (lo + 1)` by the same
    `drop_take`/`take_take`/`take_left` identity the leaf uses. -/
theorem recseqbody_descend (tokens : Array (Positioned YamlToken)) (lo H p : Nat)
    (h_body : RecSeqBody ((tokens.toList.take H).drop lo))
    (h_H_sz : H ≤ tokens.size)
    (h_lo_p : lo < p) (h_p_H : p < H)
    (h_lo_open : tokens[lo]!.val = .flowSequenceStart)
    (h_p_open : tokens[p]!.val = .flowSequenceStart)
    (h_floor : ∀ i, lo < i → i ≤ p → flowBracketBalance tokens lo i ≥ 1) :
    ∃ H', lo + 1 ≤ p ∧ p < H' ∧ H' ≤ H ∧
      RecSeqBody ((tokens.toList.take H').drop (lo + 1)) ∧
      ((tokens.toList.take H').drop (lo + 1)).length < ((tokens.toList.take H).drop lo).length := by
  -- Size facts.
  have h_tl_len : tokens.toList.length = tokens.size := Array.length_toList
  have h_lo_sz : lo < tokens.size := by omega
  have h_p_sz : p < tokens.size := by omega
  have h_lo_len : lo < tokens.toList.length := by rw [h_tl_len]; exact h_lo_sz
  have h_p_len : p < tokens.toList.length := by rw [h_tl_len]; exact h_p_sz
  have h_lo_val : tokens[lo]! = tokens.toList[lo]'h_lo_len := by
    rw [getElem!_pos tokens lo h_lo_sz, Array.getElem_toList]
  have h_body_len : ((tokens.toList.take H).drop lo).length = H - lo := by
    rw [List.length_drop, List.length_take, h_tl_len, Nat.min_eq_left h_H_sz]
  -- Head entry `e` of the body window.
  obtain ⟨e, h_ne, h_e, _h_head, h_prefix0⟩ := recseqbody_head_entry h_body
  have h_e_ne_len : 0 < e.length := List.length_pos_iff.mpr h_ne
  have h_elen_le : e.length ≤ H - lo := by
    have hc := congrArg List.length h_prefix0
    rw [List.length_take, h_body_len] at hc; omega
  have h_eslice : e = (tokens.toList.drop lo).take e.length := by
    have h1 : ((tokens.toList.take H).drop lo).take e.length
        = (tokens.toList.drop lo).take e.length := by
      rw [List.drop_take, List.take_take, Nat.min_eq_left h_elen_le]
    exact h_prefix0.trans h1
  -- Bridge: window prefix balance = `pbalance` of the head-entry prefix.
  have balstruct : ∀ m, m ≤ e.length →
      flowBracketBalance tokens lo (lo + m) = pbalance (e.take m) := by
    intro m hm
    rw [flowBracketBalance_eq_pbalance tokens lo (lo + m) (by omega)]
    congr 1
    rw [show lo + m - lo = m from by omega]
    have h2 : e.take m = (tokens.toList.drop lo).take m := by
      rw [h_eslice, List.take_take, Nat.min_eq_left hm]
    rw [h2]
  -- `p` is strictly inside the head entry: the whole entry balances to 0, which the floor forbids ≤ p.
  have h_p_lt : p < lo + e.length := by
    rcases Nat.lt_or_ge p (lo + e.length) with hlt | hge
    · exact hlt
    · exfalso
      have hbs := balstruct e.length (Nat.le_refl _)
      rw [List.take_length, h_e.toWellBracketed.1] at hbs
      have hfl := h_floor (lo + e.length) (by omega) hge
      rw [hbs] at hfl; omega
  -- Extract the head entry's stored interior, ruling out the three non-`seq` shapes.
  cases h_e with
  | scalar t c s ht =>
      exfalso; simp only [List.length_cons, List.length_nil] at h_p_lt; omega
  | seqEmpty op cl h_op h_cl =>
      exfalso
      have hlen : (op :: ([] ++ [cl])).length = 0 + 1 + 1 := by simp
      rw [hlen] at h_eslice h_p_lt
      rw [List.drop_eq_getElem_cons h_lo_len, List.take_succ_cons] at h_eslice
      have h_tail : ([] ++ [cl]) = (tokens.toList.drop (lo + 1)).take (0 + 1) :=
        (List.cons.inj h_eslice).2
      have hp1 : p = lo + 1 := by omega
      have h_close_sz : lo + 1 < tokens.size := by omega
      have h_cl_q : tokens.toList[lo + 1]? = some cl := by
        have hstep : tokens.toList[lo + 1]?
            = (([] : List (Positioned YamlToken)) ++ [cl])[0]? := by
          rw [h_tail, List.getElem?_take, if_pos (by omega), List.getElem?_drop]
        rw [hstep]; rfl
      have hcl : tokens.toList[lo + 1]'(by rw [h_tl_len]; exact h_close_sz) = cl := by
        have hg := List.getElem?_eq_getElem (l := tokens.toList) (i := lo + 1)
          (by rw [h_tl_len]; exact h_close_sz)
        rw [hg] at h_cl_q; exact Option.some.inj h_cl_q
      have h_close_val : tokens[lo + 1]!.val = .flowSequenceEnd := by
        rw [getElem!_pos tokens (lo + 1) h_close_sz, ← Array.getElem_toList, hcl, h_cl]
      rw [hp1, h_close_val] at h_p_open
      simp at h_p_open
  | map op cl interior h_op h_cl h_wb =>
      exfalso
      have hlen : (op :: (interior ++ [cl])).length = interior.length + 1 + 1 := by
        simp [List.length_append]
      rw [hlen] at h_eslice
      rw [List.drop_eq_getElem_cons h_lo_len, List.take_succ_cons] at h_eslice
      have h_op_eq : op = tokens.toList[lo]'h_lo_len := (List.cons.inj h_eslice).1
      have h_val : tokens[lo]!.val = .flowMappingStart := by rw [h_lo_val, ← h_op_eq, h_op]
      rw [h_lo_open] at h_val; exact absurd h_val (by simp)
  | seq op cl interior h_op h_cl h_wb h_rec =>
      have hlen : (op :: (interior ++ [cl])).length = interior.length + 1 + 1 := by
        simp [List.length_append]
      rw [hlen] at h_eslice h_p_lt h_elen_le
      rw [List.drop_eq_getElem_cons h_lo_len, List.take_succ_cons] at h_eslice
      have h_tail : interior ++ [cl] = (tokens.toList.drop (lo + 1)).take (interior.length + 1) :=
        (List.cons.inj h_eslice).2
      have h_close_sz : lo + 1 + interior.length < tokens.size := by omega
      have h_close_val : tokens[lo + 1 + interior.length]!.val = .flowSequenceEnd := by
        have h_cl_q : tokens.toList[lo + 1 + interior.length]? = some cl := by
          have hstep : ((tokens.toList.drop (lo + 1)).take (interior.length + 1))[interior.length]?
              = tokens.toList[lo + 1 + interior.length]? := by
            rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop]
          rw [← hstep, ← h_tail, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
        have hcl : tokens.toList[lo + 1 + interior.length]'(by rw [h_tl_len]; exact h_close_sz)
            = cl := by
          have hg := List.getElem?_eq_getElem (l := tokens.toList) (i := lo + 1 + interior.length)
            (by rw [h_tl_len]; exact h_close_sz)
          rw [hg] at h_cl_q; exact Option.some.inj h_cl_q
        rw [getElem!_pos tokens (lo + 1 + interior.length) h_close_sz, ← Array.getElem_toList,
            hcl, h_cl]
      have hp_close : p ≠ lo + 1 + interior.length := by
        intro he; rw [he, h_close_val] at h_p_open; simp at h_p_open
      have key : (tokens.toList.take (lo + 1 + interior.length)).drop (lo + 1) = interior := by
        rw [List.drop_take, show (lo + 1 + interior.length) - (lo + 1) = interior.length from by omega]
        calc (tokens.toList.drop (lo + 1)).take interior.length
            = ((tokens.toList.drop (lo + 1)).take (interior.length + 1)).take interior.length := by
                rw [List.take_take, Nat.min_eq_left (by omega)]
          _ = (interior ++ [cl]).take interior.length := by rw [← h_tail]
          _ = interior := List.take_left
      refine ⟨lo + 1 + interior.length, by omega, by omega, by omega, ?_, ?_⟩
      · rw [key]; exact h_rec
      · rw [key, h_body_len]; omega

/-! ### Emit-producer strengthening — seq-body recursive deliverable (Phase J feed)

The locate recursion is *fed* by the top-level `RecSeqBody`/`RecMapBody` of the emitted+filtered
body — the recursive structure the locate descends.  `emitList_scans_safebody`
(`BlockProducers.lean`) already produces the *flat* body invariants (`SafeBody` / `SafeBodyUnit` /
`WellBracketed` / `WellTyped`) for the comma-separated body `block` of `emitList items`; the
strengthening below produces the *recursive* `RecSeqBody block` instead.

It follows the established **consumer-joint-before-producer** rhythm (Reflection 231 family) one more
time, on the emit feed: the assembler `emitList_scans_recseqbody` is keyed on the not-yet-produced
per-item recursive deliverable as a bare hypothesis (`EmitScansInFlowRecEntry`, a superset of
`EmitScansInFlowBlock` additionally carrying `RecSeqEntry block`), and accumulates `RecSeqBody` by
the **same induction** `emitList_scans_safebody` uses for `SafeBody` — `RecSeqBody.single`/`.cons`
in place of `SafeBody.single`/`.cons`, with `RecSeqEntry block₁` where the flat proof used
`EntrySafe block₁` and the recursive tail `RecSeqBody block_rest` where it used `SafeBody …`.  Every
other step (the scanner-chain replay, the comma `.flowEntry` separator, the whitespace preprocess,
the chain lift) is transported verbatim.  Verified-but-unconsumed: it references no sorry site, so
the frontier sorry count is unchanged — it retypes the residual one structural layer down, reducing
"deliver the top-level `RecSeqBody`" to "deliver each item's `RecSeqEntry`" (the next residual: the
`Grammable`-case-split per-item producer, whose `scalar` leaf is `RecSeqEntry.scalar` and whose
`sequence`/`mapping` cases recurse through this very assembler). -/

/-- Per-item refinement of `EmitScansInFlowBlock`: scanning `emit v` delivers a `block` that is not
    only flat (`WellBracketed`/`WellTyped`/`EntrySafe`/`EntryUnit`/content-start head) but a
    *recursive* `RecSeqEntry` — the deliverable the seq-body assembler accumulates into `RecSeqBody`.
    Stated as a strict superset of `EmitScansInFlowBlock` (the lone extra conjunct `RecSeqEntry block`
    sits just before the content-start head) so the `RecSeqEntry block` is keyed to the *same* internal
    `block`: the future per-item producer supplies both from one scanner run. -/
def EmitScansInFlowRecEntry (v : YamlValue) : Prop :=
  ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit v).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    s.simpleKeyStack.size = s.flowLevel →
    ∃ n s' block,
      ScanChainGrew (fun t => t.val != .placeholder) s n s'
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.line = s.line
      ∧ s'.simpleKeyAllowed = false
      ∧ (∀ t, lastRealTokenVal? s'.tokens = some t →
          t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ FlowMonoChain s.flowLevel s n s'
      ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block
      ∧ WellBracketed block
      ∧ WellTyped block
      ∧ EntrySafe block
      ∧ EntryUnit block
      ∧ RecSeqEntry block
      ∧ (∃ (h : block ≠ []), ContentStartTok (block.head h).val)

/-- **Seq-body recursive-deliverable assembler** (Phase J — the `RecSeqBody` strengthening of
    `emitList_scans_safebody`).  Given that each item's `emit v` block is a recursive `RecSeqEntry`
    (the bare per-item hypothesis `EmitScansInFlowRecEntry`), the comma-separated body block of
    `emitList items` is a full `RecSeqBody` — `.single`/`.cons` accumulated by the same induction
    `emitList_scans_safebody` uses for `SafeBody`, with `RecSeqEntry block₁` in place of
    `EntrySafe block₁` and the recursive tail `RecSeqBody block_rest` in place of `SafeBody …`.  The
    proof is a verbatim mirror of `emitList_scans_safebody`; only the per-entry constructor changes.
    Verified-but-unconsumed: references no sorry site, frontier sorry count unchanged. -/
theorem emitList_scans_recseqbody (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, EmitScansInFlowRecEntry v) :
    ∀ (s : ScannerState) (rest_chars : List Char),
      ScannerSurfCorr s ⟨(emit.emitList items).toList ++ rest_chars, s.col⟩ →
      s.inFlow = true →
      s.flowLevel > 0 →
      s.currentIndent < 0 →
      s.col > 0 →
      s.explicitKeyLine = none →
      AllTokensOnLine s s.line →
      EndLineOnLine s →
      s.simpleKeyStack.size = s.flowLevel →
      ∃ n s' block,
        ScanChainGrew (fun t => t.val != .placeholder) s n s'
        ∧ ScannerSurfCorr s' ⟨rest_chars, s'.col⟩
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
        ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block
        ∧ WellBracketed block
        ∧ WellTyped block
        ∧ RecSeqBody block := by
  induction items with
  | nil => contradiction
  | cons v tail ih =>
    intro s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
    match tail, ih with
    | [], _ =>
      have h_eq : (emit.emitList [v]).toList = (emit v).toList := by
        simp only [emit.emitList]
      rw [h_eq] at hcorr
      obtain ⟨n, s', block, h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow',
              h_indent', h_line_v, _h_ska, _h_last, h_atol', h_endline', h_stack', h_fmc',
              h_block_eq, h_wb, h_wt, _h_es, _h_eu, h_e, h_cs⟩ :=
        h_all v (.head _) s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
      obtain ⟨h_cs_ne, h_cs_val⟩ := h_cs
      exact ⟨n, s', block, h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow',
        h_indent', h_line_v, h_atol', h_endline', h_stack', h_fmc', h_block_eq, h_wb, h_wt,
        RecSeqBody.single block h_cs_ne h_e h_cs_val⟩
    | v' :: vs, ih =>
      have h_eq : (emit.emitList (v :: v' :: vs)).toList ++ rest_chars =
          (emit v).toList ++ ([',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars) := by
        simp [emit.emitList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: Scan emit v via EmitScansInFlowRecEntry (item block `block₁`, with RecSeqEntry + head)
      have h_ev : EmitScansInFlowRecEntry v := h_all v (.head _)
      obtain ⟨n₁, s₁, block₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, h_flow₁,
              h_indent₁, _h_line₁, _h_ska₁, h_last₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁,
              h_block_eq₁, h_wb₁, h_wt₁, _h_es₁, _h_eu₁, h_e₁, h_cs₁⟩ :=
        h_ev s ([',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
      obtain ⟨h_cs₁_ne, h_cs₁_val⟩ := h_cs₁
      -- Step 2: Scan ',' via scanNextToken_flow_comma (state) + push lemma (block)
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, _h_line₂, h_atol₂, h_endline₂, h_stack₂⟩ :=
        scanNextToken_flow_comma s₁
          (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁
          h_last₁ h_atol₁ h_endline₁
      obtain ⟨feTok, h_feTok_val, h_comma_eq⟩ :=
        scanNextToken_flow_comma_filtered_push s₁
          (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ h_last₁ h_snt₂
      -- Step 3: Handle leading space via preprocessing equality
      obtain ⟨c, rest', h_first, h_nws, h_nlb, h_nc⟩ := emitList_first_char v' vs
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: c :: (rest' ++ rest_chars), s₂.col⟩ := by
        have : ' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars =
            ' ' :: c :: (rest' ++ rest_chars) := by
          rw [h_first]; simp only [List.cons_append]
        rwa [this] at h_corr₂
      have h_s2_flow : s₂.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₂]; omega)
      have h_s2_indent : s₂.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids₂]; exact h_indent₁
      have h_s2_col : s₂.col > 0 := by rw [h_col₂]; omega
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _, _⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ c (rest' ++ rest_chars) h_corr₂_ws
          h_s2_flow h_nws h_nlb h_nc h_s2_indent
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit.emitList (v' :: vs)).toList ++ rest_chars, s₃.col⟩ := by
        have : c :: (rest' ++ rest_chars) = (emit.emitList (v' :: vs)).toList ++ rest_chars := by
          rw [h_first]; simp only [List.cons_append]
        rwa [this] at h_corr₃
      -- Step 4: Recursive scan of emitList (v' :: vs) from s₃ (tail block `block_rest`, with RecSeqBody)
      have h_tail_all : ∀ w ∈ v' :: vs, EmitScansInFlowRecEntry w :=
        fun w hw => h_all w (.tail _ hw)
      obtain ⟨n₃, s_end, block_rest, h_chain₃, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end, h_endline_end, h_stack_end, h_fmc₃, h_block_eq_end, h_wb_rest, h_wt_rest, h_rec_rest⟩ :=
        ih (by simp) h_tail_all s₃ rest_chars h_corr₃'
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_s2_indent)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃, h_ek₂, h_ek₁]; exact h_ek)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
          (by rw [h_stack_pp₃, h_stack₂, h_stack₁, h_fl₃, h_fl₂, h_fl₁]; exact h_sync)
      -- Step 5: Lift chain for s₂ via preprocessing equality
      have h_snt_eq : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n₃_pos : n₃ ≥ 1 := by
        match n₃, h_chain₃ with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit.emitList (v' :: vs)).toList = [] := by
            match h_list : (emit.emitList (v' :: vs)).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          exact absurd h_nil (emitList_toList_ne_nil v' vs)
        | _ + 1, _ => omega
      obtain ⟨n₃', rfl⟩ : ∃ k, n₃ = k + 1 := ⟨n₃ - 1, by omega⟩
      have h_filt_le : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                       (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws : ScanChainGrew (fun t => t.val != .placeholder)
            s₂ (n₃' + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq h_filt_le h_chain₃
      have h_grew₂ : (s₂.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₁.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorr s₁
            ⟨',' :: (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars), s₁.col⟩ := by
          have : [',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars =
              ',' :: (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextToken_filtered_grows_in_flow s₁ s₂ ','
          (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      have h_fmc₃' : FlowMonoChain s.flowLevel s₃ (n₃' + 1) s_end :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc₃
      have h_fmc_ws : FlowMonoChain s.flowLevel s₂ (n₃' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq (by omega) h_fmc₃'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans h_fmc_ws)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans h_chain_ws)
      have h_arith : n₁ + (1 + (n₃' + 1)) = n₁ + 1 + (n₃' + 1) := by omega
      -- Block accumulation: block = block₁ ++ [feTok] ++ block_rest
      have h_block_eq₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ (block₁ ++ [feTok]) := by
        have h_s3_s2 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList := by
          rw [h_toks_pp₃]
        rw [h_s3_s2, congrArg Array.toList h_comma_eq, Array.toList_push, h_block_eq₁,
            List.append_assoc]
      refine ⟨n₁ + 1 + (n₃' + 1), s_end, block₁ ++ [feTok] ++ block_rest,
        h_arith ▸ h_chain_all, h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end,
        ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, ?_, ?_, ?_, ?_⟩
      · rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek₃, h_ek₂, h_ek₁]
      · rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp₃, h_stack₂, h_stack₁]
      · -- block equation: s_end = s₃ ++ block_rest = s ++ (block₁ ++ [feTok]) ++ block_rest
        rw [h_block_eq_end, h_block_eq₃, List.append_assoc]
      · -- WellBracketed (block₁ ++ [feTok] ++ block_rest)
        exact WellBracketed_append _ _
          (WellBracketed_append _ _ h_wb₁
            (WellBracketed_singleton_delta_zero feTok (by rw [h_feTok_val]; exact flowBracketDelta_flowEntry)))
          h_wb_rest
      · -- WellTyped (block₁ ++ [feTok] ++ block_rest) — typed twin of the WellBracketed bullet.
        exact WellTyped_append _ _
          (WellTyped_append _ _ h_wt₁
            (WellTyped_singleton_delta_zero feTok (by rw [h_feTok_val]; exact flowBracketDelta_flowEntry)))
          h_wt_rest
      · -- RecSeqBody (block₁ ++ [feTok] ++ block_rest)
        have h_reassoc : block₁ ++ [feTok] ++ block_rest = block₁ ++ feTok :: block_rest := by
          rw [List.append_assoc]; rfl
        rw [h_reassoc]
        exact RecSeqBody.cons block₁ feTok block_rest h_cs₁_ne h_e₁ h_cs₁_val h_feTok_val h_rec_rest

/-- **Seq-body recursive seed** (Phase J — the `RecSeqBody` analog of
    `emitList_body_filtered_characterization`).  Where that lemma packages `emitList_scans_safebody`
    into the body's *flat* content characterization, this one packages `emitList_scans_recseqbody`
    into the body's *recursive* deliverable, restated positionally: the `drop old_sz` tail of the
    final filtered token list is one `RecSeqBody`.  This is the **root the locate recursion descends
    from** — the outer-window (`lo = old_sz`) leaf of the per-window `RecSeqBody` producer
    `flowSubrangesOk_of_window_producers` consumes: at the body-interior span `[2, size-2)` the window
    `(take (size-2)).drop 2` is exactly this `drop old_sz` tail, so this is the universal producer's
    base case; the recursion navigates this top-level structure down to every nested guarded subrange.
    Keyed on the recursive per-item hypothesis `EmitScansInFlowRecEntry` (the superset of
    `EmitScansInFlowBlock` carrying `RecSeqEntry`, supplied per item by `emit_scans_in_flow_rec_entry`).
    Verified-but-unconsumed until the locate lands: composes only `emitList_scans_recseqbody` + the
    positional `drop` (`h_drop`, verbatim from the flat lemma), references no sorry site, frontier
    sorry count unchanged. -/
theorem emitList_body_recseqbody
    (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, EmitScansInFlowRecEntry v)
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
    ∧ RecSeqBody ((s'.tokens.filter p).toList.drop old_sz) := by
  obtain ⟨n, s', block, h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, h_block_eq, h_wb, h_wt, h_rec⟩ :=
    emitList_scans_recseqbody items h_ne h_all s rest h_corr h_flow h_fl h_indent h_col
      h_ek h_atol h_endline h_sync
  -- The body block is exactly the `drop old_sz` of the final filtered token list (verbatim from
  -- `emitList_body_filtered_characterization`).
  have h_drop : (s'.tokens.filter (fun t => t.val != .placeholder)).toList.drop
      (s.tokens.filter (fun t => t.val != .placeholder)).size = block := by
    rw [h_block_eq,
      show (s.tokens.filter (fun t => t.val != .placeholder)).size
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList.length
        from Array.length_toList.symm,
      List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
  refine ⟨n, s', h_chain.toScanChain, h_corr', h_fl', h_dp', h_ids', h_ek',
          h_col', h_inflow', h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, ?_⟩
  show RecSeqBody ((s'.tokens.filter (fun t => t.val != .placeholder)).toList.drop
      (s.tokens.filter (fun t => t.val != .placeholder)).size)
  rw [h_drop]; exact h_rec

/-- **Seq root provider — windowed `RecSeqBody` at the outer span `[2, size-2)`** (Phase J,
    `(i'-b-B2c-desc-from-emission)`, the ROOT SEED of the position-keyed nested-body projection).
    Per [[ref-root-seed-recursive-producer-swap]], this is the FLAT-fact derivation
    `seqRoot_safeBodyUnit` re-run with the *recursive* deliverable KEPT instead of projected: it
    delivers `RecSeqBody ((tokens.toList.take (tokens.size - 2)).drop 2)` directly from emission,
    with NO recursion over nested seq windows.  The richer `RecSeqBody` re-projects to the flat
    `SafeBodyUnit` the root carrier needs (`seqRoot_safeBodyUnit` below), AND — crucially — carries
    every nested entry's interior `RecSeqBody` in its `RecSeqEntry.seq.h_rec` fields, the structural
    source `rec_seq_body_nested_project` descends to discharge `bodySucc` at the nested gated
    windows (R327: the carrier's only deliverable-projecting field, unthreadable through the guard,
    must be sourced globally from this seed).

    The construction is the **slice bridge** the next-step note named "verbatim": replay the
    open-bracket → body → close-bracket chain exactly as `scanFiltered_emitSeq_nonempty_structure`
    does, but feed the body through the *recursive* producer `emitList_body_recseqbody` (whose
    deliverable is `RecSeqBody` over the body block `(s₂.tokens.filter p).toList.drop 2`), then
    re-slice through the same token-decomposition slice identity `h_take_eq` that the structural
    lemma uses for `WellTyped`: the interior slice `tokens.toList.take (tokens.size - 2)` is exactly
    the body block `(s₂.tokens.filter p).toList` (the two trailing pushes `tok_fse`/`streamEnd` are
    dropped by `take (size-2)`), so its `.drop 2` is the `.drop old_sz` tail the `RecSeqBody` is
    keyed on (`old_sz = (s₁.filter p).size = 2`).

    Keyed on the recursive per-item hypothesis `EmitScansInFlowRecEntry` (the producer's interface,
    supplied per item by `emit_scans_in_flow_rec_entry` from `Grammable`).  This is the producer's
    GIFT side made concrete (R301): the gate `SeqTypedInterior` the carrier `intro`s is *consumed*
    when proving the carrier; here at the root the provider just hands over the `RecSeqBody` the
    emission already scanned. -/
theorem seqRoot_recseqbody
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v) :
    RecSeqBody ((tokens.toList.take (tokens.size - 2)).drop 2) := by
  let input := "[" ++ emit.emitList items.toList ++ "]"
  let p := fun (t : Positioned YamlToken) => t.val != .placeholder
  have h_toList : input.toList = '[' :: (emit.emitList items.toList).toList ++ [']'] := by
    simp only [input, String.toList_append]; rfl
  -- Open bracket → s₁
  obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
          h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, h_sk₁, h_filt₁,
          h_sync₁, _h_ska₁, _h_ssv₁⟩ :=
    scanNextToken_flow_open_init input
      ((emit.emitList items.toList).toList ++ [']']) h_toList
  -- Body scanning → s₂ via the RECURSIVE producer (delivers `RecSeqBody` of the body block)
  obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_inflow₂,
          h_indent₂, h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂, h_rec₂⟩ :=
    emitList_body_recseqbody items.toList h_ne h_all s₁ [']']
      h_corr₁ h_inflow₁ (by rw [h_fl₁]; omega) h_indent₁ (by rw [h_col₁]; omega)
      h_ek₁ (h_line₁ ▸ h_atol₁) h_endline₁ h_sync₁
  -- Close bracket → s₃
  obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃, h_ids₃, ⟨tok_fse, h_tok_fse_val, h_filt₃⟩⟩ :=
    scanNextToken_flow_close_seq_outermost_ext s₂ h_corr₂ h_inflow₂ h_indent₂ h_col₂
      (by rw [h_fl₂, h_fl₁]) (by rw [h_dp₂, h_dp₁])
  -- EOF + chain composition
  have h_eof : scanNextToken s₃ = .ok none := scanNextToken_eof s₃ h_peek₃
  have h_chain_all := (ScanChain.single h_snt₁).trans
    (h_chain₂.trans (ScanChain.single h_snt₃))
  -- BOM check
  have h_no_bom : (ScannerState.mk' input).peek? ≠ some '﻿' := by
    have h_chars := chars_from_zero_toList input
    rw [h_toList] at h_chars
    have h_corr := initial_corr _ _ h_chars
    have ⟨h_pk, _⟩ := peek_of_chars_cons _ '['
      ((emit.emitList items.toList).toList ++ [']']) 0 h_corr
    rw [h_pk]; decide
  -- Indents chain: s₃.indents = s₁.indents = #[] (default from mk')
  have h_indents_small : s₃.indents.size ≤ 1 := by
    rw [h_ids₃, h_ids₂, h_ids₁]
    unfold ScannerState.emit ScannerState.mk'
    dsimp only []
    decide
  -- Token equation: tokens = (s₃.emit .streamEnd).tokens.filter p
  have h_tok_eq : Scanner.scanFiltered input =
      .ok ((s₃.emit .streamEnd).tokens.filter p) :=
    scanFiltered_tokens_eq_of_chain_short_stack input _ s₃ _ rfl h_no_bom
      h_chain_all h_eof h_fl₃ h_dp₃
      (ScanChain.fuel_bound _ _ _ _ rfl h_chain_all h_eof)
      h_indents_small
  have h_tokens_eq : tokens = (s₃.emit .streamEnd).tokens.filter p := by
    have : Scanner.scanFiltered input = .ok tokens := h_scan
    rw [h_tok_eq] at this; exact (Except.ok.inj this).symm
  -- Decompose: tokens = ((s₂.tokens.filter p).push tok_fse).push streamEnd
  have h_emit_se_tokens : (s₃.emit .streamEnd).tokens =
      s₃.tokens.push { pos := s₃.currentPos, val := .streamEnd } := by
    unfold ScannerState.emit; rfl
  have h_final_filter : (s₃.emit .streamEnd).tokens.filter p =
      (s₃.tokens.filter p).push { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_emit_se_tokens, Array.filter_push]; rfl
  have h_tokens_decomp : tokens = ((s₂.tokens.filter p).push tok_fse).push
      { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_tokens_eq, h_final_filter, h_filt₃]
  -- old_sz = (s₁.tokens.filter p).size = 2
  have h_filt₁_sz : (s₁.tokens.filter p).size = 2 := by
    have : ((s₁.tokens.filter p).map (·.val)).size = 2 := by rw [h_filt₁]; rfl
    simpa [Array.size_map] using this
  -- The interior slice `take (size-2)` is exactly the body block `(s₂.filter p).toList`
  have h_tokens_sz_eq : tokens.size - 2 = (s₂.tokens.filter p).size := by
    rw [h_tokens_decomp]; simp [Array.size_push]
  have h_take_eq : tokens.toList.take (tokens.size - 2) = (s₂.tokens.filter p).toList := by
    have h_sz : tokens.size - 2 = (s₂.tokens.filter p).toList.length := by
      rw [h_tokens_sz_eq, Array.length_toList]
    rw [h_sz, h_tokens_decomp, Array.toList_push, Array.toList_push, List.append_assoc,
      List.take_left]
  -- The body block's `RecSeqBody`, re-sliced to the outer window `[2, size-2)`.
  rw [h_filt₁_sz] at h_rec₂
  rw [h_take_eq]
  exact h_rec₂

/-- **Seq root provider — windowed `SafeBodyUnit` at the outer span `[2, size-2)`** (Phase J,
    `(i'-b-descend-root-provider)`, the ROOT instance of the universal seq-window producer).
    Per [[ref-universal-producer-root-seed-first]], this is the base case of the `provider`
    `seqInteriorSeparators_of_safebody_provider` consumes.  Now a one-line `.toSafeBodyUnit`
    re-projection of the `seqRoot_recseqbody` seed (the flat fact re-derives from the recursive
    deliverable; [[ref-root-seed-recursive-producer-swap]]: swapping in the recursive producer
    loses nothing, gains the nested-body structure). -/
theorem seqRoot_safeBodyUnit
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntry v) :
    SafeBodyUnit ContentStartTok ((tokens.toList.take (tokens.size - 2)).drop 2) :=
  (seqRoot_recseqbody items tokens h_scan h_ne h_all).toSafeBodyUnit

/-! ### Recursive deliverable — map side (`RecMapBody` / `RecMapPair`)

The map-side mirror of `RecSeqBody`/`RecSeqEntry` (Reflection 234), one nesting level deeper.  A
flow-MAPPING body's emitted+filtered block is a `.flowEntry`-separated list of **pairs**, each pair
the filtered tokens `key :: (block_k ++ value :: block_v)` — a `.key` marker, the key's `emit`
block, a `.value` marker, the value's `emit` block.  A key or a value is *one* `emit v` block, which
is exactly what `RecSeqEntry` already characterizes (scalar / nested seq / nested map / empty), so a
pair carries **two `RecSeqEntry`s** (key and value).  This is what lets the map-side descent-locator
reach into a key's or value's nested flow-sequence interior: that interior's `RecSeqBody` is recorded
inside the `RecSeqEntry.seq` of `block_k`/`block_v`.

`RecMapPair` depends only on the already-defined `RecSeqEntry` (its key/value blocks), and `RecMapBody`
recurses only on itself — so, unlike the seq side, **no `mutual` block is needed** (avoiding the
`mutual`-doc-comment / `induction` / `Or`-nesting gotchas of Reflection 234 entirely): define
`RecMapPair` first, then `RecMapBody`.  As on the seq side, the deeper key/value-of-a-nested-*mapping*
recursion still bottoms out at the `RecSeqEntry.map` `WellBracketed` (a fully-recursive map interior is
a later refinement); this deliverable resolves nested *sequences* inside map keys/values, which is what
the seq locate already in hand needs. -/

/-- One key/value pair of a flow-mapping body: `key :: (block_k ++ value :: block_v)`, with the key
    and value each a recursive `emit` entry (`RecSeqEntry`). -/
inductive RecMapPair : List (Positioned YamlToken) → Prop where
  | mk (kt : Positioned YamlToken) (block_k : List (Positioned YamlToken))
      (vt : Positioned YamlToken) (block_v : List (Positioned YamlToken))
      (h_kt : kt.val = .key) (h_ke : RecSeqEntry block_k)
      (h_vt : vt.val = .value) (h_ve : RecSeqEntry block_v) :
      RecMapPair (kt :: (block_k ++ vt :: block_v))

/-- A flow-mapping body: one or more `RecMapPair`s separated by single depth-`0` `.flowEntry`
    tokens.  The map mirror of `RecSeqBody`; `.single`/`.cons` store the head-`.key` and non-empty
    facts (uniformly derivable from the pair, but stored to mirror `RecSeqBody` so the flat
    projection is a verbatim mirror — and the future producer supplies them trivially). -/
inductive RecMapBody : List (Positioned YamlToken) → Prop where
  | single (p : List (Positioned YamlToken)) (h_ne : p ≠ [])
      (h_p : RecMapPair p) (h_head : (p.head h_ne).val = .key) : RecMapBody p
  | cons (p : List (Positioned YamlToken)) (fe : Positioned YamlToken)
      (rest : List (Positioned YamlToken)) (h_ne : p ≠ [])
      (h_p : RecMapPair p) (h_head : (p.head h_ne).val = .key)
      (h_fe : fe.val = .flowEntry) (h_rest : RecMapBody rest) :
      RecMapBody (p ++ fe :: rest)

/-- **Flat projection (map side, pair level).**  A `RecMapPair` is `EntrySafe`: the key block is
    `EntrySafe` (`RecSeqEntry.toEntrySafe`), the value block is `EntrySafe`, and the delta-`0`
    `.key`/`.value` glue tokens carry the assembly via `EntrySafe_cons_delta_zero` /
    `EntrySafe_append` / `EntrySafe_singleton` — exactly how `emitPairList_scans_safebody` builds the
    per-pair `EntrySafe`, here read off the recursive witness instead of the scanner chain. -/
theorem RecMapPair.toEntrySafe {p : List (Positioned YamlToken)}
    (h : RecMapPair p) : EntrySafe p := by
  cases h with
  | mk kt block_k vt block_v h_kt h_ke h_vt h_ve =>
      refine EntrySafe_cons_delta_zero kt (block_k ++ vt :: block_v)
        (by rw [h_kt]; rfl) (by rw [h_kt]; simp) ?_
      have h_reassoc : (block_k ++ [vt]) ++ block_v = block_k ++ vt :: block_v := by
        rw [List.append_assoc]; rfl
      rw [← h_reassoc]
      exact EntrySafe_append (block_k ++ [vt]) block_v
        (EntrySafe_append block_k [vt] h_ke.toEntrySafe
          (EntrySafe_singleton vt (by rw [h_vt]; rfl) (by rw [h_vt]; simp)))
        h_ve.toEntrySafe

/-- **Flat projection (map side, body level).**  A `RecMapBody` is a flat `SafeBody (· = .key)` —
    exactly the windowed deliverable `mapBodyProps_of_windowed_safebody` consumes.  Term-mode
    structural recursion on the `RecMapBody` argument, a verbatim mirror of `RecSeqBody.toSafeBody`
    (per-pair `EntrySafe` via `RecMapPair.toEntrySafe`, head-`.key` and `.flowEntry` separators from
    the constructor fields).  This is the map-side R234 projection: it validates the recursive type
    by handing the existing map consumer joint its sole structural input, leaving the six pair-interior
    primitives as the separate residual. -/
theorem RecMapBody.toSafeBody : {l : List (Positioned YamlToken)} →
    RecMapBody l → SafeBody (fun t => t = .key) l
  | _, .single p h_ne h_p h_head => SafeBody.single p h_ne h_p.toEntrySafe h_head
  | _, .cons p fe rest h_ne h_p h_head h_fe h_rest =>
      SafeBody.cons p fe rest h_ne h_p.toEntrySafe h_head h_fe h_rest.toSafeBody

/-- **Balance projection (map side, pair level).**  A `RecMapPair` is in particular
    `WellBracketed`: the delta-`0` `.key` opener (`flowBracketDelta_key`) cons'd onto
    `block_k ++ .value :: block_v`, whose two `RecSeqEntry` blocks are each `WellBracketed`
    (`RecSeqEntry.toWellBracketed`) chained by `WellBracketed_append` across the delta-`0` `.value`
    glue (`WellBracketed_cons_delta_zero`).  The balance mirror of `RecMapPair.toEntrySafe` — same
    `.key`/`.value` delta-`0` assembly, reading each block's `WellBracketed` half instead of its
    `EntrySafe` half.  This is the navigation invariant the map *locate* needs: matching a guarded
    balanced subrange to a pair and descending into a key/value's nested interior both require that
    sub-part's own `WellBracketed`, which only the deliverable's per-block structure can supply. -/
theorem RecMapPair.toWellBracketed {p : List (Positioned YamlToken)}
    (h : RecMapPair p) : WellBracketed p := by
  cases h with
  | mk kt block_k vt block_v h_kt h_ke h_vt h_ve =>
      refine WellBracketed_cons_delta_zero kt (block_k ++ vt :: block_v)
        (by rw [h_kt]; rfl) ?_
      exact WellBracketed_append block_k (vt :: block_v) h_ke.toWellBracketed
        (WellBracketed_cons_delta_zero vt block_v (by rw [h_vt]; rfl) h_ve.toWellBracketed)

/-- **Balance projection (map side, body level).**  A `RecMapBody` is in particular
    `WellBracketed`: each pair is `WellBracketed` (`RecMapPair.toWellBracketed`) and the depth-`0`
    `.flowEntry` separators carry delta `0`, so `WellBracketed_append` + `WellBracketed_cons_delta_zero`
    chain the segments — term-mode structural recursion on the `RecMapBody` argument, a verbatim
    mirror of `RecSeqBody.toWellBracketed`.  Completes the map-side projection family
    (`EntrySafe` / `SafeBody` / `WellBracketed`) so the map descent-locator can recover the
    untyped-balance invariant at any sub-body it descends into, not just the outer one. -/
theorem RecMapBody.toWellBracketed : {l : List (Positioned YamlToken)} →
    RecMapBody l → WellBracketed l
  | _, .single p _ h_p _ => h_p.toWellBracketed
  | _, .cons p fe rest _ h_p _ h_fe h_rest =>
      WellBracketed_append p (fe :: rest) h_p.toWellBracketed
        (WellBracketed_cons_delta_zero fe rest (h_fe ▸ flowBracketDelta_flowEntry)
          h_rest.toWellBracketed)

/-! ### Emit-producer strengthening — map-body recursive deliverable (Phase J feed)

The map-side mirror of `emitList_scans_recseqbody` (Reflection 249): the `RecMapBody` strengthening
of `emitPairList_scans_safebody`.  Same consumer-joint-before-producer move at the emit boundary —
the per-pair recursive deliverable `RecMapPair` is unrecoverable from the flat per-key/per-value
handles, so key the assembler on SUPERSET per-item predicates carrying the recursive `RecSeqEntry`
of the key block (`EmitScansInFlowSavedKeyRecEntry`, a superset of `EmitScansInFlowSavedKeyBlock`)
and of the value block (`EmitScansInFlowRecEntry`, already in hand from the seq side — a key and a
value are each *one* `emit v` block, exactly what `RecSeqEntry` characterizes).  The assembler then
accumulates `RecMapBody` by the **same induction** `emitPairList_scans_safebody` uses for
`SafeBody (· = .key)` — `RecMapBody.single`/`.cons` in place of `SafeBody.single`/`.cons`, the
per-pair `RecMapPair` (built from the two `RecSeqEntry`s) in place of the per-pair `EntrySafe`, and
the recursive tail `RecMapBody block_rest` in place of `SafeBody …`.  Every other step (the colon's
placeholder→`.key` re-anchor, the value scan, the `", "` separator, the chain lift, the
`WellBracketed`/`WellTyped` glue) is transported verbatim.  Unlike the seq mirror, the `3 ≤ n`
chain-length floor stays in the output (it is load-bearing for the recursion's positivity, derived
by `omega` from the tail's floor exactly as in the flat producer), so the proof is a *truly*
verbatim mirror — only the per-pair constructor changes.  Verified-but-unconsumed: references no
sorry site, frontier sorry count unchanged; it retypes the residual one structural layer down,
reducing "deliver the top-level `RecMapBody`" to "deliver each pair's two `RecSeqEntry`s" (the next
residual: the `Grammable`-case-split per-key/per-value producers, recursing through the seq and map
assemblers). -/

/-- Per-key refinement of `EmitScansInFlowSavedKeyBlock`: scanning `emit v` as a saved key delivers
    a `block` that is not only the flat saved-key substrate (layout + `WellBracketed`/`WellTyped`/
    `EntrySafe` + take-side re-anchor) but a *recursive* `RecSeqEntry` — the deliverable the
    map-body assembler reads as a pair's key.  The map-side twin of `EmitScansInFlowRecEntry`
    (the per-value refinement): a strict superset of `EmitScansInFlowSavedKeyBlock` whose lone extra
    conjunct `RecSeqEntry block` is keyed to the *same* internal `block`, so the future per-key
    producer supplies both from one scanner run. -/
def EmitScansInFlowSavedKeyRecEntry (v : YamlValue) : Prop :=
  ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit v).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    s.simpleKeyAllowed = true →
    s.simpleKeyStack.size = s.flowLevel →
    ∃ n s' block,
      ScanChainGrew (fun t => t.val != .placeholder) s n s'
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
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.simpleKey.possible = true
      ∧ s'.simpleKey.tokenIndex = s.tokens.size
      ∧ s.tokens.size + 1 < s'.tokens.size
      ∧ (∀ (h : s.tokens.size < s'.tokens.size),
          (s'.tokens[s.tokens.size]'h).val = .placeholder)
      ∧ (∀ (h : s.tokens.size + 1 < s'.tokens.size),
          (s'.tokens[s.tokens.size + 1]'h).val = .placeholder)
      ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block
      ∧ (s'.tokens.toList.take (s.tokens.size + 1)).filter (fun t => t.val != .placeholder)
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList
      ∧ WellBracketed block
      ∧ WellTyped block
      ∧ EntrySafe block
      ∧ RecSeqEntry block

/-- **Map-body recursive-deliverable assembler** (Phase J — the `RecMapBody` strengthening of
    `emitPairList_scans_safebody`).  Given that each pair's key `emit` block is a recursive
    `RecSeqEntry` (`EmitScansInFlowSavedKeyRecEntry`) and its value `emit` block is a recursive
    `RecSeqEntry` (`EmitScansInFlowRecEntry`), the `", "`-separated `key: value` body block of
    `emitPairList pairs` is a full `RecMapBody` — `.single`/`.cons` accumulated by the same
    induction `emitPairList_scans_safebody` uses for `SafeBody (· = .key)`, with the per-pair
    `RecMapPair` (assembled from the two `RecSeqEntry`s) in place of the per-pair `EntrySafe` and the
    recursive tail `RecMapBody block_rest` in place of `SafeBody …`.  The proof is a verbatim mirror
    of `emitPairList_scans_safebody`; only the per-pair constructor changes.  Verified-but-unconsumed:
    references no sorry site, frontier sorry count unchanged. -/
theorem emitPairList_scans_recmapbody (pairs : List (YamlValue × YamlValue))
    (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansInFlowSavedKeyRecEntry p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansInFlowRecEntry p.2) :
    ∀ (s : ScannerState) (rest : List Char),
      ScannerSurfCorr s ⟨(emit.emitPairList pairs).toList ++ rest, s.col⟩ →
      s.inFlow = true →
      s.flowLevel > 0 →
      s.currentIndent < 0 →
      s.col > 0 →
      s.explicitKeyLine = none →
      AllTokensOnLine s s.line →
      EndLineOnLine s →
      s.simpleKeyAllowed = true →
      s.simpleKeyStack.size = s.flowLevel →
      ∃ n s' block,
        ScanChainGrew (fun t => t.val != .placeholder) s n s'
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
        ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block
        ∧ WellBracketed block
        ∧ WellTyped block
        ∧ RecMapBody block
        ∧ 3 ≤ n := by
  induction pairs with
  | nil => contradiction
  | cons p tail ih =>
    intro s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
    match tail, ih with
    | [], _ =>
      have h_eq : (emit.emitPairList [p]).toList ++ rest_chars =
          (emit p.1).toList ++ ([':', ' '] ++ (emit p.2).toList ++ rest_chars) := by
        simp [emit.emitPairList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      have h_ek_key : EmitScansInFlowSavedKeyRecEntry p.1 := h_all_k p (.head _)
      obtain ⟨n₁, s₁, block_k, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
              h_flow₁, h_indent₁, _h_line₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁,
              h_ska₁, h_poss₁, h_tidx₁, h_szlt₁, _h_ph0₁, h_ph1₁, h_blockeq_k, h_take_k, h_wb_k, h_wt_k, _h_es_k, h_ke⟩ :=
        h_ek_key s ([':', ' '] ++ (emit p.2).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
      have h_n₁_pos : 1 ≤ n₁ := by
        rcases Nat.eq_zero_or_pos n₁ with h0 | hpos
        · subst h0; rw [ScanChainGrew.eq_of_zero h_chain₁] at h_szlt₁; omega
        · exact hpos
      have h_sk_id := saveSimpleKey_id_of_flow_ska_false_ek_none s₁ h_flow₁ h_ska₁
          (by rw [h_ek₁]; exact h_ek)
      have h_sv : scanValueValidate (saveSimpleKey s₁) = .ok () := by
        rw [h_sk_id]
        exact scanValueValidate_ok_of_flow_allTokensOnLine s₁ h_flow₁
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂, _, _, _⟩ :=
        scanNextToken_flow_value s₁ ((emit p.2).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁
      have h_lt_k : s₁.simpleKey.tokenIndex + 1 < s₁.tokens.size := by rw [h_tidx₁]; exact h_szlt₁
      have h_ph_k : (s₁.tokens[s₁.simpleKey.tokenIndex + 1]'h_lt_k).val = .placeholder := by
        simp only [h_tidx₁]; exact h_ph1₁ h_szlt₁
      obtain ⟨s₂', pos_v, h_snt₂', h_block_colon⟩ :=
        scanNextToken_flow_value_block s₁ ((emit p.2).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁ h_ska₁ h_poss₁ h_lt_k h_ph_k
      have h_s2_eq : s₂' = s₂ := Option.some.inj (Except.ok.inj (h_snt₂'.symm.trans h_snt₂))
      rw [h_s2_eq] at h_block_colon
      have h_hk : s.tokens.size + 1 < s₁.tokens.toList.length := by
        rw [Array.length_toList]; exact h_szlt₁
      have h_old : (fun t : Positioned YamlToken => t.val != .placeholder)
          (s₁.tokens.toList[s.tokens.size + 1]'h_hk) = false := by
        have hph := h_ph1₁ h_szlt₁
        simp only [Array.getElem_toList, hph]; rfl
      have h_full : s₁.tokens.toList.filter (fun t => t.val != .placeholder)
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block_k := by
        rw [← Array.toList_filter]; exact h_blockeq_k
      have h_drop : (s₁.tokens.toList.drop (s.tokens.size + 2)).filter
            (fun t => t.val != .placeholder) = block_k :=
        List_filter_drop_succ_of_take s₁.tokens.toList (s.tokens.size + 1)
          (fun t => t.val != .placeholder) h_hk h_old _ block_k h_take_k h_full
      rw [h_tidx₁, h_take_k, h_drop] at h_block_colon
      have h_block_kc : (s₂.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ (⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                (block_k ++ [⟨pos_v, .value, pos_v⟩])) := by
        rw [h_block_colon]; simp only [List.append_assoc, List.cons_append]
      obtain ⟨c_v, rest_v, h_first_v, h_nws_v, h_nlb_v, h_nc_v⟩ := emit_first_char p.2
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: c_v :: (rest_v ++ rest_chars), s₂.col⟩ := by
        have h_eq_chars : (' ' :: (emit p.2).toList ++ rest_chars) =
            (' ' :: c_v :: (rest_v ++ rest_chars)) := by
          congr 1; rw [h_first_v]; simp only [List.cons_append]
        exact h_eq_chars ▸ h_corr₂
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _, _⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ c_v (rest_v ++ rest_chars) h_corr₂_ws
          h_flow₂ h_nws_v h_nlb_v h_nc_v h_indent₂
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit p.2).toList ++ rest_chars, s₃.col⟩ := by
        have h_eq_chars : (c_v :: (rest_v ++ rest_chars)) =
            ((emit p.2).toList ++ rest_chars) := by
          rw [h_first_v]; simp only [List.cons_append]
        exact h_eq_chars ▸ h_corr₃
      have h_ev : EmitScansInFlowRecEntry p.2 := h_all_v p (.head _)
      obtain ⟨n_v, s_end, block_v, h_chain_v, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, _h_ska_v, _h_last_v,
              h_atol_end, h_endline_end, h_stack_end, h_fmc_v, h_blockeq_v, h_wb_v, h_wt_v, _h_es_v, _h_eu_v, h_ve, _h_cs_v⟩ :=
        h_ev s₃ rest_chars h_corr₃'
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_indent₂)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃]; exact h_ek₂)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
          (by rw [h_stack_pp₃, h_stack_v₂, h_stack₁, h_fl₃, h_fl₂, h_fl₁]; exact h_sync)
      have h_snt_eq : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n_v_pos : n_v ≥ 1 := by
        match n_v, h_chain_v with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit p.2).toList = [] := by
            match h_list : (emit p.2).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.2
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n_v', rfl⟩ : ∃ k, n_v = k + 1 := ⟨n_v - 1, by omega⟩
      have h_filt_le : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                       (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws : ScanChainGrew (fun t => t.val != .placeholder)
            s₂ (n_v' + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq h_filt_le h_chain_v
      have h_grew₂ : (s₂.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₁.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorr s₁
            ⟨':' :: (' ' :: (emit p.2).toList ++ rest_chars), s₁.col⟩ := by
          have : [':', ' '] ++ (emit p.2).toList ++ rest_chars =
              ':' :: (' ' :: (emit p.2).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextToken_filtered_grows_in_flow s₁ s₂ ':'
          (' ' :: (emit p.2).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      have h_fmc_v' : FlowMonoChain s.flowLevel s₃ (n_v' + 1) s_end :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc_v
      have h_fmc_ws : FlowMonoChain s.flowLevel s₂ (n_v' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq (by omega) h_fmc_v'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans h_fmc_ws)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans h_chain_ws)
      have h_arith : n₁ + (1 + (n_v' + 1)) = n₁ + 1 + (n_v' + 1) := by omega
      have h_block_end : (s_end.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ ((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                  (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) := by
        have h_s3_s2 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList := by
          rw [h_toks_pp₃]
        rw [h_blockeq_v, h_s3_s2, h_block_kc, List.append_assoc]
      -- Per-pair entry `EntrySafe`: `.key`/`.value` glue (delta 0) around `EntrySafe` blocks.
      have h_pair : RecMapPair ((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
            (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) := by
        have h_reassoc_pair : (⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
              (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v
            = ⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
              (block_k ++ ⟨pos_v, .value, pos_v⟩ :: block_v) := by
          rw [List.cons_append, List.append_assoc]; rfl
        rw [h_reassoc_pair]
        exact RecMapPair.mk _ block_k _ block_v (by rfl) h_ke (by rfl) h_ve
      refine ⟨n₁ + 1 + (n_v' + 1), s_end,
        (⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ :: (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v,
        h_arith ▸ h_chain_all, h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end,
        ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, h_block_end, ?_, ?_, ?_, by omega⟩
      · rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek₃, h_ek₂]; exact h_ek.symm
      · rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp₃, h_stack_v₂, h_stack₁]
      · -- WellBracketed ((.key :: block_k ++ [.value]) ++ block_v): delta-`0` `.key`/`.value`
        -- glue around the key/value `WellBracketed` blocks (mirrors the per-pair WellBracketed assembly).
        exact WellBracketed_cons_delta_zero _ _ (by rfl)
          (WellBracketed_append _ _
            (WellBracketed_append _ _ h_wb_k (WellBracketed_singleton_delta_zero _ (by rfl)))
            h_wb_v)
      · -- WellTyped ((.key :: block_k ++ [.value]) ++ block_v) — typed twin.
        exact WellTyped_cons_delta_zero _ _ (by rfl)
          (WellTyped_append _ _
            (WellTyped_append _ _ h_wt_k (WellTyped_singleton_delta_zero _ (by rfl)))
            h_wt_v)
      · -- RecMapBody ((.key :: block_k ++ [.value]) ++ block_v)
        exact RecMapBody.single _ (by exact List.cons_ne_nil _ _) h_pair (by rfl)
    | p' :: ps, ih =>
      have h_eq : (emit.emitPairList (p :: p' :: ps)).toList ++ rest_chars =
          (emit p.1).toList ++ ([':', ' '] ++ (emit p.2).toList ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
        simp [emit.emitPairList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      have h_ek_key : EmitScansInFlowSavedKeyRecEntry p.1 := h_all_k p (.head _)
      obtain ⟨n₁, s₁, block_k, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
              h_flow₁, h_indent₁, _h_line₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁,
              h_ska₁, h_poss₁, h_tidx₁, h_szlt₁, _h_ph0₁, h_ph1₁, h_blockeq_k, h_take_k, h_wb_k, h_wt_k, _h_es_k, h_ke⟩ :=
        h_ek_key s ([':', ' '] ++ (emit p.2).toList ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
      have h_sk_id := saveSimpleKey_id_of_flow_ska_false_ek_none s₁ h_flow₁ h_ska₁
          (by rw [h_ek₁]; exact h_ek)
      have h_sv : scanValueValidate (saveSimpleKey s₁) = .ok () := by
        rw [h_sk_id]
        exact scanValueValidate_ok_of_flow_allTokensOnLine s₁ h_flow₁
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂, _, _, _⟩ :=
        scanNextToken_flow_value s₁
          ((emit p.2).toList ++ [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁
      have h_lt_k : s₁.simpleKey.tokenIndex + 1 < s₁.tokens.size := by rw [h_tidx₁]; exact h_szlt₁
      have h_ph_k : (s₁.tokens[s₁.simpleKey.tokenIndex + 1]'h_lt_k).val = .placeholder := by
        simp only [h_tidx₁]; exact h_ph1₁ h_szlt₁
      obtain ⟨s₂', pos_v, h_snt₂', h_block_colon⟩ :=
        scanNextToken_flow_value_block s₁
          ((emit p.2).toList ++ [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁ h_ska₁ h_poss₁ h_lt_k h_ph_k
      have h_s2_eq : s₂' = s₂ := Option.some.inj (Except.ok.inj (h_snt₂'.symm.trans h_snt₂))
      rw [h_s2_eq] at h_block_colon
      have h_hk : s.tokens.size + 1 < s₁.tokens.toList.length := by
        rw [Array.length_toList]; exact h_szlt₁
      have h_old : (fun t : Positioned YamlToken => t.val != .placeholder)
          (s₁.tokens.toList[s.tokens.size + 1]'h_hk) = false := by
        have hph := h_ph1₁ h_szlt₁
        simp only [Array.getElem_toList, hph]; rfl
      have h_full : s₁.tokens.toList.filter (fun t => t.val != .placeholder)
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block_k := by
        rw [← Array.toList_filter]; exact h_blockeq_k
      have h_drop : (s₁.tokens.toList.drop (s.tokens.size + 2)).filter
            (fun t => t.val != .placeholder) = block_k :=
        List_filter_drop_succ_of_take s₁.tokens.toList (s.tokens.size + 1)
          (fun t => t.val != .placeholder) h_hk h_old _ block_k h_take_k h_full
      rw [h_tidx₁, h_take_k, h_drop] at h_block_colon
      have h_block_kc : (s₂.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ (⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                (block_k ++ [⟨pos_v, .value, pos_v⟩])) := by
        rw [h_block_colon]; simp only [List.append_assoc, List.cons_append]
      obtain ⟨c_v, rest_v, h_first_v, h_nws_v, h_nlb_v, h_nc_v⟩ := emit_first_char p.2
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: c_v :: (rest_v ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₂.col⟩ := by
        have h_eq_chars : (' ' :: (emit p.2).toList ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) =
            (' ' :: c_v :: (rest_v ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)) := by
          congr 1; rw [h_first_v]; simp only [List.cons_append, List.append_assoc]
        exact h_eq_chars ▸ h_corr₂
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _, _⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ c_v
          (rest_v ++ [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₂_ws h_flow₂ h_nws_v h_nlb_v h_nc_v h_indent₂
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit p.2).toList ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars, s₃.col⟩ := by
        have h_eq_chars : (c_v :: (rest_v ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)) =
            ((emit p.2).toList ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
          rw [h_first_v]; simp only [List.cons_append, List.append_assoc]
        exact h_eq_chars ▸ h_corr₃
      have h_ev : EmitScansInFlowRecEntry p.2 := h_all_v p (.head _)
      have h_corr₃_assoc : ScannerSurfCorr s₃
          ⟨(emit p.2).toList ++ ([',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₃.col⟩ := by
        simp only [List.append_assoc] at h_corr₃' ⊢; exact h_corr₃'
      obtain ⟨n_v, s_v, block_v, h_chain_v, h_corr_v, h_fl_v, h_dp_v, h_ids_v,
              h_ek_v, h_col_v, h_flow_v, h_indent_v, _h_line_v, h_ska_v, h_last_v,
              h_atol_v, h_endline_v, h_stack_v, h_fmc_v, h_blockeq_v, h_wb_v, h_wt_v, _h_es_v, _h_eu_v, h_ve, _h_cs_v⟩ :=
        h_ev s₃ ([',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₃_assoc
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_indent₂)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃]; exact h_ek₂)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
          (by rw [h_stack_pp₃, h_stack_v₂, h_stack₁, h_fl₃, h_fl₂, h_fl₁]; exact h_sync)
      have h_snt_eq_v : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n_v_pos : n_v ≥ 1 := by
        match n_v, h_chain_v with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_v.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit p.2).toList = [] := by
            match h_list : (emit p.2).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.2
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n_v', rfl⟩ : ∃ k, n_v = k + 1 := ⟨n_v - 1, by omega⟩
      have h_filt_le_v : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                         (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws_v : ScanChainGrew (fun t => t.val != .placeholder)
            s₂ (n_v' + 1) s_v :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq_v h_filt_le_v h_chain_v
      have h_grew₂ : (s₂.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₁.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorr s₁
            ⟨':' :: (' ' :: (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₁.col⟩ := by
          have : [':', ' '] ++ (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars =
              ':' :: (' ' :: (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextToken_filtered_grows_in_flow s₁ s₂ ':'
          (' ' :: (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      obtain ⟨s_c, h_snt_c, h_corr_c, h_fl_c, h_dp_c, h_ids_c, h_ek_c, h_col_c, _h_line_c, h_atol_c, h_endline_c, h_stack_c⟩ :=
        scanNextToken_flow_comma s_v
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v h_flow_v h_indent_v h_col_v h_last_v h_atol_v h_endline_v
      obtain ⟨feTok, h_feTok_val, h_comma_eq⟩ :=
        scanNextToken_flow_comma_filtered_push s_v
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v h_flow_v h_indent_v h_col_v h_last_v h_snt_c
      obtain ⟨h_ska_c_true, _h_sk_c_eq⟩ :=
        scanNextToken_flow_comma_simpleKey s_v
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v h_flow_v h_indent_v h_col_v h_last_v h_snt_c
      obtain ⟨c_p, rest_p, h_first_p, h_nws_p, h_nlb_p, h_nc_p⟩ :=
        emitPairList_first_char p' ps
      have h_corr_c_ws : ScannerSurfCorr s_c
          ⟨' ' :: c_p :: (rest_p ++ rest_chars), s_c.col⟩ := by
        have : ' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars =
            ' ' :: c_p :: (rest_p ++ rest_chars) := by
          rw [h_first_p]; simp only [List.cons_append]
        rwa [this] at h_corr_c
      have h_sc_flow : s_c.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl_c]; omega)
      have h_sc_indent : s_c.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids_c]; exact h_indent_v
      obtain ⟨s_pp, h_corr_pp, h_flow_pp, h_fl_pp, h_indent_pp, h_col_pp,
              h_dp_pp, h_ids_pp, h_ek_pp, _h_line_pp, h_pp_eq_r, h_atol_transfer_pp, h_endline_transfer_pp, h_stack_pp, h_toks_pp, h_sk_pp, h_ska_pp⟩ :=
        scanNextToken_preprocess_flow_ws1 s_c c_p (rest_p ++ rest_chars) h_corr_c_ws
          h_sc_flow h_nws_p h_nlb_p h_nc_p h_sc_indent
      have h_corr_pp' : ScannerSurfCorr s_pp
          ⟨(emit.emitPairList (p' :: ps)).toList ++ rest_chars, s_pp.col⟩ := by
        have : c_p :: (rest_p ++ rest_chars) =
            (emit.emitPairList (p' :: ps)).toList ++ rest_chars := by
          rw [h_first_p]; simp only [List.cons_append]
        rwa [this] at h_corr_pp
      have h_tail_all_k : ∀ q ∈ p' :: ps, EmitScansInFlowSavedKeyRecEntry q.1 :=
        fun q hq => h_all_k q (.tail _ hq)
      have h_tail_all_v : ∀ q ∈ p' :: ps, EmitScansInFlowRecEntry q.2 :=
        fun q hq => h_all_v q (.tail _ hq)
      obtain ⟨n_r, s_end, block_rest, h_chain_r, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end, h_endline_end, h_stack_end, h_fmc_r, h_blockeq_rest, h_wb_rest, h_wt_rest, h_rec_rest, h_n_r_ge3⟩ :=
        ih (by simp) h_tail_all_k h_tail_all_v s_pp rest_chars h_corr_pp'
          h_flow_pp
          (by rw [h_fl_pp, h_fl_c]; rw [h_fl_v, h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent_pp]; exact h_sc_indent)
          (by rw [h_col_pp]; omega)
          (by rw [h_ek_pp, h_ek_c, h_ek_v, h_ek₃]; exact h_ek₂)
          (h_atol_transfer_pp h_atol_c)
          (h_endline_transfer_pp h_endline_c)
          (by rw [h_ska_pp]; exact h_ska_c_true)
          (by rw [h_stack_pp, h_stack_c, h_stack_v, h_stack_pp₃, h_stack_v₂, h_stack₁,
              h_sync, h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁])
      have h_snt_eq_r : scanNextToken s_c = scanNextToken s_pp :=
        scanNextToken_eq_of_preprocess s_c s_pp h_pp_eq_r
      have h_n_r_pos : n_r ≥ 1 := by omega
      obtain ⟨n_r', rfl⟩ : ∃ k, n_r = k + 1 := ⟨n_r - 1, by omega⟩
      have h_filt_le_r : (s_c.tokens.filter (fun t => t.val != .placeholder)).size ≤
                         (s_pp.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp]; exact Nat.le_refl _
      have h_chain_ws_r : ScanChainGrew (fun t => t.val != .placeholder)
            s_c (n_r' + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq_r h_filt_le_r h_chain_r
      have h_grew_c : (s_c.tokens.filter (fun t => t.val != .placeholder)).size >
                      (s_v.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr_v_cons : ScannerSurfCorr s_v
            ⟨',' :: (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s_v.col⟩ := by
          have : [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars =
              ',' :: (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr_v
        exact scanNextToken_filtered_grows_in_flow s_v s_c ','
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v_cons h_flow_v h_indent_v h_col_v
          (by decide) (by decide) (by decide) h_snt_c
      have h_fmc_v' : FlowMonoChain s.flowLevel s₃ (n_v' + 1) s_v :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc_v
      have h_fmc_ws_v : FlowMonoChain s.flowLevel s₂ (n_v' + 1) s_v :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq_v (by omega) h_fmc_v'
      have h_fmc_r' : FlowMonoChain s.flowLevel s_pp (n_r' + 1) s_end :=
        (show s.flowLevel = s_pp.flowLevel from by omega) ▸ h_fmc_r
      have h_fmc_ws_r : FlowMonoChain s.flowLevel s_c (n_r' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq_r (by omega) h_fmc_r'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans
          (h_fmc_ws_v.trans
            ((FlowMonoChain.single h_snt_c (by omega) (by omega)).trans h_fmc_ws_r)))
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans
          (h_chain_ws_v.trans
            ((ScanChainGrew.single h_snt_c h_grew_c).trans h_chain_ws_r)))
      have h_arith : n₁ + (1 + ((n_v' + 1) + (1 + (n_r' + 1)))) =
          n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1) := by omega
      have h_block_end : (s_end.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ ((((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                  (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) ++ [feTok]) ++ block_rest) := by
        have h_s3_s2 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList := by
          rw [h_toks_pp₃]
        have h_block_v_end : (s_v.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s.tokens.filter (fun t => t.val != .placeholder)).toList
              ++ ((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                  (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) := by
          rw [h_blockeq_v, h_s3_s2, h_block_kc, List.append_assoc]
        have h_block_c_end : (s_c.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s.tokens.filter (fun t => t.val != .placeholder)).toList
              ++ (((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                  (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) ++ [feTok]) := by
          rw [congrArg Array.toList h_comma_eq, Array.toList_push, h_block_v_end, List.append_assoc]
        have h_s_pp_c : (s_pp.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s_c.tokens.filter (fun t => t.val != .placeholder)).toList := by
          rw [h_toks_pp]
        rw [h_blockeq_rest, h_s_pp_c, h_block_c_end, List.append_assoc]
      -- Per-pair entry `EntrySafe`, glued by delta-0 `.key`/`.value` tokens.
      have h_pair : RecMapPair ((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
            (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) := by
        have h_reassoc_pair : (⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
              (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v
            = ⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
              (block_k ++ ⟨pos_v, .value, pos_v⟩ :: block_v) := by
          rw [List.cons_append, List.append_assoc]; rfl
        rw [h_reassoc_pair]
        exact RecMapPair.mk _ block_k _ block_v (by rfl) h_ke (by rfl) h_ve
      refine ⟨n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1), s_end,
        (((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ :: (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) ++ [feTok]) ++ block_rest,
        h_arith ▸ h_chain_all, h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end,
        ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, h_block_end, ?_, ?_, ?_, by omega⟩
      · rw [h_fl_end, h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp_pp, h_dp_c, h_dp_v, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids_pp, h_ids_c, h_ids_v, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek_pp, h_ek_c, h_ek_v, h_ek₃]; exact h_ek₂.trans h_ek.symm
      · rw [h_line_end, _h_line_pp, _h_line_c, _h_line_v, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp, h_stack_c, h_stack_v, h_stack_pp₃, h_stack_v₂, h_stack₁]
      · -- WellBracketed ((entry ++ [feTok]) ++ block_rest): per-pair entry (delta-`0` `.key`/
        -- `.value` glue) ++ delta-`0` `.flowEntry` separator ++ recursive tail (`h_wb_rest`).
        exact WellBracketed_append _ _
          (WellBracketed_append _ _
            (WellBracketed_cons_delta_zero _ _ (by rfl)
              (WellBracketed_append _ _
                (WellBracketed_append _ _ h_wb_k (WellBracketed_singleton_delta_zero _ (by rfl)))
                h_wb_v))
            (WellBracketed_singleton_delta_zero feTok
              (by rw [h_feTok_val]; exact flowBracketDelta_flowEntry)))
          h_wb_rest
      · -- WellTyped ((entry ++ [feTok]) ++ block_rest) — typed twin of the WellBracketed bullet.
        exact WellTyped_append _ _
          (WellTyped_append _ _
            (WellTyped_cons_delta_zero _ _ (by rfl)
              (WellTyped_append _ _
                (WellTyped_append _ _ h_wt_k (WellTyped_singleton_delta_zero _ (by rfl)))
                h_wt_v))
            (WellTyped_singleton_delta_zero feTok
              (by rw [h_feTok_val]; exact flowBracketDelta_flowEntry)))
          h_wt_rest
      · -- RecMapBody ((entry ++ [feTok]) ++ block_rest)
        have h_reassoc : (((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
              (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) ++ [feTok]) ++ block_rest
            = ((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
              (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) ++ feTok :: block_rest := by
          rw [List.append_assoc]; rfl
        rw [h_reassoc]
        exact RecMapBody.cons _ feTok block_rest (by exact List.cons_ne_nil _ _)
          h_pair (by rfl) h_feTok_val h_rec_rest

/-- **Map-body recursive seed** (Phase J — the `RecMapBody` analog of
    `emitPairList_body_filtered_characterization`, and the symmetric mirror of the seq-body seed
    `emitList_body_recseqbody`).  Where the flat characterization packages the flat map-body content,
    this one packages `emitPairList_scans_recmapbody` into the body's *recursive* deliverable,
    restated positionally: the `drop old_sz` tail of the final filtered token list is one
    `RecMapBody`.  This is the **root the locate recursion descends from** on the map side — the
    outer-window (`lo = old_sz`) leaf of the per-window `RecMapBody` producer
    `flowSubrangesOk_of_window_producers` consumes: at the body-interior span `[2, size-2)` the window
    `(take (size-2)).drop 2` is exactly this `drop old_sz` tail, so this is the map-side universal
    producer's base case; the recursion navigates this top-level structure down to every nested
    guarded subrange.  Keyed on BOTH per-item recursive hypotheses the map feed reads —
    `EmitScansInFlowSavedKeyRecEntry` (every key) and `EmitScansInFlowRecEntry` (every value) — plus
    the extra `simpleKeyAllowed = true` precondition the map feed needs that the seq feed does not
    (the R246 stored-vs-projected asymmetry surfacing one tier up, at the seed's hypothesis count).
    Verified-but-unconsumed until the locate lands: composes only `emitPairList_scans_recmapbody` +
    the positional `drop` (`h_drop`, verbatim from the seq seed), references no sorry site, frontier
    sorry count unchanged. -/
theorem emitPairList_body_recmapbody
    (pairs : List (YamlValue × YamlValue)) (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansInFlowSavedKeyRecEntry p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansInFlowRecEntry p.2)
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
    ∧ RecMapBody ((s'.tokens.filter p).toList.drop old_sz) := by
  obtain ⟨n, s', block, h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, h_block_eq, h_wb, h_wt, h_rec, _h_n3⟩ :=
    emitPairList_scans_recmapbody pairs h_ne h_all_k h_all_v s rest h_corr h_flow h_fl h_indent h_col
      h_ek h_atol h_endline h_ska h_sync
  -- The body block is exactly the `drop old_sz` of the final filtered token list (verbatim from
  -- the seq seed `emitList_body_recseqbody`).
  have h_drop : (s'.tokens.filter (fun t => t.val != .placeholder)).toList.drop
      (s.tokens.filter (fun t => t.val != .placeholder)).size = block := by
    rw [h_block_eq,
      show (s.tokens.filter (fun t => t.val != .placeholder)).size
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList.length
        from Array.length_toList.symm,
      List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
  refine ⟨n, s', h_chain.toScanChain, h_corr', h_fl', h_dp', h_ids', h_ek',
          h_col', h_inflow', h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, ?_⟩
  show RecMapBody ((s'.tokens.filter (fun t => t.val != .placeholder)).toList.drop
      (s.tokens.filter (fun t => t.val != .placeholder)).size)
  rw [h_drop]; exact h_rec

/-! ### Emit-producer strengthening — value-side `RecSeqEntry` deliverable (Phase J feed)

The per-value producer `emit_scans_in_flow_rec_entry : Grammable v inFlow → EmitScansInFlowRecEntry v`
closes the value half of the emit feed: it strengthens the flat block producer `emit_scans_in_flow_block`
to additionally deliver `RecSeqEntry block`, the per-item recursive deliverable both
`emitList_scans_recseqbody` (every seq item) and `emitPairList_scans_recmapbody` (every map value)
read as a bare hypothesis.  It is **self-contained** — a single `Grammable` induction:

  * `scalar` → `RecSeqEntry.scalar` (the single token is the entry);
  * `sequence` → `RecSeqEntry.seqEmpty`/`RecSeqEntry.seq`, the body block scanned by
    `emitList_scans_recseqbody` fed by this induction's own IH (per-item `EmitScansInFlowRecEntry`);
  * `mapping` → `RecSeqEntry.map`, which **stores only `WellBracketed interior`** (R244 — projections track
    stored fields), already supplied by the flat mapping proof, so the value side needs **no** map-body
    recursion and **no** saved-key dependency.  The flat conjuncts are re-derived verbatim from the flat
    combined producer's `block` cases, with the map case's per-pair key/value sub-producers supplied by the
    black-box flat wrappers `emit_scans_in_flow_saved_key_block`/`emit_scans_in_flow_block`.

The proof is a verbatim mirror of `emit_scans_block_combined`'s three `block` cases; only the per-entry
`RecSeqEntry` leaf is woven in (and the seq body scan swapped for its recursive twin).
Verified-but-unconsumed: references no sorry site, frontier sorry count unchanged. -/
set_option maxHeartbeats 1600000 in
theorem emit_scans_in_flow_rec_entry (v : YamlValue) {inFlow : Bool}
    (hg : Grammable v inFlow) : EmitScansInFlowRecEntry v := by
  induction hg with
  | scalar sc _ h =>
      intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline _h_sync
      have h_chars : (emit (.scalar sc)).toList ++ rest =
          ['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest := by
        simp only [emit, emitScalar, String.toList_append]; rfl
      have hcorr' : ScannerSurfCorr s_state
          ⟨['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest, s_state.col⟩ := by
        rwa [← h_chars]
      have hcorr_q : ScannerSurfCorr s_state
          ⟨'"' :: ((escapeString sc.content).toList ++ ['"'] ++ rest), s_state.col⟩ := by
        have : ['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest =
            '"' :: ((escapeString sc.content).toList ++ ['"'] ++ rest) := by
          simp only [List.cons_append, List.nil_append, List.append_assoc]
        rwa [this] at hcorr'
      obtain ⟨s', h_snt, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_tok', h_ska', _h_line', h_atol', h_endline', h_stack'⟩ :=
        scanNextToken_flow_scanDoubleQuoted s_state sc.content rest hcorr' h_flow h_indent h_col
          h_atol h_endline
      have h_grew : (s'.tokens.filter (fun t => t.val != .placeholder)).size >
                    (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s_state s' '"'
          ((escapeString sc.content).toList ++ ['"'] ++ rest) hcorr_q
          h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt
      obtain ⟨tok, str, st, h_tok_val, h_push⟩ :=
        scanNextToken_flow_scalar_filtered_push s_state ((escapeString sc.content).toList ++ ['"'] ++ rest)
          hcorr_q h_flow h_indent h_col h_snt
      refine ⟨1, s', [tok], ScanChainGrew.single h_snt h_grew, h_corr', h_fl', h_dp', h_ids', h_ek',
        h_col', ?_, ?_, _h_line', h_ska', h_tok', h_atol', h_endline', h_stack',
        FlowMonoChain.single h_snt (Nat.le.refl) (by omega), ?_, ?_, ?_, ?_,
        EntryUnit_scalar tok str st h_tok_val, RecSeqEntry.scalar tok str st h_tok_val, ?_⟩
      · unfold ScannerState.inFlow; rw [h_fl']
        unfold ScannerState.inFlow at h_flow; exact h_flow
      · unfold ScannerState.currentIndent; rw [h_ids']; exact h_indent
      · rw [h_push, Array.toList_push]
      · exact WellBracketed_singleton_delta_zero tok (by rw [h_tok_val]; exact flowBracketDelta_scalar str st)
      · exact WellTyped_singleton_delta_zero tok (by rw [h_tok_val]; exact flowBracketDelta_scalar str st)
      · exact EntrySafe_scalar tok str st h_tok_val
      · exact ⟨List.cons_ne_nil _ _, Or.inl ⟨str, st, by rw [List.head_cons]; exact h_tok_val⟩⟩
  | sequence style items tag anchor _ h ih =>
      intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
      have h_chars : (emit (.sequence style items tag anchor)).toList ++ rest =
          ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest := by
        simp only [emit, String.toList_append]; rfl
      have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
      have h_corr_state_cons : ScannerSurfCorr s_state
          ⟨'[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest), s_state.col⟩ := by
        have : ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest =
            '[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest) := by
          simp only [List.cons_append, List.nil_append, List.append_assoc]
        rwa [this] at hcorr₀
      obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁, h_endline₁, h_stack_endline₁, h_stack_pop₁, _h_sk_poss₁, _h_toks_gt₁, h_stack_push₁⟩ :=
        scanNextToken_flow_open_nested s_state
          ((emit.emitList items.toList).toList ++ [']'] ++ rest) hcorr₀ h_flow h_indent h_col
          h_atol h_endline
      have h_fl₁_ge2 : s₁.flowLevel ≥ 2 := by rw [h_fl₁]; omega
      have h_s1_inflow : s₁.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
      have h_s1_indent : s₁.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
      have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
      have h_s1_sync : s₁.simpleKeyStack.size = s₁.flowLevel := by
        rw [h_stack_push₁, Array.size_push, h_sync, h_fl₁]
      obtain ⟨fssTok, h_fss_val, h_open_push⟩ :=
        scanNextToken_flow_open_seq_filtered_push s_state
          ((emit.emitList items.toList).toList ++ [']'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col h_snt₁
      have h_corr₁_assoc : ScannerSurfCorr s₁
          ⟨(emit.emitList items.toList).toList ++ ([']'] ++ rest), s₁.col⟩ := by
        rw [List.append_assoc] at h_corr₁; exact h_corr₁
      obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
              h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
              h_body_append, h_body_wb, h_body_wt, h_entry_builder⟩ :
          (∃ n₂ s₂ bodyBlock,
            ScanChainGrew (fun t => t.val != .placeholder) s₁ n₂ s₂
            ∧ ScannerSurfCorr s₂ ⟨[']'] ++ rest, s₂.col⟩
            ∧ s₂.flowLevel = s₁.flowLevel
            ∧ s₂.directivesPresent = s₁.directivesPresent
            ∧ s₂.indents = s₁.indents
            ∧ s₂.explicitKeyLine = s₁.explicitKeyLine
            ∧ s₂.col > 0
            ∧ s₂.inFlow = true
            ∧ s₂.currentIndent < 0
            ∧ s₂.line = s₁.line
            ∧ AllTokensOnLine s₂ s₂.line
            ∧ EndLineOnLine s₂
            ∧ s₂.simpleKeyStack = s₁.simpleKeyStack
            ∧ FlowMonoChain s₁.flowLevel s₁ n₂ s₂
            ∧ (s₂.tokens.filter (fun t => t.val != .placeholder)).toList
                = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList ++ bodyBlock
            ∧ WellBracketed bodyBlock
            ∧ WellTyped bodyBlock
            ∧ (∀ (fss fse : Positioned YamlToken),
                fss.val = .flowSequenceStart → fse.val = .flowSequenceEnd →
                  RecSeqEntry (fss :: (bodyBlock ++ [fse])))) := by
        match h_list : items.toList with
        | [] =>
          refine ⟨0, s₁, [], .zero, ?_, rfl, rfl, rfl, rfl, h_s1_col, h_s1_inflow, h_s1_indent, rfl,
                  h_atol₁, h_endline₁, rfl, .zero (Nat.le.refl), ?_, WellBracketed_nil, WellTyped_nil,
                  fun fss fse hf1 hf2 => RecSeqEntry.seqEmpty fss fse hf1 hf2⟩
          · have h_e : (emit.emitList items.toList).toList ++ ([']'] ++ rest) = [']'] ++ rest := by
              rw [h_list]; simp only [emit.emitList]; rfl
            rw [h_e] at h_corr₁_assoc; exact h_corr₁_assoc
          · simp
        | w :: ws =>
          have h_all_rec : ∀ u ∈ (w :: ws), EmitScansInFlowRecEntry u := fun u hu => by
            have hu' : u ∈ items.toList := h_list ▸ hu
            have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hu'
            have h_sz : i < items.size := by rwa [Array.length_toList] at hi
            exact h_eq ▸ ih ⟨i, h_sz⟩
          obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
                  h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
                  h_body_append, h_body_wb, h_body_wt, h_body_rec⟩ :=
            emitList_scans_recseqbody (w :: ws) (by simp) h_all_rec s₁ ([']'] ++ rest)
              (h_list ▸ h_corr₁_assoc) h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
              (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁ h_s1_sync
          exact ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
                 h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
                 h_body_append, h_body_wb, h_body_wt,
                 fun fss fse hf1 hf2 => RecSeqEntry.seq fss fse bodyBlock hf1 hf2 h_body_wb h_body_rec⟩
      have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
      have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
        unfold StackEndLineOnLine at h_stack_endline₁ ⊢
        rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
      obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃, _h_line₃, h_atol₃, h_endline₃, h_stack₃, _, _⟩ :=
        scanNextToken_flow_close_seq_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
          h_atol₂ h_stack_endline₂
      have h_corr₂_cons : ScannerSurfCorr s₂ ⟨']' :: rest, s₂.col⟩ := by
        have : [']'] ++ rest = ']' :: rest := by simp
        rwa [this] at h_corr₂
      obtain ⟨fseTok, h_fse_val, h_close_push⟩ :=
        scanNextToken_flow_close_seq_filtered_push s₂ rest h_corr₂_cons h_s2_inflow h_s2_indent h_col₂
          h_fl₂_ge2 h_snt₃
      have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ := h_fmc₂.weaken (by omega)
      have h_fmc_all :=
        (FlowMonoChain.single h_snt₁ (Nat.le.refl) (by omega)).trans
          (h_fmc₂'.trans (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
      have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s_state s₁ '['
          ((emit.emitList items.toList).toList ++ [']'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt₁
      have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₂.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s₂ s₃ ']' rest
          h_corr₂_cons h_s2_inflow h_s2_indent h_col₂ (by decide) (by decide) (by decide) h_snt₃
      have h_block_eq : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ (fssTok :: (bodyBlock ++ [fseTok])) := by
        have h1 : (s₁.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fssTok] := by
          rw [h_open_push, Array.toList_push]
        have h3 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fseTok] := by
          rw [h_close_push, Array.toList_push]
        rw [h3, h_body_append, h1]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have h_wrap := wrap_seq_block fssTok fseTok bodyBlock h_fss_val h_fse_val h_body_wb
      have h_wrap_t := wrap_seq_typed fssTok fseTok bodyBlock h_fss_val h_fse_val h_body_wt
      refine ⟨(1 + n₂) + 1, s₃, fssTok :: (bodyBlock ++ [fseTok]),
        (ScanChainGrew.single h_snt₁ h_grew₁).trans (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
        h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_ska₃, h_tok₃, ?_, ?_, ?_, h_fmc_all,
        h_block_eq, h_wrap.1, h_wrap_t, h_wrap.2,
        EntryUnit_wrap fssTok fseTok bodyBlock (h_fss_val ▸ flowBracketDelta_flowSequenceStart)
          (h_fse_val ▸ flowBracketDelta_flowSequenceEnd) h_body_wb, h_entry_builder fssTok fseTok h_fss_val h_fse_val, ?_⟩
      · rw [h_fl₃, h_fl₂, h_fl₁]; omega
      · rw [h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek₃, h_ek₂, h_ek₁]
      · rw [h_col₃]; omega
      · unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
      · unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
      · rw [_h_line₃, _h_line₂, _h_line₁]
      · exact h_atol₃
      · exact h_endline₃
      · rw [h_stack₃, h_stack₂, h_stack_pop₁]
      · exact ⟨List.cons_ne_nil _ _, Or.inr (Or.inl (by rw [List.head_cons]; exact h_fss_val))⟩
  | mapping style pairs tag anchor _ hk hv ihk ihv =>
      intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
      have h_chars : (emit (.mapping style pairs tag anchor)).toList ++ rest =
          ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest := by
        simp only [emit, String.toList_append]; rfl
      have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
      have h_corr_state_cons : ScannerSurfCorr s_state
          ⟨'{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest), s_state.col⟩ := by
        have : ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest =
            '{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) := by
          simp only [List.cons_append, List.nil_append, List.append_assoc]
        rwa [this] at hcorr₀
      obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁, h_endline₁, h_stack_endline₁, h_stack_pop₁, _h_sk_poss₁, _h_toks_gt₁, h_stack_push₁⟩ :=
        scanNextToken_flow_open_mapping_nested s_state
          ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) hcorr₀ h_flow h_indent h_col
          h_atol h_endline
      have h_fl₁_ge2 : s₁.flowLevel ≥ 2 := by rw [h_fl₁]; omega
      have h_s1_inflow : s₁.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
      have h_s1_indent : s₁.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
      have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
      have h_s1_ska : s₁.simpleKeyAllowed = true :=
        scanNextToken_flow_open_mapping_ska s_state s₁
          ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col h_snt₁
      have h_s1_sync : s₁.simpleKeyStack.size = s₁.flowLevel := by
        rw [h_stack_push₁, Array.size_push, h_sync, h_fl₁]
      obtain ⟨fmsTok, h_fms_val, h_open_push⟩ :=
        scanNextToken_flow_open_map_filtered_push s_state
          ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col h_snt₁
      have h_pair_scan : EmitPairListScansInFlowBlock pairs.toList := by
        match h_list : pairs.toList with
        | [] => exact emitPairList_scans_block_empty
        | _ :: _ =>
          exact emitPairList_scans_block_nonempty _ (by simp) (fun p hp => by
            have hp' : p ∈ pairs.toList := h_list ▸ hp
            have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
            have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
            exact h_eq ▸ emit_scans_in_flow_saved_key_block _ (hk ⟨i, h_sz⟩)) (fun p hp => by
            have hp' : p ∈ pairs.toList := h_list ▸ hp
            have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
            have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
            exact h_eq ▸ emit_scans_in_flow_block _ (hv ⟨i, h_sz⟩))
      have h_corr₁_assoc : ScannerSurfCorr s₁
          ⟨(emit.emitPairList pairs.toList).toList ++ (['}'] ++ rest), s₁.col⟩ := by
        rw [List.append_assoc] at h_corr₁; exact h_corr₁
      obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂, h_body_append, h_body_wb, h_body_wt⟩ :=
        h_pair_scan s₁ (['}'] ++ rest) h_corr₁_assoc h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁ h_s1_ska h_s1_sync
      have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
      have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
        unfold StackEndLineOnLine at h_stack_endline₁ ⊢
        rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
      obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃, _h_line₃, h_atol₃, h_endline₃, h_stack₃, _, _⟩ :=
        scanNextToken_flow_close_mapping_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
          h_atol₂ h_stack_endline₂
      have h_corr₂_cons : ScannerSurfCorr s₂ ⟨'}' :: rest, s₂.col⟩ := by
        have : ['}'] ++ rest = '}' :: rest := by simp
        rwa [this] at h_corr₂
      obtain ⟨fmeTok, h_fme_val, h_close_push⟩ :=
        scanNextToken_flow_close_map_filtered_push s₂ rest h_corr₂_cons h_s2_inflow h_s2_indent h_col₂
          h_fl₂_ge2 h_snt₃
      have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ := h_fmc₂.weaken (by omega)
      have h_fmc_all :=
        (FlowMonoChain.single h_snt₁ (Nat.le.refl) (by omega)).trans
          (h_fmc₂'.trans (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
      have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s_state s₁ '{'
          ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt₁
      have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₂.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s₂ s₃ '}' rest
          h_corr₂_cons h_s2_inflow h_s2_indent h_col₂ (by decide) (by decide) (by decide) h_snt₃
      have h_block_eq : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ (fmsTok :: (bodyBlock ++ [fmeTok])) := by
        have h1 : (s₁.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fmsTok] := by
          rw [h_open_push, Array.toList_push]
        have h3 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fmeTok] := by
          rw [h_close_push, Array.toList_push]
        rw [h3, h_body_append, h1]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have h_wrap := wrap_map_block fmsTok fmeTok bodyBlock h_fms_val h_fme_val h_body_wb
      have h_wrap_t := wrap_map_typed fmsTok fmeTok bodyBlock h_fms_val h_fme_val h_body_wt
      refine ⟨(1 + n₂) + 1, s₃, fmsTok :: (bodyBlock ++ [fmeTok]),
        (ScanChainGrew.single h_snt₁ h_grew₁).trans (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
        h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_ska₃, h_tok₃, ?_, ?_, ?_, h_fmc_all,
        h_block_eq, h_wrap.1, h_wrap_t, h_wrap.2,
        EntryUnit_wrap fmsTok fmeTok bodyBlock (h_fms_val ▸ flowBracketDelta_flowMappingStart)
          (h_fme_val ▸ flowBracketDelta_flowMappingEnd) h_body_wb, RecSeqEntry.map fmsTok fmeTok bodyBlock h_fms_val h_fme_val h_body_wb, ?_⟩
      · rw [h_fl₃, h_fl₂, h_fl₁]; omega
      · rw [h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek₃, h_ek₂, h_ek₁]
      · rw [h_col₃]; omega
      · unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
      · unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
      · rw [_h_line₃, _h_line₂, _h_line₁]
      · exact h_atol₃
      · exact h_endline₃
      · rw [h_stack₃, h_stack₂, h_stack_pop₁]
      · exact ⟨List.cons_ne_nil _ _, Or.inr (Or.inr (by rw [List.head_cons]; exact h_fms_val))⟩

/-! ### Emit-producer strengthening — key-side `RecSeqEntry` deliverable (Phase J feed)

The per-key producer `emit_scans_in_flow_saved_key_rec_entry : Grammable v inFlow →
EmitScansInFlowSavedKeyRecEntry v` closes the **key half** of the emit feed: it strengthens the flat
saved-key block producer `emit_scans_in_flow_saved_key_block` to additionally deliver `RecSeqEntry block`,
the per-pair *key* recursive deliverable `emitPairList_scans_recmapbody` reads as a bare hypothesis.

It is the **saved-key twin** of `emit_scans_in_flow_rec_entry` (the value half) and **depends on it**
(R251 — the storage graph orders the family): a `sequence` value scanned as a saved key has *value* body
items, so its body scan is fed by the black-box value producer `emit_scans_in_flow_rec_entry`, not by this
induction's own IH (which would carry the wrong, saved-key, deliverable).  Concretely the three cases:

  * `scalar` → `RecSeqEntry.scalar` (the single token is the entry — a leaf);
  * `sequence` → `RecSeqEntry.seqEmpty`/`RecSeqEntry.seq`, body block scanned by
    `emitList_scans_recseqbody` fed per item by `emit_scans_in_flow_rec_entry` (the value producer);
  * `mapping` → `RecSeqEntry.map`, which **stores only `WellBracketed interior`** (R244 — projections track
    stored fields), so the body needs no recursive map-body delivery: the flat pair scan (black-box flat
    wrappers `emit_scans_in_flow_saved_key_block`/`emit_scans_in_flow_block`) suffices, and the case is a leaf.

The proof is a verbatim mirror of `emit_scans_block_combined`'s three `savedkey` cases; only the per-entry
`RecSeqEntry` leaf is woven in (and the seq body scan swapped for its recursive twin, fed by the value
producer rather than `(ih i).1`).  Verified-but-unconsumed: references no sorry site, frontier sorry count
unchanged.  With both halves landed, the emit feed of both body assemblers is closed. -/
set_option maxHeartbeats 1600000 in
theorem emit_scans_in_flow_saved_key_rec_entry (v : YamlValue) {inFlow : Bool}
    (hg : Grammable v inFlow) : EmitScansInFlowSavedKeyRecEntry v := by
  induction hg with
  | scalar sc _ h =>
    intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska _h_sync
    have h_chars : (emit (.scalar sc)).toList ++ rest =
        ['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest := by
      simp only [emit, emitScalar, String.toList_append]; rfl
    have hcorr' : ScannerSurfCorr s_state
        ⟨['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest, s_state.col⟩ := by
      rwa [← h_chars]
    have hcorr_q : ScannerSurfCorr s_state
        ⟨'"' :: ((escapeString sc.content).toList ++ ['"'] ++ rest), s_state.col⟩ := by
      have : ['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest =
          '"' :: ((escapeString sc.content).toList ++ ['"'] ++ rest) := by
        simp only [List.cons_append, List.nil_append, List.append_assoc]
      rwa [this] at hcorr'
    obtain ⟨s', h_snt, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', _h_tok', h_ska', _h_line', h_atol', h_endline', h_stack'⟩ :=
      scanNextToken_flow_scanDoubleQuoted s_state sc.content rest hcorr' h_flow h_indent h_col
        h_atol h_endline
    obtain ⟨s'', h_snt'', h_poss'', h_tidx'', h_size'', h_ph'', h_ph1''⟩ :=
      scanNextToken_flow_scalar_savedKey s_state sc.content rest hcorr' h_flow h_indent h_col h_ek h_ska
    have h_eq : s'' = s' := Option.some.inj (Except.ok.inj (h_snt''.symm.trans h_snt))
    subst h_eq
    have h_grew : (s''.tokens.filter (fun t => t.val != .placeholder)).size >
                  (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
      scanNextToken_filtered_grows_in_flow s_state s'' '"'
        ((escapeString sc.content).toList ++ ['"'] ++ rest) hcorr_q
        h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt''
    obtain ⟨tok, str, st, h_tok_val, h_push⟩ :=
      scanNextToken_flow_scalar_filtered_push s_state ((escapeString sc.content).toList ++ ['"'] ++ rest)
        hcorr_q h_flow h_indent h_col h_snt''
    have h_N1 : s_state.tokens.size < s''.tokens.size := by omega
    have h_nc : ∀ t c', scanNextToken_preprocess s_state = .ok (some (t, c')) → c' ≠ ':' :=
      no_colon_of_preprocess_flow s_state '"' ((escapeString sc.content).toList ++ ['"'] ++ rest)
        s_state.col hcorr_q h_flow (by decide) (by decide) (by decide) (by decide)
    have h_pref : ∀ j, j < s_state.tokens.size → s''.tokens[j]? = s_state.tokens[j]? := by
      intro j hj
      have h_pt := scanNextToken_at_non_colon_preserves_positions s_state s'' h_snt'' h_nc j hj
      rw [Array.getElem?_eq_getElem (by
            have := ScannerCorrectness.scanNextToken_adds_tokens s_state s'' h_snt''; omega),
          Array.getElem?_eq_getElem hj, h_pt]
    have h_ph_false :
        (fun (t : Positioned YamlToken) => t.val != .placeholder) (s''.tokens[s_state.tokens.size]'h_N1) = false := by
      have h := h_ph'' h_N1; simp [h]
    have h_take :
        (s''.tokens.toList.take (s_state.tokens.size + 1)).filter (fun t => t.val != .placeholder)
          = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList :=
      block_take_eq_of_getElem? s''.tokens s_state.tokens s_state.tokens.size
        (fun t => t.val != .placeholder) rfl h_N1 h_pref h_ph_false
    have h_wb_es : WellBracketed [tok] ∧ WellTyped [tok] ∧ EntrySafe [tok] :=
      ⟨WellBracketed_singleton_delta_zero tok (by rw [h_tok_val]; exact flowBracketDelta_scalar str st),
        WellTyped_singleton_delta_zero tok (by rw [h_tok_val]; exact flowBracketDelta_scalar str st),
        EntrySafe_scalar tok str st h_tok_val⟩
    refine ⟨1, s'', [tok], ScanChainGrew.single h_snt'' h_grew, h_corr', h_fl', h_dp', h_ids', h_ek',
      h_col', ?_, ?_, _h_line', h_atol', h_endline', h_stack',
      FlowMonoChain.single h_snt'' (Nat.le.refl) (by omega),
      h_ska', h_poss'', h_tidx'', h_size'', h_ph'', h_ph1'', ?_, h_take,
      h_wb_es.1, h_wb_es.2.1, h_wb_es.2.2, RecSeqEntry.scalar tok str st h_tok_val⟩
    · unfold ScannerState.inFlow; rw [h_fl']
      unfold ScannerState.inFlow at h_flow; exact h_flow
    · unfold ScannerState.currentIndent; rw [h_ids']; exact h_indent
    · rw [h_push, Array.toList_push]
  | sequence style items tag anchor _ h _ih =>
    intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
    have h_chars : (emit (.sequence style items tag anchor)).toList ++ rest =
        ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest := by
      simp only [emit, String.toList_append]; rfl
    have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
    have h_corr_state_cons : ScannerSurfCorr s_state
        ⟨'[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest), s_state.col⟩ := by
      have : ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest =
          '[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest) := by
        simp only [List.cons_append, List.nil_append, List.append_assoc]
      rwa [this] at hcorr₀
    obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁, h_endline₁, h_stack_endline₁, h_stack_pop₁, h_sk_poss₁, _h_toks_gt₁, h_stack_push₁⟩ :=
      scanNextToken_flow_open_nested s_state
        ((emit.emitList items.toList).toList ++ [']'] ++ rest) hcorr₀ h_flow h_indent h_col
        h_atol h_endline
    obtain ⟨h_s1_size, h_s1_rawN, h_s1_rawN1⟩ :=
      scanNextToken_flow_open_seq_savedKey s_state s₁ ((emit.emitList items.toList).toList ++ [']'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col h_ek h_ska h_snt₁
    have h_fl₁_ge2 : s₁.flowLevel ≥ 2 := by rw [h_fl₁]; omega
    have h_s1_inflow : s₁.inFlow = true := by
      unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
    have h_s1_indent : s₁.currentIndent < 0 := by
      unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
    have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
    have h_stack_size₁ : s₁.simpleKeyStack.size = s₁.flowLevel := by
      rw [h_stack_push₁, Array.size_push, h_sync, h_fl₁]
    obtain ⟨fssTok, h_fss_val, h_open_push⟩ :=
      scanNextToken_flow_open_seq_filtered_push s_state
        ((emit.emitList items.toList).toList ++ [']'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col h_snt₁
    have h_corr₁_assoc : ScannerSurfCorr s₁
        ⟨(emit.emitList items.toList).toList ++ ([']'] ++ rest), s₁.col⟩ := by
      rw [List.append_assoc] at h_corr₁; exact h_corr₁
    obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
            h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
            h_body_append, h_body_wb, h_body_wt, h_entry_builder⟩ :
        (∃ n₂ s₂ bodyBlock,
          ScanChainGrew (fun t => t.val != .placeholder) s₁ n₂ s₂
          ∧ ScannerSurfCorr s₂ ⟨[']'] ++ rest, s₂.col⟩
          ∧ s₂.flowLevel = s₁.flowLevel
          ∧ s₂.directivesPresent = s₁.directivesPresent
          ∧ s₂.indents = s₁.indents
          ∧ s₂.explicitKeyLine = s₁.explicitKeyLine
          ∧ s₂.col > 0
          ∧ s₂.inFlow = true
          ∧ s₂.currentIndent < 0
          ∧ s₂.line = s₁.line
          ∧ AllTokensOnLine s₂ s₂.line
          ∧ EndLineOnLine s₂
          ∧ s₂.simpleKeyStack = s₁.simpleKeyStack
          ∧ FlowMonoChain s₁.flowLevel s₁ n₂ s₂
          ∧ (s₂.tokens.filter (fun t => t.val != .placeholder)).toList
              = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList ++ bodyBlock
          ∧ WellBracketed bodyBlock
          ∧ WellTyped bodyBlock
          ∧ (∀ (fss fse : Positioned YamlToken),
              fss.val = .flowSequenceStart → fse.val = .flowSequenceEnd →
                RecSeqEntry (fss :: (bodyBlock ++ [fse])))) := by
      match h_list : items.toList with
      | [] =>
        refine ⟨0, s₁, [], .zero, ?_, rfl, rfl, rfl, rfl, h_s1_col, h_s1_inflow, h_s1_indent, rfl,
                h_atol₁, h_endline₁, rfl, .zero (Nat.le.refl), ?_, WellBracketed_nil, WellTyped_nil,
                fun fss fse hf1 hf2 => RecSeqEntry.seqEmpty fss fse hf1 hf2⟩
        · have h_e : (emit.emitList items.toList).toList ++ ([']'] ++ rest) = [']'] ++ rest := by
            rw [h_list]; simp only [emit.emitList]; rfl
          rw [h_e] at h_corr₁_assoc; exact h_corr₁_assoc
        · simp
      | w :: ws =>
        have h_all_rec : ∀ u ∈ (w :: ws), EmitScansInFlowRecEntry u := fun u hu => by
          have hu' : u ∈ items.toList := h_list ▸ hu
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hu'
          have h_sz : i < items.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ emit_scans_in_flow_rec_entry _ (h ⟨i, h_sz⟩)
        obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
                h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
                h_body_append, h_body_wb, h_body_wt, h_body_rec⟩ :=
          emitList_scans_recseqbody (w :: ws) (by simp) h_all_rec s₁ ([']'] ++ rest)
            (h_list ▸ h_corr₁_assoc) h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
            (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁ h_stack_size₁
        exact ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
               h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
               h_body_append, h_body_wb, h_body_wt,
               fun fss fse hf1 hf2 => RecSeqEntry.seq fss fse bodyBlock hf1 hf2 h_body_wb h_body_rec⟩
    have h_skaf_N : SimpleKeyAboveFloor s₁ s_state.tokens.size s₁.flowLevel := by
      refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
        fun j hj hjb _ => by exfalso; omega, by omega⟩
    have h_skaf₁ : SimpleKeyAboveFloor s₁ (s_state.tokens.size + 1) s₁.flowLevel := by
      refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
        fun j hj hjb _ => by exfalso; omega, by omega⟩
    have h_body_rawN : s₂.tokens[s_state.tokens.size]? = s₁.tokens[s_state.tokens.size]? := by
      have h_eq := FlowMonoChain_preserves_raw_prefix h_fmc₂ (s_state.tokens.size + 1)
        (by omega) h_skaf₁ (by omega) s_state.tokens.size (by omega)
      rw [Array.getElem?_eq_getElem (by have := h_fmc₂.tokens_mono; omega),
          Array.getElem?_eq_getElem (by omega), h_eq]
    have h_skaf₁' : SimpleKeyAboveFloor s₁ (s_state.tokens.size + 2) s₁.flowLevel := by
      refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
        fun j hj hjb _ => by exfalso; omega, by omega⟩
    have h_body_rawN1 : s₂.tokens[s_state.tokens.size + 1]? = s₁.tokens[s_state.tokens.size + 1]? := by
      have h_eq := FlowMonoChain_preserves_raw_prefix h_fmc₂ (s_state.tokens.size + 2)
        (by omega) h_skaf₁' (by omega) (s_state.tokens.size + 1) (by omega)
      rw [Array.getElem?_eq_getElem (by have := h_fmc₂.tokens_mono; omega),
          Array.getElem?_eq_getElem (by omega), h_eq]
    have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
    have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
      unfold StackEndLineOnLine at h_stack_endline₁ ⊢
      rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
    obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃, _h_line₃, h_atol₃, h_endline₃, h_stack₃, h_skrestore₃, h_prefix₃⟩ :=
      scanNextToken_flow_close_seq_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
        h_atol₂ h_stack_endline₂
    have h_corr₂_cons : ScannerSurfCorr s₂ ⟨']' :: rest, s₂.col⟩ := by
      have : [']'] ++ rest = ']' :: rest := by simp
      rwa [this] at h_corr₂
    obtain ⟨fseTok, h_fse_val, h_close_push⟩ :=
      scanNextToken_flow_close_seq_filtered_push s₂ rest h_corr₂_cons h_s2_inflow h_s2_indent h_col₂
        h_fl₂_ge2 h_snt₃
    have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ := h_fmc₂.weaken (by omega)
    have h_fmc_all :=
      (FlowMonoChain.single h_snt₁ (Nat.le.refl) (by omega)).trans
        (h_fmc₂'.trans (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
    have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
      scanNextToken_filtered_grows_in_flow s_state s₁ '['
        ((emit.emitList items.toList).toList ++ [']'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt₁
    have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s₂.tokens.filter (fun t => t.val != .placeholder)).size :=
      scanNextToken_filtered_grows_in_flow s₂ s₃ ']' rest
        h_corr₂_cons h_s2_inflow h_s2_indent h_col₂ (by decide) (by decide) (by decide) h_snt₃
    have h_skey_eq : s₃.simpleKey = (saveSimpleKey s_state).simpleKey := by
      rw [h_skrestore₃, h_stack₂, h_stack_push₁]; simp [Array.back?_push]
    obtain ⟨_h_skp, _h_skt, _, _⟩ := saveSimpleKey_eval s_state h_ek h_ska
    have h_close_mono : s₂.tokens.size ≤ s₃.tokens.size := by
      have := ScannerCorrectness.scanNextToken_adds_tokens s₂ s₃ h_snt₃; omega
    have h_body_mono : s₁.tokens.size ≤ s₂.tokens.size := h_fmc₂.tokens_mono
    have h_s3_rawN? : s₃.tokens[s_state.tokens.size]? = some ⟨s_state.currentPos, .placeholder, s_state.currentPos⟩ := by
      rw [h_prefix₃ s_state.tokens.size (by omega), h_body_rawN, h_s1_rawN]
    have h_s3_rawN1? : s₃.tokens[s_state.tokens.size + 1]? = some ⟨s_state.currentPos, .placeholder, s_state.currentPos⟩ := by
      rw [h_prefix₃ (s_state.tokens.size + 1) (by omega), h_body_rawN1, h_s1_rawN1]
    have h_block_eq : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
        = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList
          ++ (fssTok :: (bodyBlock ++ [fseTok])) := by
      have h1 : (s₁.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fssTok] := by
        rw [h_open_push, Array.toList_push]
      have h3 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fseTok] := by
        rw [h_close_push, Array.toList_push]
      rw [h3, h_body_append, h1]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have h_N1 : s_state.tokens.size < s₃.tokens.size := by omega
    have h_pref : ∀ j, j < s_state.tokens.size → s₃.tokens[j]? = s_state.tokens[j]? := by
      intro j hj
      have hj2 : j < s₂.tokens.size := by omega
      have h_nc_open : ∀ t c', scanNextToken_preprocess s_state = .ok (some (t, c')) → c' ≠ ':' :=
        no_colon_of_preprocess_flow s_state '[' ((emit.emitList items.toList).toList ++ [']'] ++ rest)
          s_state.col h_corr_state_cons h_flow (by decide) (by decide) (by decide) (by decide)
      have ho := scanNextToken_at_non_colon_preserves_positions s_state s₁ h_snt₁ h_nc_open j hj
      have hb := FlowMonoChain_preserves_raw_prefix h_fmc₂ s_state.tokens.size (by omega)
        h_skaf_N (by omega) j hj
      have hc := h_prefix₃ j hj2
      rw [hc, Array.getElem?_eq_getElem hj2, hb, ho, Array.getElem?_eq_getElem hj]
    have h_ph_false :
        (fun (t : Positioned YamlToken) => t.val != .placeholder) (s₃.tokens[s_state.tokens.size]'h_N1) = false := by
      have h_some : s₃.tokens[s_state.tokens.size]? = some (s₃.tokens[s_state.tokens.size]'h_N1) :=
        Array.getElem?_eq_getElem h_N1
      have heq := Option.some.inj (h_some.symm.trans h_s3_rawN?)
      rw [heq]; rfl
    have h_take :
        (s₃.tokens.toList.take (s_state.tokens.size + 1)).filter (fun t => t.val != .placeholder)
          = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList :=
      block_take_eq_of_getElem? s₃.tokens s_state.tokens s_state.tokens.size
        (fun t => t.val != .placeholder) rfl h_N1 h_pref h_ph_false
    have h_wrap := wrap_seq_block fssTok fseTok bodyBlock h_fss_val h_fse_val h_body_wb
    have h_wrap_t := wrap_seq_typed fssTok fseTok bodyBlock h_fss_val h_fse_val h_body_wt
    refine ⟨(1 + n₂) + 1, s₃, fssTok :: (bodyBlock ++ [fseTok]),
      (ScanChainGrew.single h_snt₁ h_grew₁).trans (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
      h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_atol₃, h_endline₃, ?_, h_fmc_all,
      h_ska₃, ?_, ?_, ?_, ?_, ?_, h_block_eq, h_take, h_wrap.1, h_wrap_t, h_wrap.2,
      h_entry_builder fssTok fseTok h_fss_val h_fse_val⟩
    · rw [h_fl₃, h_fl₂, h_fl₁]; omega
    · rw [h_dp₃, h_dp₂, h_dp₁]
    · rw [h_ids₃, h_ids₂, h_ids₁]
    · rw [h_ek₃, h_ek₂, h_ek₁]
    · rw [h_col₃]; omega
    · unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
    · unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
    · rw [_h_line₃, _h_line₂, _h_line₁]
    · rw [h_stack₃, h_stack₂, h_stack_pop₁]
    · rw [h_skey_eq]; exact _h_skp
    · rw [h_skey_eq]; exact _h_skt
    · omega
    · intro hh
      have h_some : s₃.tokens[s_state.tokens.size]? = some (s₃.tokens[s_state.tokens.size]'hh) :=
        Array.getElem?_eq_getElem hh
      have := Option.some.inj (h_some.symm.trans h_s3_rawN?); rw [this]
    · intro hh
      have h_some : s₃.tokens[s_state.tokens.size + 1]? = some (s₃.tokens[s_state.tokens.size + 1]'hh) :=
        Array.getElem?_eq_getElem hh
      have := Option.some.inj (h_some.symm.trans h_s3_rawN1?); rw [this]
  | mapping style pairs tag anchor _ hk hv _ihk _ihv =>
    intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
    have h_chars : (emit (.mapping style pairs tag anchor)).toList ++ rest =
        ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest := by
      simp only [emit, String.toList_append]; rfl
    have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
    have h_corr_state_cons : ScannerSurfCorr s_state
        ⟨'{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest), s_state.col⟩ := by
      have : ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest =
          '{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) := by
        simp only [List.cons_append, List.nil_append, List.append_assoc]
      rwa [this] at hcorr₀
    obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁, h_endline₁, h_stack_endline₁, h_stack_pop₁, h_sk_poss₁, _h_toks_gt₁, h_stack_push₁⟩ :=
      scanNextToken_flow_open_mapping_nested s_state
        ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) hcorr₀ h_flow h_indent h_col
        h_atol h_endline
    obtain ⟨h_s1_size, h_s1_rawN, h_s1_rawN1⟩ :=
      scanNextToken_flow_open_mapping_savedKey s_state s₁ ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col h_ek h_ska h_snt₁
    have h_fl₁_ge2 : s₁.flowLevel ≥ 2 := by rw [h_fl₁]; omega
    have h_s1_inflow : s₁.inFlow = true := by
      unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
    have h_s1_indent : s₁.currentIndent < 0 := by
      unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
    have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
    have h_stack_size₁ : s₁.simpleKeyStack.size = s₁.flowLevel := by
      rw [h_stack_push₁, Array.size_push, h_sync, h_fl₁]
    have h_s1_ska : s₁.simpleKeyAllowed = true :=
      scanNextToken_flow_open_mapping_ska s_state s₁
        ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col h_snt₁
    obtain ⟨fmsTok, h_fms_val, h_open_push⟩ :=
      scanNextToken_flow_open_map_filtered_push s_state
        ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col h_snt₁
    have h_pair_scan : EmitPairListScansInFlowBlock pairs.toList := by
      match h_list : pairs.toList with
      | [] => exact emitPairList_scans_block_empty
      | _ :: _ =>
        exact emitPairList_scans_block_nonempty _ (by simp) (fun p hp => by
          have hp' : p ∈ pairs.toList := h_list ▸ hp
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
          have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ emit_scans_in_flow_saved_key_block _ (hk ⟨i, h_sz⟩)) (fun p hp => by
          have hp' : p ∈ pairs.toList := h_list ▸ hp
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
          have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ emit_scans_in_flow_block _ (hv ⟨i, h_sz⟩))
    have h_corr₁_assoc : ScannerSurfCorr s₁
        ⟨(emit.emitPairList pairs.toList).toList ++ (['}'] ++ rest), s₁.col⟩ := by
      rw [List.append_assoc] at h_corr₁; exact h_corr₁
    obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂, h_body_append, h_body_wb, h_body_wt⟩ :=
      h_pair_scan s₁ (['}'] ++ rest) h_corr₁_assoc h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
        (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁ h_s1_ska h_stack_size₁
    have h_skaf_N : SimpleKeyAboveFloor s₁ s_state.tokens.size s₁.flowLevel := by
      refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
        fun j hj hjb _ => by exfalso; omega, by omega⟩
    have h_skaf₁ : SimpleKeyAboveFloor s₁ (s_state.tokens.size + 1) s₁.flowLevel := by
      refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
        fun j hj hjb _ => by exfalso; omega, by omega⟩
    have h_body_rawN : s₂.tokens[s_state.tokens.size]? = s₁.tokens[s_state.tokens.size]? := by
      have h_eq := FlowMonoChain_preserves_raw_prefix h_fmc₂ (s_state.tokens.size + 1)
        (by omega) h_skaf₁ (by omega) s_state.tokens.size (by omega)
      rw [Array.getElem?_eq_getElem (by have := h_fmc₂.tokens_mono; omega),
          Array.getElem?_eq_getElem (by omega), h_eq]
    have h_skaf₁' : SimpleKeyAboveFloor s₁ (s_state.tokens.size + 2) s₁.flowLevel := by
      refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
        fun j hj hjb _ => by exfalso; omega, by omega⟩
    have h_body_rawN1 : s₂.tokens[s_state.tokens.size + 1]? = s₁.tokens[s_state.tokens.size + 1]? := by
      have h_eq := FlowMonoChain_preserves_raw_prefix h_fmc₂ (s_state.tokens.size + 2)
        (by omega) h_skaf₁' (by omega) (s_state.tokens.size + 1) (by omega)
      rw [Array.getElem?_eq_getElem (by have := h_fmc₂.tokens_mono; omega),
          Array.getElem?_eq_getElem (by omega), h_eq]
    have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
    have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
      unfold StackEndLineOnLine at h_stack_endline₁ ⊢
      rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
    obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃, _h_line₃, h_atol₃, h_endline₃, h_stack₃, h_skrestore₃, h_prefix₃⟩ :=
      scanNextToken_flow_close_mapping_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
        h_atol₂ h_stack_endline₂
    have h_corr₂_cons : ScannerSurfCorr s₂ ⟨'}' :: rest, s₂.col⟩ := by
      have : ['}'] ++ rest = '}' :: rest := by simp
      rwa [this] at h_corr₂
    obtain ⟨fmeTok, h_fme_val, h_close_push⟩ :=
      scanNextToken_flow_close_map_filtered_push s₂ rest h_corr₂_cons h_s2_inflow h_s2_indent h_col₂
        h_fl₂_ge2 h_snt₃
    have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ := h_fmc₂.weaken (by omega)
    have h_fmc_all :=
      (FlowMonoChain.single h_snt₁ (Nat.le.refl) (by omega)).trans
        (h_fmc₂'.trans (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
    have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
      scanNextToken_filtered_grows_in_flow s_state s₁ '{'
        ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt₁
    have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s₂.tokens.filter (fun t => t.val != .placeholder)).size :=
      scanNextToken_filtered_grows_in_flow s₂ s₃ '}' rest
        h_corr₂_cons h_s2_inflow h_s2_indent h_col₂ (by decide) (by decide) (by decide) h_snt₃
    have h_skey_eq : s₃.simpleKey = (saveSimpleKey s_state).simpleKey := by
      rw [h_skrestore₃, h_stack₂, h_stack_push₁]; simp [Array.back?_push]
    obtain ⟨_h_skp, _h_skt, _, _⟩ := saveSimpleKey_eval s_state h_ek h_ska
    have h_close_mono : s₂.tokens.size ≤ s₃.tokens.size := by
      have := ScannerCorrectness.scanNextToken_adds_tokens s₂ s₃ h_snt₃; omega
    have h_body_mono : s₁.tokens.size ≤ s₂.tokens.size := h_fmc₂.tokens_mono
    have h_s3_rawN? : s₃.tokens[s_state.tokens.size]? = some ⟨s_state.currentPos, .placeholder, s_state.currentPos⟩ := by
      rw [h_prefix₃ s_state.tokens.size (by omega), h_body_rawN, h_s1_rawN]
    have h_s3_rawN1? : s₃.tokens[s_state.tokens.size + 1]? = some ⟨s_state.currentPos, .placeholder, s_state.currentPos⟩ := by
      rw [h_prefix₃ (s_state.tokens.size + 1) (by omega), h_body_rawN1, h_s1_rawN1]
    have h_block_eq : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
        = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList
          ++ (fmsTok :: (bodyBlock ++ [fmeTok])) := by
      have h1 : (s₁.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fmsTok] := by
        rw [h_open_push, Array.toList_push]
      have h3 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fmeTok] := by
        rw [h_close_push, Array.toList_push]
      rw [h3, h_body_append, h1]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have h_N1 : s_state.tokens.size < s₃.tokens.size := by omega
    have h_pref : ∀ j, j < s_state.tokens.size → s₃.tokens[j]? = s_state.tokens[j]? := by
      intro j hj
      have hj2 : j < s₂.tokens.size := by omega
      have h_nc_open : ∀ t c', scanNextToken_preprocess s_state = .ok (some (t, c')) → c' ≠ ':' :=
        no_colon_of_preprocess_flow s_state '{' ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
          s_state.col h_corr_state_cons h_flow (by decide) (by decide) (by decide) (by decide)
      have ho := scanNextToken_at_non_colon_preserves_positions s_state s₁ h_snt₁ h_nc_open j hj
      have hb := FlowMonoChain_preserves_raw_prefix h_fmc₂ s_state.tokens.size (by omega)
        h_skaf_N (by omega) j hj
      have hc := h_prefix₃ j hj2
      rw [hc, Array.getElem?_eq_getElem hj2, hb, ho, Array.getElem?_eq_getElem hj]
    have h_ph_false :
        (fun (t : Positioned YamlToken) => t.val != .placeholder) (s₃.tokens[s_state.tokens.size]'h_N1) = false := by
      have h_some : s₃.tokens[s_state.tokens.size]? = some (s₃.tokens[s_state.tokens.size]'h_N1) :=
        Array.getElem?_eq_getElem h_N1
      have heq := Option.some.inj (h_some.symm.trans h_s3_rawN?)
      rw [heq]; rfl
    have h_take :
        (s₃.tokens.toList.take (s_state.tokens.size + 1)).filter (fun t => t.val != .placeholder)
          = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList :=
      block_take_eq_of_getElem? s₃.tokens s_state.tokens s_state.tokens.size
        (fun t => t.val != .placeholder) rfl h_N1 h_pref h_ph_false
    have h_wrap := wrap_map_block fmsTok fmeTok bodyBlock h_fms_val h_fme_val h_body_wb
    have h_wrap_t := wrap_map_typed fmsTok fmeTok bodyBlock h_fms_val h_fme_val h_body_wt
    refine ⟨(1 + n₂) + 1, s₃, fmsTok :: (bodyBlock ++ [fmeTok]),
      (ScanChainGrew.single h_snt₁ h_grew₁).trans (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
      h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_atol₃, h_endline₃, ?_, h_fmc_all,
      h_ska₃, ?_, ?_, ?_, ?_, ?_, h_block_eq, h_take, h_wrap.1, h_wrap_t, h_wrap.2,
      RecSeqEntry.map fmsTok fmeTok bodyBlock h_fms_val h_fme_val h_body_wb⟩
    · rw [h_fl₃, h_fl₂, h_fl₁]; omega
    · rw [h_dp₃, h_dp₂, h_dp₁]
    · rw [h_ids₃, h_ids₂, h_ids₁]
    · rw [h_ek₃, h_ek₂, h_ek₁]
    · rw [h_col₃]; omega
    · unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
    · unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
    · rw [_h_line₃, _h_line₂, _h_line₁]
    · rw [h_stack₃, h_stack₂, h_stack_pop₁]
    · rw [h_skey_eq]; exact _h_skp
    · rw [h_skey_eq]; exact _h_skt
    · omega
    · intro hh
      have h_some : s₃.tokens[s_state.tokens.size]? = some (s₃.tokens[s_state.tokens.size]'hh) :=
        Array.getElem?_eq_getElem hh
      have := Option.some.inj (h_some.symm.trans h_s3_rawN?); rw [this]
    · intro hh
      have h_some : s₃.tokens[s_state.tokens.size + 1]? = some (s₃.tokens[s_state.tokens.size + 1]'hh) :=
        Array.getElem?_eq_getElem hh
      have := Option.some.inj (h_some.symm.trans h_s3_rawN1?); rw [this]

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

/-- **Recursive map bracket-entry** (Phase J, map side — the descent-locator's raw output type).
    A `{ … }` flow-MAPPING bracket entry whose interior carries the *recursive* `RecMapBody`
    structure, not merely its `WellBracketed` substrate.  This is the map-side refinement
    `RecSeqEntry.map` deliberately deferred (its interior bottoms out at `WellBracketed`, with the
    fully-recursive map interior flagged "a later refinement"): a dedicated entry type depending only
    on the already-defined `RecMapBody`, so no `mutual` with `RecSeqEntry` is needed.  `mapEmpty` is
    the `{}` witness (`interior = []`, which `RecMapBody` — having no `nil` constructor — cannot
    represent); `map` carries the non-empty `RecMapBody interior`.  Unlike `RecSeqEntry`, every
    constructor is a mapping, so the entry *internalizes* the `.flowMappingStart` opener guard the
    seq entry needed supplied externally — the map front-end joint therefore needs no separate
    `h_open`. -/
inductive RecMapEntry : List (Positioned YamlToken) → Prop where
  | mapEmpty (op cl : Positioned YamlToken)
      (h_op : op.val = .flowMappingStart) (h_cl : cl.val = .flowMappingEnd) :
      RecMapEntry (op :: ([] ++ [cl]))
  | map (op cl : Positioned YamlToken) (interior : List (Positioned YamlToken))
      (h_op : op.val = .flowMappingStart) (h_cl : cl.val = .flowMappingEnd)
      (h_rec : RecMapBody interior) :
      RecMapEntry (op :: (interior ++ [cl]))

/-- **Single-level map descent** (Phase J, map side — the recursive analog of
    `RecSeqEntry.seq_interior`).  A located `RecMapEntry (op :: (interior ++ [cl]))` has an interior
    that is EITHER a `RecMapBody` (the `lo < hi` shape the back-half joint
    `mapBodyProps_of_recmapbody_window` consumes after `RecMapBody.toSafeBody`) OR empty
    (`interior = []`, the `lo = hi` shape `mapBodyProps_empty` discharges vacuously).  This is the
    producer-contract split (Reflection 233 — the empty branch the `SafeBody (· = .key)`-keyed joint
    structurally cannot cover is the branch it is never asked to cover); no opener guard is needed
    because both `RecMapEntry` constructors are mappings. -/
theorem RecMapEntry.map_interior {e interior : List (Positioned YamlToken)}
    {op cl : Positioned YamlToken}
    (h : RecMapEntry e) (h_eq : e = op :: (interior ++ [cl])) :
    RecMapBody interior ∨ interior = [] := by
  cases h with
  | mapEmpty op' cl' h_op' h_cl' =>
      right
      injection h_eq with _h1 h2
      simp only [List.nil_append] at h2
      exact (append_singleton_inj h2.symm).1
  | map op' cl' interior' h_op' h_cl' h_rec =>
      left
      injection h_eq with _h1 h2
      exact (append_singleton_inj h2).1 ▸ h_rec

/-- **Balance projection (map side, recursive bracket-entry level).**  A `RecMapEntry` is in
    particular `WellBracketed` — its bracket balance returns to `0` at the end and stays `≥ 0`
    throughout.  This completes the `RecMapEntry` projection family (R242 added the type and its
    single-level descent `RecMapEntry.map_interior`, but not its balance projection), the entry-level
    map mirror of `RecSeqEntry.toWellBracketed` (R238): both `RecMapEntry` constructors are `{ … }`
    frames, so `wrap_map_block` wraps the interior's `WellBracketed` — `WellBracketed_nil` for the
    `mapEmpty` `{}` leaf, `RecMapBody.toWellBracketed h_rec` (R240) for the non-empty `map` interior —
    reading its `.1` (the `WellBracketed` half) exactly as the `RecSeqEntry.map` case does.  This is
    the navigation invariant the map *locate* needs at the entry level: matching a guarded balanced
    flow-mapping subrange to a `RecMapEntry` is a balance argument (the matching close of a depth-0
    `{` opener is the entry's last token), and only the deliverable's structure can supply that
    per-entry — never a single global hypothesis. -/
theorem RecMapEntry.toWellBracketed {e : List (Positioned YamlToken)}
    (h : RecMapEntry e) : WellBracketed e := by
  cases h with
  | mapEmpty op cl h_op h_cl => exact (wrap_map_block op cl [] h_op h_cl WellBracketed_nil).1
  | map op cl interior h_op h_cl h_rec =>
      exact (wrap_map_block op cl interior h_op h_cl h_rec.toWellBracketed).1

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

/-- **Located-entry → `SeqBodyProps` consumer joint** (Phase J, seq side — the descent-locator's
    FRONT-END consumer).  The consumer-joint-before-producer reshape at the *locate* boundary: it
    consumes the descent-locator's not-yet-produced output — `RecSeqEntry` of the absolute
    opener-window `(tokens.toList.take (hi+1)).drop (lo-1)` of a guarded balanced flow-SEQUENCE
    subrange `[lo, hi)` — and assembles `SeqBodyProps tokens lo hi`, adding no structural content.
    All it does is the coordinate arithmetic bridging that located entry to the already-proven back
    half `seqBodyProps_of_recseqbody_window`:

    * **peel the opener** — `(take (hi+1)).drop (lo-1) = tokens[lo-1] :: (take (hi+1)).drop lo`
      (`List.getElem_cons_drop`, using `1 ≤ lo`), so the located entry takes the `op :: rest` shape
      `RecSeqEntry.seq_interior` matches;
    * **decompose the rest** — `(take (hi+1)).drop lo = (take hi).drop lo ++ [tokens[hi]]`
      (`interior_window_eq`'s slice: `List.take_add_one` + `List.drop_append_of_le_length`), exposing
      the interior window `(take hi).drop lo` and the closer `tokens[hi]`;
    * **descend** via `RecSeqEntry.seq_interior` (the opener guard `h_open` supplies `op.val =
      .flowSequenceStart`): the non-empty disjunct `RecSeqBody` feeds the back half (content-start
      recovered from the body's head via `toSafeBody.head_Q`, the windowed-slice head index
      `((·).drop lo)[0] = tokens[lo]`), the empty disjunct `interior = []` forces `lo = hi`
      (`List.length_drop`/`List.length_take`) and routes to the vacuous leaf `seqBodyProps_empty`.

    With this, the seq-side Phase-J residual collapses to the pure *locate correspondence*: "for every
    guarded balanced flow-sequence subrange, its opener-window is a `RecSeqEntry` of the body the
    producer emits."  No positional plumbing remains downstream of locate — it is the front half of
    the descent-locator's bridge (Reflection 236), now consumed end-to-end. -/
theorem seqBodyProps_of_located_entry (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi_sz : hi < tokens.size)
    (h_tpe : tokens[hi]!.val = .flowSequenceEnd)
    (h_outer_bal : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt_interior : WellTyped ((tokens.toList.take hi).drop lo))
    (h_open : tokens[lo - 1]!.val = .flowSequenceStart)
    (h_entry : RecSeqEntry ((tokens.toList.take (hi + 1)).drop (lo - 1))) :
    SeqBodyProps tokens lo hi := by
  have h_hi_len : hi < tokens.toList.length := by rw [Array.length_toList]; exact h_hi_sz
  have h_lo1_sz : lo - 1 < tokens.size := by omega
  -- rest-decomposition: the `interior ++ [cl]` slice the back half is keyed on.
  have h_rest : (tokens.toList.take (hi + 1)).drop lo
      = (tokens.toList.take hi).drop lo ++ [tokens.toList[hi]] := by
    have h_ts : tokens.toList.take (hi + 1)
        = tokens.toList.take hi ++ [tokens.toList[hi]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem h_hi_len]; rfl
    rw [h_ts]
    have h_len : lo ≤ (tokens.toList.take hi).length := by rw [List.length_take]; omega
    rw [List.drop_append_of_le_length h_len]
  -- peel the opener: the opener-window is `tokens[lo-1] :: rest`.
  have h_peel : (tokens.toList.take (hi + 1)).drop (lo - 1)
      = tokens.toList[lo - 1]'(by rw [Array.length_toList]; omega)
        :: (tokens.toList.take (hi + 1)).drop lo := by
    have hlen : lo - 1 < (tokens.toList.take (hi + 1)).length := by
      rw [List.length_take]; omega
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take] at h
    rw [show lo - 1 + 1 = lo from by omega] at h
    exact h
  -- the located entry now reads as `op :: (interior_w ++ [cl])`.
  rw [h_peel, h_rest] at h_entry
  have h_op_val : (tokens.toList[lo - 1]'(by rw [Array.length_toList]; omega)).val
      = .flowSequenceStart := by
    have hb : tokens[lo - 1]! = tokens.toList[lo - 1]'(by rw [Array.length_toList]; omega) := by
      rw [getElem!_pos tokens (lo - 1) h_lo1_sz, Array.getElem_toList]
    rw [← hb]; exact h_open
  -- descend one nesting level.
  rcases RecSeqEntry.seq_interior h_entry rfl h_op_val with h_rec | h_empty
  · -- non-empty interior: feed the back half, recovering content-start from the body head.
    have h_cs : isFlowContentStart tokens[lo]!.val := by
      obtain ⟨hl, hQ⟩ := h_rec.toSafeBody.head_Q
      have h_lo_sz : lo < tokens.size := by omega
      have h_get : (((tokens.toList.take hi).drop lo)[0]'hl).val = (tokens[lo]'h_lo_sz).val := by
        rw [List.getElem_drop, List.getElem_take, Array.getElem_toList]
        congr 2
      rw [getElem!_pos tokens lo h_lo_sz, ← h_get]
      exact hQ
    exact seqBodyProps_of_recseqbody_window tokens lo hi ((tokens.toList.take hi).drop lo)
      tokens.toList[hi] h_lo_hi h_hi_sz h_tpe h_outer_bal h_dyck h_wt_interior h_cs h_rest h_rec
  · -- empty interior: `(take hi).drop lo = []` forces `lo = hi`.
    have hlen_take : (tokens.toList.take hi).length = hi := by rw [List.length_take]; omega
    have hl : ((tokens.toList.take hi).drop lo).length
        = (tokens.toList.take hi).length - lo := List.length_drop
    rw [h_empty, hlen_take] at hl
    simp only [List.length_nil] at hl
    exact seqBodyProps_empty tokens lo hi (by omega)

/-- **Located-entry → inner-window `RecSeqBody` descent** (Phase J, seq side — the *navigation
    recursion's* per-level descent step).  The array-window form of `RecSeqEntry.seq_interior`: given
    a guarded flow-SEQUENCE subrange `[lo, hi)` whose opener `tokens[lo-1]` is a `.flowSequenceStart`
    and whose opener-window `(tokens.toList.take (hi+1)).drop (lo-1)` has been matched to a
    `RecSeqEntry` (the locate's per-window deliverable), descend ONE nesting level to the interior
    window's recursive structure: `RecSeqBody ((tokens.toList.take hi).drop lo)` (the non-empty case)
    OR `lo = hi` (the empty `[ ]` case the no-`nil` `RecSeqBody` structurally cannot represent — the
    Reflection 233 producer-contract split).

    This is the constructive *descent* counterpart of the consumer joint
    `seqBodyProps_of_located_entry`: that lemma runs the same opener-peel / rest-decomposition and
    then *consumes* the descended `RecSeqBody` straight into the terminal `SeqBodyProps`; this one
    *stops at the descended `RecSeqBody`*, so the navigation recursion can take that inner-window body
    as the IH input one nesting level down.  Crucially, its non-empty disjunct
    `RecSeqBody ((tokens.toList.take hi).drop lo)` is *exactly* the `flowSubrangesOk_of_window_producers`
    `h_seq_rec` deliverable at a window that is itself a top-level nested-sequence entry — so once the
    locate matches a guarded subrange's opener-window to its `RecSeqEntry`, this lemma finishes the
    seq producer obligation at that window with no further structural work.

    The proof is the opener-peel (`List.getElem_cons_drop`, using `1 ≤ lo`) + rest-decomposition
    (`List.take_add_one` + `List.drop_append_of_le_length`) of `seqBodyProps_of_located_entry` run
    verbatim, terminated by `RecSeqEntry.seq_interior` (the empty disjunct forced to `lo = hi` by the
    `List.length_drop`/`List.length_take` length argument) instead of the back-half consumer.
    Verified-but-unconsumed (R225): references no sorry site, frontier sorry count unchanged. -/
theorem recseqbody_window_of_located_entry (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi_sz : hi < tokens.size)
    (h_open : tokens[lo - 1]!.val = .flowSequenceStart)
    (h_entry : RecSeqEntry ((tokens.toList.take (hi + 1)).drop (lo - 1))) :
    RecSeqBody ((tokens.toList.take hi).drop lo) ∨ lo = hi := by
  have h_hi_len : hi < tokens.toList.length := by rw [Array.length_toList]; exact h_hi_sz
  have h_lo1_sz : lo - 1 < tokens.size := by omega
  -- rest-decomposition: the `interior ++ [cl]` slice the descent is keyed on.
  have h_rest : (tokens.toList.take (hi + 1)).drop lo
      = (tokens.toList.take hi).drop lo ++ [tokens.toList[hi]] := by
    have h_ts : tokens.toList.take (hi + 1)
        = tokens.toList.take hi ++ [tokens.toList[hi]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem h_hi_len]; rfl
    rw [h_ts]
    have h_len : lo ≤ (tokens.toList.take hi).length := by rw [List.length_take]; omega
    rw [List.drop_append_of_le_length h_len]
  -- peel the opener: the opener-window is `tokens[lo-1] :: rest`.
  have h_peel : (tokens.toList.take (hi + 1)).drop (lo - 1)
      = tokens.toList[lo - 1]'(by rw [Array.length_toList]; omega)
        :: (tokens.toList.take (hi + 1)).drop lo := by
    have hlen : lo - 1 < (tokens.toList.take (hi + 1)).length := by
      rw [List.length_take]; omega
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take] at h
    rw [show lo - 1 + 1 = lo from by omega] at h
    exact h
  -- the located entry now reads as `op :: (interior_w ++ [cl])`.
  rw [h_peel, h_rest] at h_entry
  have h_op_val : (tokens.toList[lo - 1]'(by rw [Array.length_toList]; omega)).val
      = .flowSequenceStart := by
    have hb : tokens[lo - 1]! = tokens.toList[lo - 1]'(by rw [Array.length_toList]; omega) := by
      rw [getElem!_pos tokens (lo - 1) h_lo1_sz, Array.getElem_toList]
    rw [← hb]; exact h_open
  -- descend one nesting level via the array-window form of `seq_interior`.
  rcases RecSeqEntry.seq_interior h_entry rfl h_op_val with h_rec | h_empty
  · left; exact h_rec
  · -- empty interior: `(take hi).drop lo = []` forces `lo = hi`.
    right
    have hlen_take : (tokens.toList.take hi).length = hi := by rw [List.length_take]; omega
    have hl : ((tokens.toList.take hi).drop lo).length
        = (tokens.toList.take hi).length - lo := List.length_drop
    rw [h_empty, hlen_take] at hl
    simp only [List.length_nil] at hl
    omega

/-- **Located-entry assembler** (Phase J, seq side — the descent-locator's FRONT-END *producer*).
    The constructive dual of `seqBodyProps_of_located_entry`: where that lemma *consumes* a located
    `RecSeqEntry` of the opener-window, this one *builds* it — the locate recursion's per-level
    final-assembly step.  Given a guarded balanced flow-SEQUENCE subrange `[lo, hi)` whose opener
    `tokens[lo-1]` is a `.flowSequenceStart`, whose close `tokens[hi]` is a `.flowSequenceEnd`, and
    whose interior window `(tokens.toList.take hi).drop lo` has been recursively established as a
    `RecSeqBody` (the locate's inductive deliverable one nesting level down), package it as the
    `RecSeqEntry` of the absolute opener-window `(tokens.toList.take (hi+1)).drop (lo-1)` — exactly
    `SeqLocated.entry`.

    It is the same positional bridge `seqBodyProps_of_located_entry` runs, now in the *constructive*
    direction: the rest-decomposition `(take (hi+1)).drop lo = (take hi).drop lo ++ [tokens[hi]]`
    (`List.take_add_one` + `List.drop_append_of_le_length`) and the opener peel `(take (hi+1)).drop
    (lo-1) = tokens[lo-1] :: …` (`List.getElem_cons_drop`, using `1 ≤ lo`) put the window into the
    `op :: (interior ++ [cl])` shape `RecSeqEntry.seq` produces; the recursive `RecSeqBody` supplies
    both the constructor's `WellBracketed interior` (via `RecSeqBody.toWellBracketed`, redundant with
    `h_rec` but the field demands it) and the recursive `h_rec` field.  Verified-but-unconsumed until
    the locate lands: it references no sorry site, so the frontier sorry count is unchanged — but it
    reduces the seq-side `SeqLocated` deliverable from "the located entry" to "the inner-window
    `RecSeqBody`" (plus the `pos`/`dyck`/`wt` bracket fields, supplied by the guards and
    `WellTyped_subrange`), the exact recursive obligation the locate descends on. -/
theorem located_entry_of_recseqbody (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi_sz : hi < tokens.size)
    (h_open : tokens[lo - 1]!.val = .flowSequenceStart)
    (h_close : tokens[hi]!.val = .flowSequenceEnd)
    (h_rec : RecSeqBody ((tokens.toList.take hi).drop lo)) :
    RecSeqEntry ((tokens.toList.take (hi + 1)).drop (lo - 1)) := by
  have h_hi_len : hi < tokens.toList.length := by rw [Array.length_toList]; exact h_hi_sz
  have h_lo1_sz : lo - 1 < tokens.size := by omega
  -- rest-decomposition: the `interior ++ [cl]` tail (mirrors `seqBodyProps_of_located_entry`).
  have h_rest : (tokens.toList.take (hi + 1)).drop lo
      = (tokens.toList.take hi).drop lo ++ [tokens.toList[hi]] := by
    have h_ts : tokens.toList.take (hi + 1)
        = tokens.toList.take hi ++ [tokens.toList[hi]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem h_hi_len]; rfl
    rw [h_ts]
    have h_len : lo ≤ (tokens.toList.take hi).length := by rw [List.length_take]; omega
    rw [List.drop_append_of_le_length h_len]
  -- peel the opener: the opener-window is `tokens[lo-1] :: rest`.
  have h_peel : (tokens.toList.take (hi + 1)).drop (lo - 1)
      = tokens.toList[lo - 1]'(by rw [Array.length_toList]; omega)
        :: (tokens.toList.take (hi + 1)).drop lo := by
    have hlen : lo - 1 < (tokens.toList.take (hi + 1)).length := by
      rw [List.length_take]; omega
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take] at h
    rw [show lo - 1 + 1 = lo from by omega] at h
    exact h
  -- target window now reads as `op :: (interior ++ [cl])`.
  rw [h_peel, h_rest]
  have h_op_val : (tokens.toList[lo - 1]'(by rw [Array.length_toList]; omega)).val
      = .flowSequenceStart := by
    have hb : tokens[lo - 1]! = tokens.toList[lo - 1]'(by rw [Array.length_toList]; omega) := by
      rw [getElem!_pos tokens (lo - 1) h_lo1_sz, Array.getElem_toList]
    rw [← hb]; exact h_open
  have h_cl_val : (tokens.toList[hi]'h_hi_len).val = .flowSequenceEnd := by
    have hb : tokens[hi]! = tokens.toList[hi]'h_hi_len := by
      rw [getElem!_pos tokens hi h_hi_sz, Array.getElem_toList]
    rw [← hb]; exact h_close
  exact RecSeqEntry.seq _ _ _ h_op_val h_cl_val h_rec.toWellBracketed h_rec

/-- **A recursive seq entry is non-empty.**  Every `RecSeqEntry` constructor produces a `cons` list
    (`[t]` = `t :: []`, or `op :: …`), so the entry is never `[]`.  The `h_ne` field the body-level
    `RecSeqBody.cons`/`.single` constructors demand, supplied here as a structural projection (cf.
    `RecSeqEntry.toEntrySafe`/`toWellBracketed`). -/
theorem RecSeqEntry.ne_nil {e : List (Positioned YamlToken)} (h : RecSeqEntry e) : e ≠ [] := by
  cases h <;> simp

/-- **A recursive seq entry's head is a content-start token.**  Each constructor's first token is a
    scalar (`scalar`), a `.flowSequenceStart` (`seqEmpty`/`seq`), or a `.flowMappingStart` (`map`) —
    exactly the three `ContentStartTok` cases.  The `h_head` field `RecSeqBody.cons`/`.single` demand,
    supplied as a structural projection so the body-level assemblers need not re-derive it from the
    per-entry token shape.  (The `h_ne` argument is threaded through to `List.head`; by proof
    irrelevance any `e ≠ []` witness gives the same head.) -/
theorem RecSeqEntry.head_contentStart {e : List (Positioned YamlToken)}
    (h : RecSeqEntry e) (h_ne : e ≠ []) : ContentStartTok (e.head h_ne).val := by
  cases h with
  | scalar t c s ht => rw [List.head_cons]; exact Or.inl ⟨c, s, ht⟩
  | seqEmpty op cl h_op _ => rw [List.head_cons]; exact Or.inr (Or.inl h_op)
  | seq op cl interior h_op _ _ _ => rw [List.head_cons]; exact Or.inr (Or.inl h_op)
  | map op cl interior h_op _ _ => rw [List.head_cons]; exact Or.inr (Or.inr h_op)

/-- **Body-cons window assembler** (Phase J, seq side — the navigation recursion's *advance* step).
    The third positional move of the locate recursion, the structural complement to the two already
    landed: `recseqbody_window_of_located_entry` *descends* into a nested entry's interior, and
    `located_entry_of_recseqbody` *builds* an entry from its inner-window `RecSeqBody`; this one
    *advances* along the body — given the window splits at a depth-`0` `.flowEntry` separator at
    position `m` into a leading `RecSeqEntry` over `[lo, m)` and a trailing `RecSeqBody` over
    `[m+1, hi)`, it produces the whole window's `RecSeqBody` over `[lo, hi)`.

    It is the positional lift of the `RecSeqBody.cons` constructor: the window identity
    `(take hi).drop lo = (take m).drop lo ++ tokens[m] :: (take hi).drop (m+1)` is assembled from the
    same take/drop plumbing the descent and build steps use — the segment split
    (`List.take_append_drop` + `List.take_take` + `List.drop_append_of_le_length`, using `lo ≤ m`)
    and the separator peel (`List.getElem_cons_drop` + `List.getElem_take`, using `m < hi`) — and the
    constructor's `h_ne`/`h_head` fields are discharged by the `RecSeqEntry.ne_nil` /
    `RecSeqEntry.head_contentStart` projections above, so the caller supplies only the located entry,
    the separator token, and the recursive rest.  Verified-but-unconsumed until the locate lands: it
    references no sorry site, so the frontier sorry count is unchanged — it completes the recursion's
    structural moves, leaving as residual only the *analytical* entry-boundary location (find, for a
    guarded window, the depth-`0` extent of its first entry and the matching separator). -/
theorem recseqbody_cons_window (tokens : Array (Positioned YamlToken)) (lo m hi : Nat)
    (h_lo_m : lo ≤ m) (h_m_hi : m < hi) (h_hi_sz : hi < tokens.size)
    (h_fe : tokens[m]!.val = .flowEntry)
    (h_entry : RecSeqEntry ((tokens.toList.take m).drop lo))
    (h_rest : RecSeqBody ((tokens.toList.take hi).drop (m + 1))) :
    RecSeqBody ((tokens.toList.take hi).drop lo) := by
  have h_m_len : m < tokens.toList.length := by rw [Array.length_toList]; omega
  have h_m_sz : m < tokens.size := by omega
  -- Segment split: the leading entry window `[lo, m)` is a prefix of the whole window `[lo, hi)`.
  have hA : (tokens.toList.take hi).drop lo
      = (tokens.toList.take m).drop lo ++ (tokens.toList.take hi).drop m := by
    rw [← List.take_append_drop (m - lo) ((tokens.toList.take hi).drop lo)]
    congr 1
    · rw [List.drop_take, List.drop_take, List.take_take,
        Nat.min_eq_left (show m - lo ≤ hi - lo by omega)]
    · rw [List.drop_drop, Nat.add_sub_cancel' h_lo_m]
  -- Separator peel: the depth-`0` `.flowEntry` at `m` heads the trailing window `[m, hi)`.
  have hB : (tokens.toList.take hi).drop m
      = tokens.toList[m]'h_m_len :: (tokens.toList.take hi).drop (m + 1) := by
    have hlen : m < (tokens.toList.take hi).length := by
      rw [List.length_take,
        Nat.min_eq_left (show hi ≤ tokens.toList.length by rw [Array.length_toList]; omega)]
      exact h_m_hi
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take] at h
    exact h
  have h_fe_val : (tokens.toList[m]'h_m_len).val = .flowEntry := by
    have hb : tokens[m]! = tokens.toList[m]'h_m_len := by
      rw [getElem!_pos tokens m h_m_sz, Array.getElem_toList]
    rw [← hb]; exact h_fe
  rw [hA, hB]
  exact RecSeqBody.cons ((tokens.toList.take m).drop lo) (tokens.toList[m]'h_m_len)
    ((tokens.toList.take hi).drop (m + 1)) (RecSeqEntry.ne_nil h_entry) h_entry
    (RecSeqEntry.head_contentStart h_entry (RecSeqEntry.ne_nil h_entry)) h_fe_val h_rest

/-- **Body-single window assembler** (Phase J, seq side — the navigation recursion's *terminate* step).
    The fourth positional move, and the one the DESCEND/BUILD/ADVANCE enumeration *missed*:
    `RecSeqBody` has **two** constructors — `cons` (entry · separator · rest) and `single` (a lone
    entry, no trailing separator) — and the three landed moves all lift `cons`-side structure
    (`recseqbody_window_of_located_entry` descends, `located_entry_of_recseqbody` builds, and
    `recseqbody_cons_window` advances via `RecSeqBody.cons`).  None lift `single`, so the recursion
    had no way to *terminate*: `recseqbody_cons_window` defers its tail to `h_rest : RecSeqBody`, which
    must eventually be produced by the *last* item — the window where `firstEntryBoundary` returns
    `m = hi` (no more depth-`0` separators).  That terminal window is exactly a `RecSeqBody.single`.

    Where `recseqbody_cons_window` needs the full window-identity plumbing (segment split + separator
    peel) to expose the `e ++ fe :: rest` shape `RecSeqBody.cons` demands, this terminal move needs
    *none*: `RecSeqBody.single` takes the entry list verbatim, so the whole-window `RecSeqEntry` *is*
    the constructor's argument.  The only fields are `h_ne`/`h_head`, discharged by the same
    `RecSeqEntry.ne_nil` / `RecSeqEntry.head_contentStart` projections the cons step uses.  It is the
    simplest of the four moves — the recursion's base case, not a compositional step.

    Verified-but-unconsumed until the locate recursion lands: references no sorry site, so the
    frontier sorry count is unchanged at 4 — it completes the *constructor coverage* of the seq
    structural moves (every `RecSeqBody` constructor now has a window lift), leaving as residual only
    the analytical head-dispatch that selects which shape-side lift produces each `[lo, m)` entry. -/
theorem recseqbody_single_window (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_entry : RecSeqEntry ((tokens.toList.take hi).drop lo)) :
    RecSeqBody ((tokens.toList.take hi).drop lo) :=
  RecSeqBody.single ((tokens.toList.take hi).drop lo) (RecSeqEntry.ne_nil h_entry) h_entry
    (RecSeqEntry.head_contentStart h_entry (RecSeqEntry.ne_nil h_entry))

/-- **Body window assembler — the seq locate DRIVER's grammar-free ADVANCE/TERMINATE step** (Phase J,
    seq side).  The driver's per-window work splits cleanly into two halves: a *classify* half that
    locates the first entry's extent `m` (`firstEntryBoundary`) and lifts the window `[lo, m)` into a
    `RecSeqEntry` (the four head-dispatch branches), and this *assemble* half that, given that located
    entry plus the recursion's tail oracle, folds them into the whole-window `RecSeqBody`.  The two
    structural moves it bundles are already proven — `recseqbody_cons_window` (ADVANCE, lift
    `RecSeqBody.cons`) and `recseqbody_single_window` (TERMINATE, lift `RecSeqBody.single`); this lemma
    is their *selector*, dispatching on whether `firstEntryBoundary`'s split point `m` reached the
    window end.

    The lesson the bundling isolates: the assemble half names **no per-window grammar substrate** at
    all.  Unlike the classify half — whose dispatches consume head-shape disjunctions and value-end
    successor facts (`h_succ`) that neither `WellTyped` nor the producer contract carries — this step
    needs only the structural facts the locator already produces: the marker disjunction `m = hi ∨
    tokens[m] = .flowEntry` (`firstEntryBoundary`'s MARKER clause) selects the branch, and the tail
    oracle is supplied *guarded* by `m < hi` (so the TERMINATE branch never invokes it).  TERMINATE
    (`m = hi`) is a pure rewrite of the located entry into `recseqbody_single_window`; ADVANCE
    (`m < hi`, hence `tokens[m] = .flowEntry` by `Or.resolve_left`) hands the entry, the separator, and
    the oracle's tail `RecSeqBody [m+1, hi)` to `recseqbody_cons_window`.  So landing it pins the driver's
    remaining residual to *exactly* the grammar-bearing classify half — the per-window head-shape /
    successor substrate (recoverable via `WellTyped_subrange` for the bracket interior, but owing the
    content grammar `WellTyped` does not encode) and the `Nat.strongRecOn` width metric that discharges
    the tail oracle.

    By the R264 mirror discriminator it names a collection-specific deliverable type (`RecSeqEntry`/
    `RecSeqBody`), so it re-splits the map axis: `recmapbody_window_assemble` is the symmetric next brick.
    Verified-but-unconsumed until the driver lands (R225): composes only existing lemmas, references no
    sorry site, frontier sorry count unchanged at 4. -/
theorem recseqbody_window_assemble (tokens : Array (Positioned YamlToken)) (lo m hi : Nat)
    (h_lo_m : lo < m) (h_m_hi : m ≤ hi) (h_hi_sz : hi < tokens.size)
    (h_m_marker : m = hi ∨ tokens[m]!.val = .flowEntry)
    (h_entry : RecSeqEntry ((tokens.toList.take m).drop lo))
    (h_tail : m < hi → RecSeqBody ((tokens.toList.take hi).drop (m + 1))) :
    RecSeqBody ((tokens.toList.take hi).drop lo) := by
  rcases Nat.lt_or_ge m hi with h_lt | h_ge
  · -- ADVANCE: a depth-`0` `.flowEntry` separator at `m`; cons the located entry onto the tail oracle.
    have h_fe : tokens[m]!.val = .flowEntry := h_m_marker.resolve_left (by omega)
    exact recseqbody_cons_window tokens lo m hi (Nat.le_of_lt h_lo_m) h_lt h_hi_sz h_fe h_entry
      (h_tail h_lt)
  · -- TERMINATE: `m = hi`, so the whole window is the one located entry, no trailing separator.
    have h_eq : m = hi := Nat.le_antisymm h_m_hi h_ge
    exact recseqbody_single_window tokens lo hi (h_eq ▸ h_entry)

/-- **A recursive map pair is non-empty.**  The sole `RecMapPair.mk` constructor produces a `cons`
    list (`kt :: …`), so the pair is never `[]`.  The map mirror of `RecSeqEntry.ne_nil`: the `h_ne`
    field the body-level `RecMapBody.cons`/`.single` constructors demand, supplied as a structural
    projection (cf. `RecMapPair.toEntrySafe`/`toWellBracketed`). -/
theorem RecMapPair.ne_nil {p : List (Positioned YamlToken)} (h : RecMapPair p) : p ≠ [] := by
  cases h <;> simp

/-- **A recursive map pair's head is the `.key` token.**  The sole constructor's first token is the
    key `kt` with `kt.val = .key`, exactly the `h_head : (p.head h_ne).val = .key` field the
    `RecMapBody.cons`/`.single` constructors demand — the map mirror of `RecSeqEntry.head_contentStart`
    (single `.key` case vs the three `ContentStartTok` cases), supplied as a structural projection so
    the body-level assemblers need not re-derive it from the per-pair token shape.  (The `h_ne`
    argument is threaded through to `List.head`; by proof irrelevance any `p ≠ []` witness gives the
    same head.) -/
theorem RecMapPair.head_key {p : List (Positioned YamlToken)}
    (h : RecMapPair p) (h_ne : p ≠ []) : (p.head h_ne).val = .key := by
  cases h with
  | mk kt block_k vt block_v h_kt _ _ _ => rw [List.head_cons]; exact h_kt

/-- **Body-cons window assembler** (Phase J, map side — the navigation recursion's *advance* step).
    The map mirror of `recseqbody_cons_window`, completing the *advance* structural move on the map
    axis as well (the seq→map mirror per the R260→R261 / R255→R256 rhythm): given the window splits at
    a depth-`0` `.flowEntry` separator at position `m` into a leading `RecMapPair` over `[lo, m)` and a
    trailing `RecMapBody` over `[m+1, hi)`, it produces the whole window's `RecMapBody` over `[lo, hi)`.

    The positional plumbing is *verbatim* the seq side — the window identity
    `(take hi).drop lo = (take m).drop lo ++ tokens[m] :: (take hi).drop (m+1)` and its segment-split /
    separator-peel derivation are bracket- and collection-agnostic, depending only on `lo ≤ m < hi` and the
    `.flowEntry` separator, not on whether the leading item is a seq entry or a map pair.  Only the
    terminal constructor differs: `RecMapBody.cons` in place of `RecSeqBody.cons`, with the leading
    item a `RecMapPair` and its `h_ne`/`h_head` fields discharged by the `RecMapPair.ne_nil` /
    `RecMapPair.head_key` projections above (head is `.key`, vs the seq entry's `ContentStartTok`).
    Verified-but-unconsumed until the map locate lands: it references no sorry site, so the frontier
    sorry count is unchanged — with this the *advance* move is complete on both axes, and the locate
    recursion's residual is, on both seq and map sides, only the *analytical* entry-boundary location. -/
theorem recmapbody_cons_window (tokens : Array (Positioned YamlToken)) (lo m hi : Nat)
    (h_lo_m : lo ≤ m) (h_m_hi : m < hi) (h_hi_sz : hi < tokens.size)
    (h_fe : tokens[m]!.val = .flowEntry)
    (h_pair : RecMapPair ((tokens.toList.take m).drop lo))
    (h_rest : RecMapBody ((tokens.toList.take hi).drop (m + 1))) :
    RecMapBody ((tokens.toList.take hi).drop lo) := by
  have h_m_len : m < tokens.toList.length := by rw [Array.length_toList]; omega
  have h_m_sz : m < tokens.size := by omega
  -- Segment split: the leading pair window `[lo, m)` is a prefix of the whole window `[lo, hi)`.
  have hA : (tokens.toList.take hi).drop lo
      = (tokens.toList.take m).drop lo ++ (tokens.toList.take hi).drop m := by
    rw [← List.take_append_drop (m - lo) ((tokens.toList.take hi).drop lo)]
    congr 1
    · rw [List.drop_take, List.drop_take, List.take_take,
        Nat.min_eq_left (show m - lo ≤ hi - lo by omega)]
    · rw [List.drop_drop, Nat.add_sub_cancel' h_lo_m]
  -- Separator peel: the depth-`0` `.flowEntry` at `m` heads the trailing window `[m, hi)`.
  have hB : (tokens.toList.take hi).drop m
      = tokens.toList[m]'h_m_len :: (tokens.toList.take hi).drop (m + 1) := by
    have hlen : m < (tokens.toList.take hi).length := by
      rw [List.length_take,
        Nat.min_eq_left (show hi ≤ tokens.toList.length by rw [Array.length_toList]; omega)]
      exact h_m_hi
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take] at h
    exact h
  have h_fe_val : (tokens.toList[m]'h_m_len).val = .flowEntry := by
    have hb : tokens[m]! = tokens.toList[m]'h_m_len := by
      rw [getElem!_pos tokens m h_m_sz, Array.getElem_toList]
    rw [← hb]; exact h_fe
  rw [hA, hB]
  exact RecMapBody.cons ((tokens.toList.take m).drop lo) (tokens.toList[m]'h_m_len)
    ((tokens.toList.take hi).drop (m + 1)) (RecMapPair.ne_nil h_pair) h_pair
    (RecMapPair.head_key h_pair (RecMapPair.ne_nil h_pair)) h_fe_val h_rest

/-- **Body-single window assembler** (Phase J, map side — the navigation recursion's *terminate*
    step).  The map mirror of `recseqbody_single_window` (the seq→map mirror per the R260→R261 /
    R255→R256 rhythm), and the move that completes *constructor coverage* on the map axis: like
    `RecSeqBody`, `RecMapBody` has **two** constructors — `cons` (pair · separator · rest) and
    `single` (a lone pair, no trailing separator) — and `recmapbody_cons_window` lifts only `cons`,
    so the map recursion likewise had a step (`recmapbody_cons_window` defers its tail to
    `h_rest : RecMapBody`) but no *base*: the terminal window, where `firstEntryBoundary` returns
    `m = hi` (no more depth-`0` separators), is exactly a `RecMapBody.single`.

    As on the seq side, this terminal move needs *no* window plumbing — where `recmapbody_cons_window`
    splits the window to expose the `p ++ fe :: rest` shape `RecMapBody.cons` demands, `RecMapBody.single`
    takes the pair list verbatim, so the whole-window `RecMapPair` *is* the constructor's argument.  The
    only fields are `h_ne`/`h_head`, discharged by the same `RecMapPair.ne_nil` / `RecMapPair.head_key`
    projections the cons step uses.  It is the cheapest of the four map moves — the recursion's base
    case, not a compositional step (R269's complexity law: a base-case lift's cost is zero because its
    constructor's index *is* the input window verbatim).

    Verified-but-unconsumed until the map locate recursion lands: references no sorry site, so the
    frontier sorry count is unchanged.  With this, *every* `RecMapBody` constructor has a window lift on
    both axes; the locate recursion's residual is, on seq and map alike, only the analytical
    head-dispatch that classifies each `[lo, m)` window and selects its shape-side lift. -/
theorem recmapbody_single_window (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_pair : RecMapPair ((tokens.toList.take hi).drop lo)) :
    RecMapBody ((tokens.toList.take hi).drop lo) :=
  RecMapBody.single ((tokens.toList.take hi).drop lo) (RecMapPair.ne_nil h_pair) h_pair
    (RecMapPair.head_key h_pair (RecMapPair.ne_nil h_pair))

/-- **Body window assembler — the map locate DRIVER's grammar-free ADVANCE/TERMINATE step** (Phase J,
    map side).  The map mirror of `recseqbody_window_assemble` (the seq→map mirror per the R260→R261 /
    R278 rhythm), and the brick that completes the driver's grammar-free *assemble* half on **both**
    axes.  As on the seq side, the driver's per-window work splits into a *classify* half that locates
    the first pair's extent `m` (`firstEntryBoundary`) and lifts the window `[lo, m)` into a
    `RecMapPair` (the map head-dispatch), and this *assemble* half that, given that located pair plus
    the recursion's tail oracle, folds them into the whole-window `RecMapBody`.  The two structural
    moves it bundles are already proven — `recmapbody_cons_window` (ADVANCE, lift `RecMapBody.cons`)
    and `recmapbody_single_window` (TERMINATE, lift `RecMapBody.single`); this lemma is their
    *selector*, dispatching on whether `firstEntryBoundary`'s split point `m` reached the window end.

    The R278 lesson recurs one level up: the selector transports the seq assemble's control flow
    *verbatim* — same `Nat.lt_or_ge m hi` split, same marker-disjunction `Or.resolve_left`, same
    `Nat.le_antisymm` collapse on TERMINATE, same `h_eq ▸` rewrite of the located item — changing only
    the deliverable type (`RecMapPair`/`RecMapBody` for `RecSeqEntry`/`RecSeqBody`) and the two
    structural moves it calls.  The marker token (`.flowEntry`) and the tail-oracle guard (`m < hi`)
    are genuinely collection-agnostic: the body separator is the same for both kinds (cf.
    `exists_least_in_range` — *no* seq/map mirror in the boundary predicate), so the assemble half
    names no collection-specific knob beyond the deliverable type itself.  Costing the mirror confirms
    the assemble step is the reusable *shape*; with it the grammar-free half of the driver is complete
    on both axes, pinning the *entire* remaining locate residual to the grammar-bearing classify half
    (per-pair head/key substrate + the `Nat.strongRecOn` width metric) on seq and map alike.

    Verified-but-unconsumed until the driver lands (R225): composes only existing lemmas, references no
    sorry site, frontier sorry count unchanged at 4. -/
theorem recmapbody_window_assemble (tokens : Array (Positioned YamlToken)) (lo m hi : Nat)
    (h_lo_m : lo < m) (h_m_hi : m ≤ hi) (h_hi_sz : hi < tokens.size)
    (h_m_marker : m = hi ∨ tokens[m]!.val = .flowEntry)
    (h_pair : RecMapPair ((tokens.toList.take m).drop lo))
    (h_tail : m < hi → RecMapBody ((tokens.toList.take hi).drop (m + 1))) :
    RecMapBody ((tokens.toList.take hi).drop lo) := by
  rcases Nat.lt_or_ge m hi with h_lt | h_ge
  · -- ADVANCE: a depth-`0` `.flowEntry` separator at `m`; cons the located pair onto the tail oracle.
    have h_fe : tokens[m]!.val = .flowEntry := h_m_marker.resolve_left (by omega)
    exact recmapbody_cons_window tokens lo m hi (Nat.le_of_lt h_lo_m) h_lt h_hi_sz h_fe h_pair
      (h_tail h_lt)
  · -- TERMINATE: `m = hi`, so the whole window is the one located pair, no trailing separator.
    have h_eq : m = hi := Nat.le_antisymm h_m_hi h_ge
    exact recmapbody_single_window tokens lo hi (h_eq ▸ h_pair)

/-- **Least witness of a decidable predicate in a bounded range** (Phase J — the navigation
    skeleton's combinatorial core).  Given a decidable predicate `P` that holds at the range end
    `start + gap`, there is a *least* `m` in `[start, start + gap]` satisfying `P`, together with the
    minimality certificate that no `k` in `[start, m)` satisfies `P`.

    Fully constructive: structural induction on `gap`, scanning upward from `start` with the
    decidability instance (`if h : P start then …`) — no `Nat.find`, no classical choice, no
    well-founded recursion.  This is the generic well-ordering brick the entry-boundary locator
    instantiates; it is deliberately predicate-agnostic so the *same* lemma serves both the seq and
    the map locate recursions (the `.flowEntry` separator that marks a body split is the same token
    for both collection kinds, so the boundary predicate is shared — no seq versus map mirror here).

    Verified-but-unconsumed (R225): references no sorry site, frontier sorry count unchanged. -/
theorem exists_least_in_range (P : Nat → Prop) [DecidablePred P] :
    ∀ (gap start : Nat), P (start + gap) →
      ∃ m, start ≤ m ∧ m ≤ start + gap ∧ P m ∧ ∀ k, start ≤ k → k < m → ¬ P k := by
  intro gap
  induction gap with
  | zero =>
    intro start hP
    refine ⟨start, Nat.le_refl _, ?_, ?_, ?_⟩
    · omega
    · simpa using hP
    · intro k hk1 hk2; exfalso; omega
  | succ g ih =>
    intro start hP
    if h0 : P start then
      refine ⟨start, Nat.le_refl _, ?_, h0, ?_⟩
      · omega
      · intro k hk1 hk2; exfalso; omega
    else
      have hP' : P ((start + 1) + g) := by
        have he : (start + 1) + g = start + (g + 1) := by omega
        rw [he]; exact hP
      obtain ⟨m, hm1, hm2, hm3, hm4⟩ := ih (start + 1) hP'
      refine ⟨m, by omega, by omega, hm3, ?_⟩
      intro k hk1 hk2
      rcases Nat.lt_or_ge k (start + 1) with hlt | hge
      · have hk_eq : k = start := by omega
        rw [hk_eq]; exact h0
      · exact hm4 k hge hk2

/-- **First entry-boundary locator** (Phase J — the analytical entry-boundary location, first brick;
    seq and map share it).  Given a balanced body-interior window `[lo, hi)` (`flowBracketBalance
    tokens lo hi = 0`, the guard the per-window `Rec…Body` producer owns), there is a least depth-`0`
    *boundary marker* `m` in `(lo, hi]` — a position where the running balance from `lo` returns to
    `0` and which is either the window end (`m = hi`) or a `.flowEntry` separator — such that no
    earlier interior position is such a marker.

    This pins the split point the locate recursion consumes: the *first* body item occupies `[lo, m)`
    (balanced, containing no depth-`0` separator, by the minimality clause), followed at `m` either by
    the trailing separator (the `ADVANCE` move's `tokens[m]! = .flowEntry`) or by the window end (the
    last item, a `single`).  It is the input side of the entry-boundary analysis — locating *where* the
    first item ends — separate from the still-owed shape side (showing `[lo, m)` is a scalar or a
    matched-bracket `RecSeqEntry`/`RecMapPair`, via `flowBracketBalance_matching_close`).

    Axis-agnostic: the boundary token `.flowEntry` is shared by sequences and mappings, so this single
    lemma feeds both the `RecSeqBody` and the `RecMapBody` recursions — there is no seq versus map
    mirror to land (contrast the structural moves, where the terminal constructor differed).

    Verified-but-unconsumed (R225): instantiates only `exists_least_in_range`, references no sorry
    site, frontier sorry count unchanged. -/
theorem firstEntryBoundary (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo_hi : lo < hi)
    (h_total : flowBracketBalance tokens lo hi = 0) :
    ∃ m, lo < m ∧ m ≤ hi ∧
      flowBracketBalance tokens lo m = 0 ∧
      (m = hi ∨ tokens[m]!.val = .flowEntry) ∧
      (∀ k, lo < k → k < m →
        ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry))) := by
  obtain ⟨m, hm1, hm2, hm3, hm4⟩ :=
    exists_least_in_range
      (fun m => flowBracketBalance tokens lo m = 0 ∧ (m = hi ∨ tokens[m]!.val = .flowEntry))
      (hi - (lo + 1)) (lo + 1)
      (by
        have he : (lo + 1) + (hi - (lo + 1)) = hi := by omega
        rw [he]; exact ⟨h_total, Or.inl rfl⟩)
  refine ⟨m, by omega, by omega, hm3.1, hm3.2, ?_⟩
  intro k hk1 hk2
  exact hm4 k (by omega) hk2

/-- **ADVANCE-step tail invariant** (Phase J — the locate recursion's *invariant-preservation*
    certificate; seq and map share it).  The four structural moves, `firstEntryBoundary`, and the full
    shape side give the recursion everything *except* the proof that, after it `ADVANCE`s past a
    depth-`0` `.flowEntry` separator at `m`, the remaining tail `[m+1, hi)` is *itself* a valid
    recursive sub-instance — and without that the driver (`Nat.strongRecOn` on the window width) cannot
    take its recursive step.  This lemma is exactly that missing primitive.  Given a balanced
    body-interior window `[lo, hi)` and a depth-`0` separator at `m` (`lo ≤ m < hi`, balance
    `lo..m = 0`, `tokens[m] = .flowEntry`), it delivers the three facts the recursive call on
    `[m+1, hi)` needs:

      (a) the prefix *through* the separator is balanced (`balance lo (m+1) = 0`);
      (b) the **tail is balanced** (`balance (m+1) hi = 0`) — the precondition `firstEntryBoundary` and
          the shape-side classifier require to act on `[m+1, hi)` at all;
      (c) the tail **re-bases**: every depth measured from the outer origin `lo` agrees with the one
          measured from the new origin `m+1` (`balance lo p = balance (m+1) p` for `m+1 ≤ p ≤ hi`), so
          any outer-origin depth-`0` fact about the tail (the *next* separator's position, the
          classifier's no-interior-separator minimality) transports into the recursion's local frame
          for free — the recursion threads its invariants from a moving origin without re-deriving the
          balance from scratch each step.

    All three are pure bracket-balance algebra: `flowBracketBalance_compose` (additivity split at `m`
    and at `m+1`) and `flowBracketBalance_single` (the separator contributes
    `flowBracketDelta .flowEntry = 0`, so crossing it neither opens nor closes a bracket).  Like
    `firstEntryBoundary`, and unlike the four structural moves, it names **no collection-specific
    deliverable type** — it is phrased purely over the shared token stream (bracket balance, the shared
    `.flowEntry` separator), so it is written ONCE and feeds both the `RecSeqBody` and the `RecMapBody`
    recursions (the seq/map mirror discriminator: a navigation brick mirrors exactly when it mentions a
    deliverable type; a shared-token-stream balance fact does not).

    Verified-but-unconsumed until the locate recursion lands: references no sorry site, frontier sorry
    count unchanged. -/
theorem advanceTail_invariant (tokens : Array (Positioned YamlToken)) (lo m hi : Nat)
    (h_lo_m : lo ≤ m) (h_m_hi : m < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_m_bal : flowBracketBalance tokens lo m = 0)
    (h_sep : tokens[m]!.val = .flowEntry)
    (h_total : flowBracketBalance tokens lo hi = 0) :
    flowBracketBalance tokens lo (m + 1) = 0 ∧
    flowBracketBalance tokens (m + 1) hi = 0 ∧
    (∀ p, m + 1 ≤ p → p ≤ hi →
      flowBracketBalance tokens lo p = flowBracketBalance tokens (m + 1) p) := by
  have h_m_sz : m < tokens.size := by omega
  have h_m_len : m < tokens.toList.length := by rw [Array.length_toList]; exact h_m_sz
  -- the separator's bracket delta is 0, so the single-token range `[m, m+1)` is balanced.
  have h_val : (tokens.toList[m]'h_m_len).val = .flowEntry := by
    have hb : tokens[m]! = tokens.toList[m]'h_m_len := by
      rw [getElem!_pos tokens m h_m_sz, Array.getElem_toList]
    rw [← hb]; exact h_sep
  have h_single : flowBracketBalance tokens m (m + 1) = 0 := by
    rw [flowBracketBalance_single tokens m h_m_len, h_val]; rfl
  -- (a) prefix through the separator: `lo..(m+1) = lo..m + m..(m+1) = 0 + 0`.
  have h_prefix : flowBracketBalance tokens lo (m + 1) = 0 := by
    rw [flowBracketBalance_compose tokens lo m (m + 1) h_lo_m (by omega), h_m_bal]; omega
  -- (b) tail: `lo..hi = lo..(m+1) + (m+1)..hi`, so `(m+1)..hi = total − prefix = 0`.
  have h_tail : flowBracketBalance tokens (m + 1) hi = 0 := by
    have hc := flowBracketBalance_compose tokens lo (m + 1) hi (by omega) (by omega)
    rw [h_total, h_prefix] at hc; omega
  refine ⟨h_prefix, h_tail, ?_⟩
  -- (c) re-basing: `lo..p = lo..(m+1) + (m+1)..p = 0 + (m+1)..p`.
  intro p hp1 hp2
  rw [flowBracketBalance_compose tokens lo (m + 1) p (by omega) hp1, h_prefix]; omega

/-- **The flow body-window guard** (Phase J — the concrete instantiation of `windowWidth_strongRecOn`'s
    abstract per-window guard `G`).  The combinator that closes the locate recursion is abstract over a
    guard `G : Nat → Nat → Prop` (the inhabitable region) and a deliverable `P`; to *drive* it on the
    seq/map body recursion that region must be named.  This structure is that name: the predicate a
    balanced flow body subrange `[lo, hi)` carries when it is a legitimate recursion instance — the
    frame bounds (`2 ≤ lo`, `hi ≤ size - 2`, `hi < size`), **non-emptiness** (`lo < hi`, the R285 peel:
    the empty window has no `RecSeqBody`/`RecMapBody` and must be EXCLUDED from `G`, never handed to the
    step), the bracket-balance closure (`balanced` + the `dyck` prefix-nonnegativity), and the content
    invariant `WellTyped` the head-shape grammar will later be read off of.

    Crucially it names **no collection-specific deliverable type** — no `RecSeqBody`, no `RecMapBody`,
    only the shared token-stream facts (`flowBracketBalance`, `WellTyped`).  So by the seq/map mirror
    discriminator ([[ref-entry-boundary-input-shape-split]]) it does NOT re-split: it is the SHARED
    guard `G` for both axes' body recursions (`windowWidth_strongRecOn (G := FlowBodyWindow tokens) …`
    instantiated once with `P := RecSeqBody …`, once with `P := RecMapBody …`).  It is the guard-level
    companion of the position-level shared bricks `firstEntryBoundary` and `advanceTail_invariant`
    (written once, fed to both recursions); the combinator's `G`/`P` factoring is exactly what lets one
    guard structure serve both motives. -/
structure FlowBodyWindow (tokens : Array (Positioned YamlToken)) (lo hi : Nat) : Prop where
  lo_ge : 2 ≤ lo
  lo_lt_hi : lo < hi
  hi_le : hi ≤ tokens.size - 2
  hi_lt : hi < tokens.size
  balanced : flowBracketBalance tokens lo hi = 0
  dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0
  wellTyped : WellTyped ((tokens.toList.take hi).drop lo)

/-- **ADVANCE guard-preservation** (Phase J — the combinator's `G`-preservation across the locate
    recursion's *advance* edge).  `windowWidth_strongRecOn` hands the per-window step an oracle
    `∀ lo' hi', hi' - lo' < hi - lo → G lo' hi' → P lo' hi'` for every strictly-narrower guarded
    window; for the step to USE that oracle on the tail `[m+1, hi)` after consuming the first entry at a
    depth-`0` `.flowEntry` separator `m`, it must first show the tail STILL satisfies the guard `G`.
    This lemma is that obligation, and it is grammar-free: it transports the whole `FlowBodyWindow`
    guard from `[lo, hi)` to `[m+1, hi)` given only the separator's position facts (and the
    non-emptiness `m + 1 < hi`, deferred to the caller — "no trailing separator" is the head-shape
    grammar's burden, not the guard's).

    It is the guard-level lift of `advanceTail_invariant`, which already delivers the balance half
    (prefix-balanced, tail-balanced, and the depth re-basing `balance lo p = balance (m+1) p`); this
    lemma adds the two remaining guard fields: the tail's `dyck` (each tail prefix re-based to the outer
    origin, then `≥ 0` by the outer `dyck`) and the tail's `WellTyped` (the balanced-subrange
    transporter `WellTyped_subrange` carries it down from `[lo, hi)`).  The frame bounds and
    non-emptiness are arithmetic.  Like its balance half and `firstEntryBoundary`, it names no
    deliverable type, so it serves BOTH axes' recursions unchanged ([[ref-structural-moves-complete-recursion]]:
    the ADVANCE positional move, here lifted to the guard the combinator descends along).

    Verified-but-unconsumed until the per-window step instantiates the combinator (R225): references no
    sorry site, frontier sorry count unchanged at 4. -/
theorem flowBodyWindow_advance (tokens : Array (Positioned YamlToken)) (lo m hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_lo_m : lo ≤ m) (h_m1_hi : m + 1 < hi)
    (h_m_bal : flowBracketBalance tokens lo m = 0)
    (h_sep : tokens[m]!.val = .flowEntry) :
    FlowBodyWindow tokens (m + 1) hi := by
  obtain ⟨h_lo2, h_lo_hi, h_hi_sz2, h_hi_sz, h_bal, h_dyck, h_wt⟩ := h_win
  have h_m_hi : m < hi := by omega
  obtain ⟨h_prefix, h_tail, h_rebase⟩ :=
    advanceTail_invariant tokens lo m hi h_lo_m h_m_hi (Nat.le_of_lt h_hi_sz) h_m_bal h_sep h_bal
  -- Dyck on the tail `[m+1, hi)`: re-base each tail prefix to the outer origin `lo`, then `≥ 0`.
  have h_dyck' : ∀ i, m + 1 ≤ i → i ≤ hi → flowBracketBalance tokens (m + 1) i ≥ 0 := by
    intro i hi1 hi2
    rw [← h_rebase i hi1 hi2]
    exact h_dyck i (by omega) hi2
  refine ⟨by omega, h_m1_hi, h_hi_sz2, h_hi_sz, h_tail, h_dyck', ?_⟩
  -- WellTyped on the tail via the balanced-subrange transporter (the subrange `[m+1, hi) ⊆ [lo, hi)`).
  exact WellTyped_subrange tokens lo (m + 1) hi hi (by omega) (by omega) (Nat.le_refl hi)
    (Nat.le_of_lt h_hi_sz) h_wt h_tail h_dyck'

/-- **DESCEND guard-preservation** (Phase J — the combinator's `G`-preservation across the locate
    recursion's *descend* edge, the symmetric companion of `flowBodyWindow_advance`).  When the first
    item of the body window `[lo, hi)` is itself a bracketed structure — a flow sequence `[ … ]` or
    flow mapping `{ … }` whose opener sits at `k` (= the entry's first token, at depth `0`) — the
    recursion must *descend* into that bracket's interior and run the IH on it.  This lemma supplies the
    two facts the step needs at the descend edge: the matching closer's position `j`, and that the
    interior window `[k+1, j)` STILL satisfies the guard `G = FlowBodyWindow`.

    Like `flowBodyWindow_advance` it invokes its position lemma internally — here
    `flowBracketBalance_matching_close` (which scans forward for the first return to depth `0`, yielding
    the closer `j` with `flowBracketDelta tokens[j]!.val = -1`, the interior balance
    `flowBracketBalance tokens (k+1) j = 0`, and the matched-bracket *depth floor*
    `∀ i ∈ (k, j], flowBracketBalance tokens lo i ≥ 1`).  Both, like the opener premise
    `flowBracketDelta tokens[k]!.val = 1`, are phrased over the SHARED `flowBracketDelta`/balance stream
    — they name no collection-specific deliverable type — so this lemma, like its ADVANCE companion,
    serves BOTH axes unchanged (`[` discharges the opener premise by `flowSequenceStart`, `{` by
    `flowMappingStart`).

    The guard-transport then mirrors ADVANCE with one genuine asymmetry ([[ref-converse-forward-invariant-asymmetry]]):
    ADVANCE's tail re-based onto a depth-`0` prefix, so its `dyck` fell straight out of the outer `dyck`;
    here the interior sits a level DOWN (the opener pushes the running balance to `1`), so the inner
    `dyck` needs the strictly-stronger *floor* `≥ 1`, not the outer `≥ 0` — re-base each interior prefix
    to the outer origin (`balance lo i = 1 + balance (k+1) i`) and close by the floor.  The `WellTyped`
    field transports by the same `WellTyped_subrange` (the interior `[k+1, j) ⊆ [lo, hi)` is balanced and
    Dyck).  The interior's non-emptiness `k + 1 < j` (the empty bracket `[]`/`{}`, which has no
    `RecSeqBody`/`RecMapBody`) is DEFERRED to the caller, guarding the delivered `FlowBodyWindow` — the
    R285 peel, exactly as ADVANCE deferred "no trailing separator".

    Verified-but-unconsumed until the per-window step instantiates the combinator (R225): references no
    sorry site, frontier sorry count unchanged at 4. -/
theorem flowBodyWindow_descend (tokens : Array (Positioned YamlToken)) (lo k hi : Nat)
    (h_win : FlowBodyWindow tokens lo hi)
    (h_lo_k : lo ≤ k) (h_k_hi : k < hi)
    (h_k_depth : flowBracketBalance tokens lo k = 0)
    (h_k_open : flowBracketDelta tokens[k]!.val = 1) :
    ∃ j, k < j ∧ j < hi ∧ flowBracketDelta tokens[j]!.val = -1 ∧
      (k + 1 < j → FlowBodyWindow tokens (k + 1) j) := by
  obtain ⟨h_lo2, h_lo_hi, h_hi_sz2, h_hi_sz, h_bal, h_dyck, h_wt⟩ := h_win
  -- Position lemma: locate the matching closer `j` with interior balance and the depth floor.
  obtain ⟨j, hkj, hjhi, hjdelta, hinner, hfloor⟩ :=
    flowBracketBalance_matching_close tokens lo k hi h_lo_k h_k_hi (Nat.le_of_lt h_hi_sz)
      h_k_depth h_k_open h_bal h_dyck
  refine ⟨j, hkj, hjhi, hjdelta, ?_⟩
  intro h_ne
  -- Balance just after the opener is `1` (the descend offset that forces the stronger floor).
  have h_k_sz : k < tokens.size := by omega
  have h_k_len : k < tokens.toList.length := by rw [Array.length_toList]; exact h_k_sz
  have hkval : tokens[k]! = tokens.toList[k]'h_k_len := by
    rw [getElem!_pos tokens k h_k_sz, Array.getElem_toList]
  have h_single : flowBracketBalance tokens k (k + 1) = flowBracketDelta tokens[k]!.val := by
    rw [flowBracketBalance_single tokens k h_k_len, ← hkval]
  have h_k1 : flowBracketBalance tokens lo (k + 1) = 1 := by
    have hc := flowBracketBalance_compose tokens lo k (k + 1) h_lo_k (Nat.le_succ k)
    rw [h_k_depth, h_single, h_k_open] at hc; omega
  -- Inner `dyck`: re-base each interior prefix to the outer origin, then close by the floor `≥ 1`.
  have h_dyck' : ∀ i, k + 1 ≤ i → i ≤ j → flowBracketBalance tokens (k + 1) i ≥ 0 := by
    intro i hi1 hi2
    have hc := flowBracketBalance_compose tokens lo (k + 1) i (by omega) hi1
    rw [h_k1] at hc
    have hf := hfloor i (by omega) hi2
    omega
  refine ⟨by omega, h_ne, by omega, by omega, hinner, h_dyck', ?_⟩
  -- WellTyped on the interior via the balanced-subrange transporter (`[k+1, j) ⊆ [lo, hi)`).
  exact WellTyped_subrange tokens lo (k + 1) j hi (by omega) (Nat.le_of_lt h_ne)
    (Nat.le_of_lt hjhi) (Nat.le_of_lt h_hi_sz) h_wt hinner h_dyck'

/-- **The flow body-window CONTENT guard** (Phase J — the content-half companion of `FlowBodyWindow`,
    the substrate the head-shape grammar dispatches on).  `FlowBodyWindow` carries only the *bracket*
    facts (balance / dyck / WellTyped), and those are provably INSUFFICIENT to read the head shape: a
    `.flowEntry`- or `.placeholder`-headed window is still balanced + dyck + WellTyped, so "the head is
    a content-start token" is NOT derivable from `FlowBodyWindow` alone (the dyck floor only excludes a
    leading CLOSER, not a leading separator).  The missing content is exactly the three structural facts
    the outer span already supplies to `seqBodyProps_assemble` (`h_content_start` / `h_body_succ` /
    `h_fe_pattern`), here named as a window-parametric guard so the body recursion can carry them down
    each edge:

    * `headContentStart` — the window's HEAD `tokens[lo]` is a content-start token (scalar / `[` / `{`);
      this is what the head-shape bridge case-splits on to pick `recseqentry_classify`'s `h_head`
      disjunct.
    * `bodySucc` — a balanced-prefix end that is not a `.flowEntry` is an entry END (the body close, or a
      `.flowEntry` separator follows); the entry-extent successor.
    * `feContentStart` — every depth-`0` `.flowEntry` separator is followed by a content-start head (no
      empty entries); this is what re-establishes `headContentStart` on the ADVANCE tail.

    Like `FlowBodyWindow` it names **no collection-specific deliverable type** — only the shared
    `isFlowContentStart` / `flowBracketBalance` vocabulary — so it is the SHARED content guard for both
    axes (each flow body, seq or map, is content-headed segments separated by depth-`0` separators).  It
    is an *additive parallel type* ([[ref-additive-parallel-type-over-shared-edit]]): a NEW structure
    beside `FlowBodyWindow`, never an edit to it, so the two landed edge lemmas
    (`flowBodyWindow_advance` / `flowBodyWindow_descend`) are untouched. -/
structure FlowBodyContent (tokens : Array (Positioned YamlToken)) (lo hi : Nat) : Prop where
  headContentStart : isFlowContentStart tokens[lo]!.val
  bodySucc : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo (k + 1) = 0 →
    tokens[k]!.val ≠ .flowEntry →
    k + 1 = hi ∨ ∃ (_ : k + 1 < hi), tokens[k + 1]!.val = .flowEntry
  feContentStart : ∀ k, lo ≤ k → k < hi →
    tokens[k]!.val = .flowEntry →
    flowBracketBalance tokens lo k = 0 →
    k + 1 ≤ hi ∧ isFlowContentStart tokens[k + 1]!.val

/-- **ADVANCE content-preservation** (Phase J — the content guard's counterpart of
    `flowBodyWindow_advance`).  After the body recursion consumes the first entry at a depth-`0`
    `.flowEntry` separator `m`, the tail `[m+1, hi)` must STILL satisfy the content guard for the head
    shape to be readable there.  This lemma transports the whole `FlowBodyContent` guard from `[lo, hi)`
    to `[m+1, hi)`, and — unlike the DESCEND content edge, which sits a nesting level down and so cannot
    recover its interior heads from the outer ones (the genuinely recursive next brick) — the ADVANCE
    content edge is pure re-basing, exactly parallel to `flowBodyWindow_advance`'s `dyck` field:

    * `headContentStart` for the tail is `feContentStart` at the separator `m` (a depth-`0` `.flowEntry`
      is followed by a content-start head) — the field whose whole purpose is to re-seat the head one
      entry along.
    * `bodySucc` / `feContentStart` for the tail are the OUTER fields restricted to `[m+1, hi)`, their
      `flowBracketBalance (m+1) ·` premises re-based to the outer origin `lo` via the separator's
      delta-`0` (`balance lo (m+1) = 0`, so `balance lo p = balance (m+1) p`).

    Names no deliverable type, so it serves both axes' recursions unchanged. -/
theorem flowBodyContent_advance (tokens : Array (Positioned YamlToken)) (lo m hi : Nat)
    (h_content : FlowBodyContent tokens lo hi)
    (h_lo_m : lo ≤ m) (h_m1_hi : m + 1 < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_m_bal : flowBracketBalance tokens lo m = 0)
    (h_sep : tokens[m]!.val = .flowEntry) :
    FlowBodyContent tokens (m + 1) hi := by
  obtain ⟨h_head, h_succ, h_fe⟩ := h_content
  have h_m_hi : m < hi := by omega
  have h_m_sz : m < tokens.size := by omega
  have h_m_len : m < tokens.toList.length := by rw [Array.length_toList]; exact h_m_sz
  -- The separator has delta `0`, so the prefix `balance lo (m+1)` is still `0`.
  have hmval : tokens[m]! = tokens.toList[m]'h_m_len := by
    rw [getElem!_pos tokens m h_m_sz, Array.getElem_toList]
  have h_single : flowBracketBalance tokens m (m + 1) = flowBracketDelta tokens[m]!.val := by
    rw [flowBracketBalance_single tokens m h_m_len, ← hmval]
  have h_m1_bal : flowBracketBalance tokens lo (m + 1) = 0 := by
    have hc := flowBracketBalance_compose tokens lo m (m + 1) h_lo_m (Nat.le_succ m)
    have hd : flowBracketDelta tokens[m]!.val = 0 := by rw [h_sep]; rfl
    rw [h_m_bal, h_single, hd] at hc; omega
  -- Re-basing: for any `p ≥ m+1`, `balance lo p = balance (m+1) p` (since `balance lo (m+1) = 0`).
  have h_rebase : ∀ p, m + 1 ≤ p →
      flowBracketBalance tokens lo p = flowBracketBalance tokens (m + 1) p := by
    intro p hp
    have hc := flowBracketBalance_compose tokens lo (m + 1) p (by omega) hp
    rw [h_m1_bal] at hc; omega
  refine ⟨?_, ?_, ?_⟩
  · -- head content-start: the separator `m` is followed by a content-start (no empty entry).
    exact (h_fe m h_lo_m h_m_hi h_sep h_m_bal).2
  · -- bodySucc on the tail: re-base `balance (m+1) (k+1)` to the outer origin, then apply `h_succ`.
    intro k hk1 hk2 hbal hnfe
    have hbal' : flowBracketBalance tokens lo (k + 1) = 0 := by
      rw [h_rebase (k + 1) (by omega)]; exact hbal
    exact h_succ k (by omega) hk2 hbal' hnfe
  · -- feContentStart on the tail: re-base `balance (m+1) k`, then apply `h_fe`.
    intro k hk1 hk2 hfek hbal
    have hbal' : flowBracketBalance tokens lo k = 0 := by
      rw [h_rebase k (by omega)]; exact hbal
    exact h_fe k (by omega) hk2 hfek hbal'

/-- **The flow body-window DEEP content guard** (Phase J — the recursion-STABLE strengthening of
    `FlowBodyContent`, the content guard the body recursion's `G` actually carries).  R289's
    `FlowBodyContent` records the content facts at the *entry* level only — its `feContentStart` is gated
    by `flowBracketBalance tokens lo k = 0` (a depth-`0` separator) and it has no opener fact at all — and
    that is provably TOO WEAK to survive the DESCEND edge.  Descending into a nested bracket `[k .. j]` at
    the window head needs the interior `[k+1, j)`'s head `tokens[k+1]` to be content-start, but that head
    sits one nesting level DOWN (balance `1` relative to the outer origin), so NO depth-`0` outer fact
    reaches it: `headContentStart` speaks of `tokens[lo]`, and `feContentStart` is keyed on a `.flowEntry`
    at balance `0`, never an opener — exactly the "genuinely recursive, not re-basing" obstruction R289
    flagged for this edge.  This is [[ref-converse-forward-invariant-asymmetry]] recurring on the content
    guard: the descend edge needs a strictly-stronger invariant than advance — precisely as the bracket
    guard's `dyck` needed the `≥ 1` floor for descend where advance used `≥ 0` (R288).

    The fix carries the content facts at ALL depths (balance-condition-FREE), so the guard is a pure
    RESTRICTION of itself on every sub-window:

    * `headContentStart` — the window head `tokens[lo]` is content-start (seeded at the root, re-derived
      at each child from the parent's `openerContentStart` / `feContentStart`).
    * `openerContentStart` — after EVERY opener strictly inside the window, the next token is content-start
      (the all-depth fact the descend edge reads the child head off — the field R289's guard lacked).
    * `feContentStart` — after EVERY separator strictly inside the window, the next token is content-start
      (the all-depth, balance-free strengthening of R289's depth-`0` field).

    Because the opener/separator fields are balance-free, BOTH recursion edges are pure restrictions of
    the quantifiers (no re-basing — contrast `flowBodyContent_advance`, whose depth-`0` field forced the
    separator re-base): `flowBodyContentDeep_descend` (below) restricts to `[k+1, j)` and reads the child
    head off the parent's `openerContentStart` at the opener `k`; the advance twin restricts to
    `[m+1, hi)` and reads the child head off `feContentStart` at the separator `m`.  R289's
    `FlowBodyContent` is the entry-level PROJECTION of this guard (its depth-`0` `feContentStart` is this
    field specialized to `balance lo k = 0`), kept for the head-shape dispatch / assemble that consume the
    depth-`0` shape; this deep guard is what `G` threads through the recursion so the projection is
    available at every window.  Like its companions it names no deliverable type, so it is the SHARED deep
    content guard for both axes.  Additive parallel guard ([[ref-additive-parallel-type-over-shared-edit]])
    beside `FlowBodyContent` / `FlowBodyWindow`, never an edit to them. -/
structure FlowBodyContentDeep (tokens : Array (Positioned YamlToken)) (lo hi : Nat) : Prop where
  headContentStart : isFlowContentStart tokens[lo]!.val
  openerContentStart : ∀ k, lo ≤ k → k + 1 < hi →
    flowBracketDelta tokens[k]!.val = 1 →
    isFlowContentStart tokens[k + 1]!.val
  feContentStart : ∀ k, lo ≤ k → k + 1 < hi →
    tokens[k]!.val = .flowEntry →
    isFlowContentStart tokens[k + 1]!.val

/-- **DESCEND deep-content-preservation** (Phase J — the genuinely-recursive content edge, the brick
    R289 isolated and the ONE the 137th-revision map flagged next).  When the body recursion descends
    into a nested bracket whose opener sits at `k` (depth `0`) and whose matching close is `j`, the
    interior `[k+1, j)` must re-establish the content guard for the IH to fire there.  Unlike R289's
    depth-`0` `FlowBodyContent` (whose descend edge is *unprovable* — the interior head sits a nesting
    level below the outer depth-`0` facts), `FlowBodyContentDeep`'s all-depth fields make this a pure
    RESTRICTION: the child head `tokens[k+1]` is content-start by the parent's `openerContentStart` at the
    opener `k`, and the child's opener/separator fields are the parent's restricted to `[k+1, j)`.  No
    balance re-basing, no grammar — the descend-strength formulation pays off as triviality, the
    [[ref-converse-forward-invariant-asymmetry]] dividend (strengthen the invariant to the descend edge's
    needs once, and the edge falls out).  The companion of `flowBodyWindow_descend`: that locates `j` and
    delivers the bracket guard on `[k+1, j)`; this delivers the content guard on the same `j`, given the
    same opener (`flowBracketDelta tokens[k] = 1`) and interior non-emptiness (`k+1 < j`, the R285 peel).
    Names no deliverable type, so it serves both axes. -/
theorem flowBodyContentDeep_descend (tokens : Array (Positioned YamlToken)) (lo k j hi : Nat)
    (h_deep : FlowBodyContentDeep tokens lo hi)
    (h_lo_k : lo ≤ k) (h_k_open : flowBracketDelta tokens[k]!.val = 1)
    (h_kj : k + 1 < j) (h_j_hi : j ≤ hi) :
    FlowBodyContentDeep tokens (k + 1) j := by
  obtain ⟨_h_head, h_op, h_fe⟩ := h_deep
  refine ⟨?_, ?_, ?_⟩
  · -- child head `tokens[k+1]` content-start: the parent's opener fact at `k` (`k+1 < j ≤ hi`).
    exact h_op k h_lo_k (by omega) h_k_open
  · -- child openerContentStart: the parent's, restricted to `[k+1, j) ⊆ [lo, hi)`.
    intro k' hk1 hk2 hopen
    exact h_op k' (by omega) (by omega) hopen
  · -- child feContentStart: the parent's, restricted to `[k+1, j) ⊆ [lo, hi)`.
    intro k' hk1 hk2 hfe
    exact h_fe k' (by omega) (by omega) hfe

/-- **ADVANCE deep-content-preservation** (Phase J — the trivial ADVANCE twin of
    `flowBodyContentDeep_descend`, the last remaining content-guard edge per the 138th-revision map).
    When the body recursion consumes the first entry at a `.flowEntry` separator `m` and advances to the
    tail `[m+1, hi)`, that tail must re-establish the deep content guard for the IH to fire there.  Because
    `FlowBodyContentDeep`'s opener/separator fields are balance-FREE, this is a pure RESTRICTION — the
    mirror image of the descend edge with `feContentStart` standing in for `openerContentStart`:

    * the child head `tokens[m+1]` is content-start by the parent's `feContentStart` at the separator `m`
      (every separator strictly inside is followed by content — the field whose purpose is to re-seat the
      head one entry along), and
    * the child's opener/separator fields are the parent's restricted to `[m+1, hi) ⊆ [lo, hi)`.

    No balance re-basing and no array-size side conditions — contrast R289's `flowBodyContent_advance`,
    whose depth-`0` `feContentStart` forced a `flowBracketBalance lo (m+1) = 0` re-base of every premise;
    the all-depth formulation pays the descend asymmetry off on BOTH edges at once
    ([[ref-converse-forward-invariant-asymmetry]] / [[ref-easy-edge-guard-fails-hard-edge]]).  With this
    twin landed, the deep content guard threads across both recursion edges, so the body recursion's
    `G := fun lo hi => FlowBodyWindow tokens lo hi ∧ FlowBodyContentDeep tokens lo hi` is now preserved on
    every edge.  Names no deliverable type, so it serves both axes' recursions unchanged. -/
theorem flowBodyContentDeep_advance (tokens : Array (Positioned YamlToken)) (lo m hi : Nat)
    (h_deep : FlowBodyContentDeep tokens lo hi)
    (h_lo_m : lo ≤ m) (h_sep : tokens[m]!.val = .flowEntry) (h_m1_hi : m + 1 < hi) :
    FlowBodyContentDeep tokens (m + 1) hi := by
  obtain ⟨_h_head, h_op, h_fe⟩ := h_deep
  refine ⟨?_, ?_, ?_⟩
  · -- child head `tokens[m+1]` content-start: the parent's separator fact at `m` (`m+1 < hi`).
    exact h_fe m h_lo_m h_m1_hi h_sep
  · -- child openerContentStart: the parent's, restricted to `[m+1, hi) ⊆ [lo, hi)`.
    intro k' hk1 hk2 hopen
    exact h_op k' (by omega) (by omega) hopen
  · -- child feContentStart: the parent's, restricted to `[m+1, hi) ⊆ [lo, hi)`.
    intro k' hk1 hk2 hfe
    exact h_fe k' (by omega) (by omega) hfe

/-- **`FlowBodyContent` assembler from the threaded deep guard** (Phase J — sub-brick (i'-a), the
    `bodySucc`-provenance factoring).  Every head-shape dispatch branch and both bracket oracles consume
    `FlowBodyContent tokens lo hi`, but the body recursion's combined guard only threads
    `G = FlowBodyWindow ∧ FlowBodyContentDeep` (R290's deep content guard, the recursion-STABLE one).
    To instantiate the dispatch inside the per-window `step` we must PRODUCE `FlowBodyContent` from `G`.
    This assembler does the producible part and names the irreducible residual exactly
    ([[ref-parametric-assembler-extraction]]: split a deferred deliverable into *assemble* (done here)
    vs *produce-primitives* (the named hypotheses)):

    * `headContentStart` — a FREE projection ([[ref-conjunct-of-projection-is-free-field]]): the
      `FlowBodyContent` and `FlowBodyContentDeep` head fields are the SAME proposition
      (`isFlowContentStart tokens[lo]!.val`), so `h_deep.headContentStart` types directly.
    * `feContentStart` INTERIOR (`k + 1 < hi`) — also a projection: the deep guard's all-depth,
      balance-free `feContentStart` subsumes the depth-`0` field's interior (drop the unused
      `balance lo k = 0` premise; the `k + 1 ≤ hi` conjunct is `omega` from `k < hi`).

    What the deep guard provably CANNOT project — the residual, the "content substrate `WellTyped` does
    not encode" — is two SEQ-specific comma-placement facts, taken as explicit hypotheses:

    * `h_bodySucc` — **values are comma-separated**: a depth-`0` non-`.flowEntry` position whose prefix
      returns to `0` is an entry END (window close or immediately-following `.flowEntry`).  Genuinely
      missing from `G`: the bracket/balance substrate accepts `[a b]` (adjacent scalars, no comma).
    * `h_noTrailingSep` — **no trailing comma**: the `feContentStart` BOUNDARY at `k + 1 = hi` (a
      depth-`0` `.flowEntry` at `hi - 1`).  Independent of `bodySucc` (it speaks to a separator
      position, where `bodySucc`'s non-separator premise fails) and unreachable from the deep guard
      (whose `feContentStart` is gated `k + 1 < hi`); discharged at the root from `emitList`'s
      no-trailing-comma emission, vacuous premise.

    So this assembler collapses (i')'s residual from "produce `FlowBodyContent` at every window" to
    "produce these two named separator facts at every window" — the genuine remaining grammar content,
    now precisely scoped.  Names no deliverable type, so it serves both axes' window producers. -/
theorem flowBodyContent_of_deep (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_deep : FlowBodyContentDeep tokens lo hi)
    (h_bodySucc : ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo (k + 1) = 0 →
        tokens[k]!.val ≠ .flowEntry →
        k + 1 = hi ∨ ∃ (_ : k + 1 < hi), tokens[k + 1]!.val = .flowEntry)
    (h_noTrailingSep : ∀ k, lo ≤ k → k + 1 = hi →
        tokens[k]!.val = .flowEntry →
        flowBracketBalance tokens lo k = 0 →
        isFlowContentStart tokens[k + 1]!.val) :
    FlowBodyContent tokens lo hi := by
  refine ⟨h_deep.headContentStart, h_bodySucc, ?_⟩
  intro k hk1 hk2 hfe hbal
  refine ⟨by omega, ?_⟩
  rcases Nat.lt_or_ge (k + 1) hi with h | h
  · -- interior separator: the deep guard's all-depth `feContentStart` projects it.
    exact h_deep.feContentStart k hk1 h hfe
  · -- boundary separator `k + 1 = hi`: the no-trailing-comma residual.
    exact h_noTrailingSep k hk1 (by omega) hfe hbal

/-- **`bodySucc` ROOT-SEED bridge** (Phase J — sub-brick (i'-b), the CERTAIN half of the seq separator
    facts at the root window, and the producer's first landable brick per
    [[ref-universal-producer-root-seed-first]]).  `emitList_body_filtered_characterization` Part 6
    delivers EXACTLY the `bodySucc` separator fact — "a depth-`0` non-`.flowEntry` balanced-prefix end is
    an entry END (window close, or immediately followed by a `.flowEntry`)" — over the body window
    `[lo, T.size)` of the filtered token array `T`, but stated with bounds-checked indexing (`T[k]'h`,
    `T[k+1]'h'`).  `flowBodyContent_of_deep`'s `h_bodySucc` parameter wants the SAME fact with panic
    indexing (`T[k]!`, `T[k+1]!`).  This is the pure index-notation bridge between the two (`getElem!_pos`
    on the hypothesis and the existential witness), so the root assembly can feed Part 6 straight into the
    `FlowBodyContent` assembler with no re-derivation.

    This pins the BASE case only.  The genuinely-open part of (i'-b) is provenance at DESCENDED windows,
    which this does NOT touch and which — per R296 — does NOT factor through any LOCAL separator carrier:
    `bodySucc` has no all-depth, balance-free form (contrast `FlowBodyContentDeep`'s
    `openerContentStart` / `feContentStart`, whose balance-freedom makes both recursion edges pure subset
    restrictions), because a child window's depth-`0` is the parent's depth-`1`, where the parent's
    `bodySucc` is silent — and inside a nested `{ … }` the fact is outright FALSE (a key is followed by
    `.value`, not a separator).  So the descended facts need a bracket-TYPE context the current guards
    lack; they are not derivable by restriction from a parent `bodySucc`.  Names no deliverable type, so
    it serves both axes' root seeds. -/
theorem flowBodyContent_bodySucc_of_part6 (T : Array (Positioned YamlToken)) (lo : Nat)
    (h_part6 : ∀ (k : Nat), lo ≤ k → (h_hi : k < T.size) →
        flowBracketBalance T lo (k + 1) = 0 →
        (T[k]'h_hi).val ≠ .flowEntry →
        k + 1 = T.size ∨ ∃ (h' : k + 1 < T.size), (T[k + 1]'h').val = .flowEntry) :
    ∀ (k : Nat), lo ≤ k → k < T.size →
        flowBracketBalance T lo (k + 1) = 0 →
        T[k]!.val ≠ .flowEntry →
        k + 1 = T.size ∨ ∃ (_ : k + 1 < T.size), T[k + 1]!.val = .flowEntry := by
  intro k hk1 hk2 hbal hnfe
  rw [getElem!_pos T k hk2] at hnfe
  rcases h_part6 k hk1 hk2 hbal hnfe with h | ⟨h', heq⟩
  · exact Or.inl h
  · refine Or.inr ⟨h', ?_⟩
    rw [getElem!_pos T (k + 1) h']
    exact heq

/-- **Nested-sequence head-dispatch oracle from the IH** (Phase J — the head-shape dispatch's recursive
    crux, the first GRAMMAR brick after the guard-threading skeleton closed: the producer-guarded
    `RecSeqBody` oracle for the nested `[ … ]` branch, built from the `windowWidth_strongRecOn`
    inductive hypothesis gated by the two descend edges).  When the body window's head `tokens[lo]` is a
    flow-sequence opener with a non-empty interior, the nested-sequence disjunct of
    `recseqentry_classify` (and its head-derived form `recseqentry_seqbracket_located`) needs, for the
    matching close `j`, the recursive interior body `RecSeqBody ((take j).drop (lo+1))` and the trailing
    separator `j + 1 = hi ∨ tokens[j+1] = .flowEntry`.  Both depend on `j`, which is not named until the
    close-locator runs inside the consumer, so this is exactly the producer-guarded quantifier shape
    ([[ref-producer-guarded-quantifier]]): a universal over `j` guarded by the locator's output
    predicate (`lo < j`, `j < hi`, the close token, the inner balance, the strict-positivity floor).

    This lemma DISCHARGES that oracle from the combinator's IH.  Given the guarded `j`, it reconstructs
    both guards on the interior `[lo+1, j)` directly from the locator facts — no re-location, so no
    matching-close uniqueness obligation: the bracket guard `FlowBodyWindow (lo+1) j` is built in place
    (`balance` and the `WellTyped` subrange from the floor and the outer guard, the inner `dyck` re-based
    by the opener prefix `balance lo (lo+1) = 1`), and the deep content guard `FlowBodyContentDeep
    (lo+1) j` falls out of `flowBodyContentDeep_descend` at the opener `lo` (the descend dividend).  The
    IH on the strictly-narrower interior then yields the `RecSeqBody`.  The interior non-emptiness
    `lo+1 < j` the descend edge needs is FREE from the deep guard's `openerContentStart` at `lo` (the
    head after the opener is content-start, hence not the closer `]`), and the trailing separator comes
    from the content guard's `bodySucc` at the close `j` (`balance lo (j+1) = 0`, `tokens[j] = ] ≠
    .flowEntry`).

    Names `RecSeqBody`, so it is seq-specific and re-splits across the map axis
    ([[ref-entry-boundary-input-shape-split]]); the map mirror is the pair's two sub-block oracles.
    Verified-but-unconsumed (R225): references no sorry site, frontier sorry count unchanged at 4. -/
theorem recseqentry_seqbracket_oracle (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_window : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeep tokens lo hi)
    (h_content : FlowBodyContent tokens lo hi)
    (h_open : tokens[lo]!.val = .flowSequenceStart)
    (Q : Nat → Prop) (h_q_succ : Q (lo + 1))
    (h_ih : ∀ lo' hi', hi' - lo' < hi - lo →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' → Q lo' →
        tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo')) :
    ∀ j, lo < j → j < hi → tokens[j]!.val = .flowSequenceEnd →
        flowBracketBalance tokens (lo + 1) j = 0 →
        (∀ i, lo < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) →
        RecSeqBody ((tokens.toList.take j).drop (lo + 1)) ∧
        (j + 1 = hi ∨ tokens[j + 1]!.val = .flowEntry) := by
  obtain ⟨h_lo2, h_lo_hi, h_hi_le, h_hi_sz, h_bal, h_dyck, h_wt⟩ := h_window
  -- Opener delta and the depth-`1` prefix `balance lo (lo+1) = 1` (the descend offset).
  have h_lo_sz : lo < tokens.size := by omega
  have h_lo_len : lo < tokens.toList.length := by rw [Array.length_toList]; exact h_lo_sz
  have h_open_delta : flowBracketDelta tokens[lo]!.val = 1 := by
    rw [h_open]; exact flowBracketDelta_flowSequenceStart
  have h_lo_val : tokens[lo]! = tokens.toList[lo]'h_lo_len := by
    rw [getElem!_pos tokens lo h_lo_sz, Array.getElem_toList]
  have h_single : flowBracketBalance tokens lo (lo + 1) = flowBracketDelta tokens[lo]!.val := by
    rw [flowBracketBalance_single tokens lo h_lo_len, ← h_lo_val]
  have h_lo1_bal : flowBracketBalance tokens lo (lo + 1) = 1 := by rw [h_single, h_open_delta]
  intro j h_lo_j h_j_hi h_close h_inner h_floor
  -- Interior non-emptiness: the deep guard's opener fact gives `tokens[lo+1]` content-start (≠ `]`).
  have h_lo1_hi : lo + 1 < hi := by omega
  have h_head_cs : isFlowContentStart tokens[lo + 1]!.val :=
    h_deep.openerContentStart lo (Nat.le_refl lo) h_lo1_hi h_open_delta
  have h_lo1_ne : tokens[lo + 1]!.val ≠ .flowSequenceEnd := by
    intro h; rw [h] at h_head_cs; simp [isFlowContentStart] at h_head_cs
  have h_lo1_j : lo + 1 < j := by
    rcases Nat.lt_or_ge (lo + 1) j with h | h
    · exact h
    · have h_eq : j = lo + 1 := by omega
      rw [h_eq] at h_close; exact absurd h_close h_lo1_ne
  -- `balance lo j = 1` (opener prefix `1` + balanced interior `0`).
  have h_lo_j_bal : flowBracketBalance tokens lo j = 1 := by
    have hc := flowBracketBalance_compose tokens lo (lo + 1) j (by omega) (by omega)
    rw [h_lo1_bal, h_inner] at hc; omega
  -- Reconstruct both guards on the interior `[lo+1, j)`; the IH then produces its `RecSeqBody`.
  have h_dyck' : ∀ i, lo + 1 ≤ i → i ≤ j → flowBracketBalance tokens (lo + 1) i ≥ 0 := by
    intro i hi1 hi2
    have hc := flowBracketBalance_compose tokens lo (lo + 1) i (by omega) hi1
    rw [h_lo1_bal] at hc
    have hf := h_floor i (by omega) hi2
    omega
  have h_win' : FlowBodyWindow tokens (lo + 1) j :=
    ⟨by omega, h_lo1_j, by omega, by omega, h_inner, h_dyck',
      WellTyped_subrange tokens lo (lo + 1) j hi (by omega) (by omega) (by omega)
        (Nat.le_of_lt h_hi_sz) h_wt h_inner h_dyck'⟩
  have h_deep' : FlowBodyContentDeep tokens (lo + 1) j :=
    flowBodyContentDeep_descend tokens lo lo j hi h_deep (Nat.le_refl lo) h_open_delta h_lo1_j
      (Nat.le_of_lt h_j_hi)
  have h_rec : RecSeqBody ((tokens.toList.take j).drop (lo + 1)) :=
    h_ih (lo + 1) j (by omega) h_win' h_deep' h_q_succ h_close
  -- Trailing-separator successor at the close `j` from the content guard's `bodySucc`.
  have h_j_sz : j < tokens.size := by omega
  have h_j_len : j < tokens.toList.length := by rw [Array.length_toList]; exact h_j_sz
  have h_close_val : tokens[j]! = tokens.toList[j]'h_j_len := by
    rw [getElem!_pos tokens j h_j_sz, Array.getElem_toList]
  have h_close_delta : flowBracketDelta tokens[j]!.val = -1 := by
    rw [h_close]; exact flowBracketDelta_flowSequenceEnd
  have h_single_j : flowBracketBalance tokens j (j + 1) = flowBracketDelta tokens[j]!.val := by
    rw [flowBracketBalance_single tokens j h_j_len, ← h_close_val]
  have h_j1_bal : flowBracketBalance tokens lo (j + 1) = 0 := by
    have hc := flowBracketBalance_compose tokens lo j (j + 1) (by omega) (Nat.le_succ j)
    rw [h_lo_j_bal, h_single_j, h_close_delta] at hc; omega
  have h_j_ne_fe : tokens[j]!.val ≠ .flowEntry := by rw [h_close]; decide
  refine ⟨h_rec, ?_⟩
  rcases h_content.bodySucc j (by omega) h_j_hi h_j1_bal h_j_ne_fe with h | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h

/-- **Nested-mapping head-dispatch oracle** (Phase J — the head-shape dispatch's NEAR-LEAF bracket
    branch, the `{ … }` mirror of `recseqentry_seqbracket_oracle`).  When the body window's head
    `tokens[lo]` is a flow-mapping opener, the nested-mapping disjunct of `recseqentry_classify` (and its
    head-derived form `recseqentry_mapbracket_located`) needs, for the matching close `j`, the interior
    `WellBracketed ((take j).drop (lo+1))` and the trailing separator `j + 1 = hi ∨ tokens[j+1] =
    .flowEntry` — both `j`-dependent, so this is again the producer-guarded quantifier shape
    ([[ref-producer-guarded-quantifier]]): a universal over `j` guarded by the locator's output predicate.

    The mirror is *asymmetric* exactly at the R244 storage fact, and the asymmetry SHRINKS this branch
    rather than thickening it.  Where the seq branch's interior is a recursive `RecSeqBody` — forcing the
    `windowWidth_strongRecOn` IH and the in-place reconstruction of both descend guards
    ([[ref-reconstruct-in-place-over-relocate]]) — `RecSeqEntry.map` stores only the interior
    `WellBracketed` (R244: a nested mapping is a NEAR-leaf, its key/value recursion deferred to the
    separate map axis).  `WellBracketed` is pure prefix-balance combinatorics, decidable from the window's
    own facts: it needs **no IH, no descend guard, and not even the interior non-emptiness** the seq branch
    derived from `FlowBodyContentDeep`.  So this oracle drops both `h_deep` and `h_ih` from the seq
    signature — it is discharged entirely from `FlowBodyWindow` (for the opener/close size bounds) and
    `FlowBodyContent` (for the separator successor), the head dispatch's two standing guards.

    Construction: the interior `WellBracketed` is read off the `flowBracketBalance`↔`pbalance` bridge
    (`flowBracketBalance_eq_pbalance`) — its balance `0` is the oracle's `h_inner` directly, and its every
    prefix balance `≥ 0` is the interior floor `flowBracketBalance (lo+1) · ≥ 0`, peeled from the locator's
    strict-positivity invariant `≥ 1` by the opener prefix `balance lo (lo+1) = 1` (the same floor the seq
    branch built, reused here without the descend).  The trailing separator comes from the content guard's
    `bodySucc` at the close `j` (`balance lo (j+1) = 0`, `tokens[j] = } ≠ .flowEntry`), verbatim from the
    seq branch — confirming (cf. `recseqentry_mapbracket_located`) the separator's `j`-dependence is what
    forces the producer-guarded shape on BOTH bracket branches, independently of whether the interior body
    is recursive.  Names `WellBracketed`, axis-agnostic, but is invoked only on the seq dispatch's map
    sub-branch.  Verified-but-unconsumed (R225): references no sorry site, frontier sorry count unchanged
    at 4. -/
theorem recseqentry_mapbracket_oracle (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_window : FlowBodyWindow tokens lo hi)
    (h_content : FlowBodyContent tokens lo hi)
    (h_open : tokens[lo]!.val = .flowMappingStart) :
    ∀ j, lo < j → j < hi → tokens[j]!.val = .flowMappingEnd →
        flowBracketBalance tokens (lo + 1) j = 0 →
        (∀ i, lo < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) →
        WellBracketed ((tokens.toList.take j).drop (lo + 1)) ∧
        (j + 1 = hi ∨ tokens[j + 1]!.val = .flowEntry) := by
  obtain ⟨h_lo2, h_lo_hi, h_hi_le, h_hi_sz, h_bal, h_dyck, h_wt⟩ := h_window
  -- Opener delta and the depth-`1` prefix `balance lo (lo+1) = 1` (the descend offset).
  have h_lo_sz : lo < tokens.size := by omega
  have h_lo_len : lo < tokens.toList.length := by rw [Array.length_toList]; exact h_lo_sz
  have h_open_delta : flowBracketDelta tokens[lo]!.val = 1 := by
    rw [h_open]; exact flowBracketDelta_flowMappingStart
  have h_lo_val : tokens[lo]! = tokens.toList[lo]'h_lo_len := by
    rw [getElem!_pos tokens lo h_lo_sz, Array.getElem_toList]
  have h_single : flowBracketBalance tokens lo (lo + 1) = flowBracketDelta tokens[lo]!.val := by
    rw [flowBracketBalance_single tokens lo h_lo_len, ← h_lo_val]
  have h_lo1_bal : flowBracketBalance tokens lo (lo + 1) = 1 := by rw [h_single, h_open_delta]
  intro j h_lo_j h_j_hi h_close h_inner h_floor
  -- Interior floor on `[lo+1, j)`: the strict-positivity invariant `≥ 1` minus the opener prefix `1`.
  have h_dyck' : ∀ i, lo + 1 ≤ i → i ≤ j → flowBracketBalance tokens (lo + 1) i ≥ 0 := by
    intro i hi1 hi2
    have hc := flowBracketBalance_compose tokens lo (lo + 1) i (by omega) hi1
    rw [h_lo1_bal] at hc
    have hf := h_floor i (by omega) hi2
    omega
  -- `WellBracketed` of the interior: balance `0` (`h_inner`) and every prefix `≥ 0` (`h_dyck'`), both
  -- transported through the `flowBracketBalance`↔`pbalance` bridge.  No IH — pure prefix-balance algebra.
  have h_wb : WellBracketed ((tokens.toList.take j).drop (lo + 1)) := by
    rw [List.drop_take]
    refine ⟨?_, ?_⟩
    · rw [← flowBracketBalance_eq_pbalance tokens (lo + 1) j (by omega)]; exact h_inner
    · intro i
      rw [List.take_take]
      have hb : pbalance ((tokens.toList.drop (lo + 1)).take (min i (j - (lo + 1))))
          = flowBracketBalance tokens (lo + 1) ((lo + 1) + min i (j - (lo + 1))) := by
        rw [flowBracketBalance_eq_pbalance tokens (lo + 1) ((lo + 1) + min i (j - (lo + 1))) (by omega),
            show (lo + 1) + min i (j - (lo + 1)) - (lo + 1) = min i (j - (lo + 1)) from by omega]
      rw [hb]
      exact h_dyck' ((lo + 1) + min i (j - (lo + 1))) (by omega) (by omega)
  -- `balance lo j = 1` (opener prefix `1` + balanced interior `0`), feeding the trailing-separator probe.
  have h_lo_j_bal : flowBracketBalance tokens lo j = 1 := by
    have hc := flowBracketBalance_compose tokens lo (lo + 1) j (by omega) (by omega)
    rw [h_lo1_bal, h_inner] at hc; omega
  -- Trailing-separator successor at the close `j` from the content guard's `bodySucc`.
  have h_j_sz : j < tokens.size := by omega
  have h_j_len : j < tokens.toList.length := by rw [Array.length_toList]; exact h_j_sz
  have h_close_val : tokens[j]! = tokens.toList[j]'h_j_len := by
    rw [getElem!_pos tokens j h_j_sz, Array.getElem_toList]
  have h_close_delta : flowBracketDelta tokens[j]!.val = -1 := by
    rw [h_close]; exact flowBracketDelta_flowMappingEnd
  have h_single_j : flowBracketBalance tokens j (j + 1) = flowBracketDelta tokens[j]!.val := by
    rw [flowBracketBalance_single tokens j h_j_len, ← h_close_val]
  have h_j1_bal : flowBracketBalance tokens lo (j + 1) = 0 := by
    have hc := flowBracketBalance_compose tokens lo j (j + 1) (by omega) (Nat.le_succ j)
    rw [h_lo_j_bal, h_single_j, h_close_delta] at hc; omega
  have h_j_ne_fe : tokens[j]!.val ≠ .flowEntry := by rw [h_close]; decide
  refine ⟨h_wb, ?_⟩
  rcases h_content.bodySucc j (by omega) h_j_hi h_j1_bal h_j_ne_fe with h | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h

/-- **Scalar-leaf entry window** (Phase J — the analytical entry-boundary location's *shape side*,
    seq, base case).  Once `firstEntryBoundary` (the input side) has pinned the split point `m`, the
    shape side classifies the first item `[lo, m)` into a `RecSeqEntry` — and `RecSeqEntry` has four
    constructors, three of which (`seqEmpty`/`seq`/`map`) wrap a bracketed sub-window and the fourth,
    `scalar`, is the lone NON-recursive leaf: a single scalar token is one entry.  This lemma is that
    leaf's positional lift — given a scalar at the window head `tokens[lo]`, the one-token window
    `(tokens.toList.take (lo + 1)).drop lo` is a `RecSeqEntry.scalar`.  It is where the locate
    recursion bottoms out (no matching-close, no descent, `m = lo + 1`), so it lands first among the
    shape-side bricks.

    The shape side is the *family of per-constructor window-lifts*, and the recursive `.seq`
    constructor's lift is ALREADY supplied by the BUILD structural move `located_entry_of_recseqbody`
    (it assembles `RecSeqEntry.seq` from the inner-window `RecSeqBody`).  So the shape side's
    genuinely-new work is the *non-`.seq`* constructors — and of those `scalar` is the leaf, ahead of
    `seqEmpty` (empty `[ ]`) and `map` (nested mapping, interior bottoming at `WellBracketed`).

    This is where the seq/map mirror RE-SPLITS (contrast `firstEntryBoundary`, written once over the
    shared token stream): the map body's first item is a whole key/value PAIR (`.key … .value …`, a
    `RecMapPair`), so its leaf is the scalar-key/scalar-value pair — a four-token shape, not this
    one-token singleton.  Hence no map mirror of *this* lemma; the map shape side is a separate brick.

    Proof: the window-singleton identity `(take (lo+1)).drop lo = [tokens.toList[lo]]`
    (`List.getElem_cons_drop` + `List.getElem_take`, the trailing `drop (lo+1)` killed by
    `List.drop_eq_nil_of_le` on the `take`-length), then `RecSeqEntry.scalar` with the head value
    transported from `tokens[lo]!` via `getElem!_pos`/`Array.getElem_toList`.  Verified-but-unconsumed:
    references no sorry site, frontier sorry count unchanged; axiom-clean `[propext, Quot.sound]`. -/
theorem recseqentry_scalar_window (tokens : Array (Positioned YamlToken)) (lo : Nat)
    (h_lo_sz : lo < tokens.size)
    (h_scalar : ∃ c s, tokens[lo]!.val = .scalar c s) :
    RecSeqEntry ((tokens.toList.take (lo + 1)).drop lo) := by
  have h_lo_len : lo < tokens.toList.length := by rw [Array.length_toList]; exact h_lo_sz
  have hlen : lo < (tokens.toList.take (lo + 1)).length := by
    rw [List.length_take]; omega
  have h_drop_nil : (tokens.toList.take (lo + 1)).drop (lo + 1) = [] := by
    apply List.drop_eq_nil_of_le
    rw [List.length_take]; omega
  have h_win : (tokens.toList.take (lo + 1)).drop lo = [tokens.toList[lo]'h_lo_len] := by
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take, h_drop_nil] at h
    exact h
  rw [h_win]
  obtain ⟨c, s, hcs⟩ := h_scalar
  have h_val : (tokens.toList[lo]'h_lo_len).val = .scalar c s := by
    have hb : tokens[lo]! = tokens.toList[lo]'h_lo_len := by
      rw [getElem!_pos tokens lo h_lo_sz, Array.getElem_toList]
    rw [← hb]; exact hcs
  exact RecSeqEntry.scalar _ c s h_val

/-- **Empty-sequence entry window** (Phase J — the entry-boundary location's *shape side*, seq, the
    second leaf).  The next shape-side constructor-lift after `recseqentry_scalar_window`: the empty
    flow-sequence `[ ]`.  `RecSeqEntry.seqEmpty` produces `RecSeqEntry (op :: ([] ++ [cl]))` — the
    two-token window `[op, cl]` with no interior — so given an opener `tokens[lo] = .flowSequenceStart`
    immediately followed by a closer `tokens[lo+1] = .flowSequenceEnd`, the window `[lo, lo+2)`,
    i.e. `(tokens.toList.take (lo + 2)).drop lo`, is a `RecSeqEntry.seqEmpty`.  Here the split point is
    `m = lo + 2` (the matching close is the very next token: an empty bracket has depth returning to `0`
    one step in), so like the scalar leaf it is NON-recursive — no `RecSeqBody` interior to descend
    into, the empty interior carried positionally by the constructor.  It joins `scalar` as the second
    of the shape side's two *leaf* constructor-lifts (the non-recursive `RecSeqEntry` constructors);
    the remaining `map` is a near-leaf (its interior bottoms at `WellBracketed`, not a `RecSeqBody`),
    and the recursive `.seq` lift is already the BUILD move `located_entry_of_recseqbody`.

    Proof: the two-token window identity `(take (lo+2)).drop lo = [tokens.toList[lo], tokens.toList[lo+1]]`
    — the one-token `List.getElem_cons_drop` chain of `recseqentry_scalar_window` applied *twice*
    (peel `[lo]`, then `[lo+1]`, the trailing `drop (lo+2)` killed by `List.drop_eq_nil_of_le`), each
    index simplified through the `take` by `List.getElem_take` — then `RecSeqEntry.seqEmpty` (whose
    `op :: ([] ++ [cl])` index is defeq to the two-element list), with both head values transported
    from `tokens[lo]!`/`tokens[lo+1]!` via `getElem!_pos`/`Array.getElem_toList`.  Verified-but-
    unconsumed: references no sorry site, frontier sorry count unchanged; axiom-clean
    `[propext, Quot.sound]`. -/
theorem recseqentry_seqempty_window (tokens : Array (Positioned YamlToken)) (lo : Nat)
    (h_lo1_sz : lo + 1 < tokens.size)
    (h_open : tokens[lo]!.val = .flowSequenceStart)
    (h_close : tokens[lo + 1]!.val = .flowSequenceEnd) :
    RecSeqEntry ((tokens.toList.take (lo + 2)).drop lo) := by
  have h_lo_sz : lo < tokens.size := by omega
  have h_lo_len : lo < tokens.toList.length := by rw [Array.length_toList]; exact h_lo_sz
  have h_lo1_len : lo + 1 < tokens.toList.length := by rw [Array.length_toList]; exact h_lo1_sz
  have hlen0 : lo < (tokens.toList.take (lo + 2)).length := by rw [List.length_take]; omega
  have hlen1 : lo + 1 < (tokens.toList.take (lo + 2)).length := by rw [List.length_take]; omega
  have h_drop_nil : (tokens.toList.take (lo + 2)).drop (lo + 2) = [] := by
    apply List.drop_eq_nil_of_le
    rw [List.length_take]; omega
  have h_win : (tokens.toList.take (lo + 2)).drop lo
      = [tokens.toList[lo]'h_lo_len, tokens.toList[lo + 1]'h_lo1_len] := by
    have e1 := (List.getElem_cons_drop hlen1).symm
    rw [List.getElem_take, h_drop_nil] at e1
    have e0 := (List.getElem_cons_drop hlen0).symm
    rw [List.getElem_take, e1] at e0
    exact e0
  rw [h_win]
  have h_op_val : (tokens.toList[lo]'h_lo_len).val = .flowSequenceStart := by
    have hb : tokens[lo]! = tokens.toList[lo]'h_lo_len := by
      rw [getElem!_pos tokens lo h_lo_sz, Array.getElem_toList]
    rw [← hb]; exact h_open
  have h_cl_val : (tokens.toList[lo + 1]'h_lo1_len).val = .flowSequenceEnd := by
    have hb : tokens[lo + 1]! = tokens.toList[lo + 1]'h_lo1_len := by
      rw [getElem!_pos tokens (lo + 1) h_lo1_sz, Array.getElem_toList]
    rw [← hb]; exact h_close
  exact RecSeqEntry.seqEmpty _ _ h_op_val h_cl_val

/-- **Nested-mapping entry window** (Phase J — the entry-boundary location's *shape side*, seq, the
    NEAR-leaf — the family's last member).  The fourth `RecSeqEntry` constructor is `map`: a nested
    flow-mapping `{ interior }` appearing as one item of the enclosing flow-SEQUENCE.  Given a window
    `[lo, hi]` whose head `tokens[lo]` is a `.flowMappingStart`, whose `tokens[hi]` is the matching
    `.flowMappingEnd`, and whose interior window `(tokens.toList.take hi).drop (lo + 1)` is
    `WellBracketed`, the opener-window `(tokens.toList.take (hi + 1)).drop lo` is a `RecSeqEntry.map`.

    It is a NEAR-leaf rather than a true leaf (scalar/seqEmpty span a fixed token count; this one spans
    a *variable* interior `[lo+1, hi)`) — but, crucially, NOT a recursion edge: `RecSeqEntry.map`
    **stores only `WellBracketed interior`** (R244), it does NOT carry a `RecSeqBody`/`RecMapBody`.  The
    map's key/value recursion is a separate map-side substrate, severed here; the enclosing seq locate
    does not descend through it.  So this lift is the *near-leaf* that terminates the seq dispatch on a
    `.flowMappingStart` head — `flowBracketBalance_matching_close_map` supplies `hi` and the interior's
    `WellBracketed`; this lemma packages them into the constructor.

    It is the SAME window plumbing as the recursive `.seq` BUILD move `located_entry_of_recseqbody`,
    transported VERBATIM — the rest-decomposition `(take (hi+1)).drop (lo+1) = (take hi).drop (lo+1) ++
    [tokens[hi]]` (`List.take_add_one` + `List.drop_append_of_le_length`) and the opener peel
    (`List.getElem_cons_drop` + `List.getElem_take`) put the window into `op :: (interior ++ [cl])`
    shape — with exactly two differences, both reading the storage decision: the terminal constructor
    is `RecSeqEntry.map` (not `.seq`), and it is fed the bare `WellBracketed interior` hypothesis (not
    `h_rec.toWellBracketed h_rec` from a `RecSeqBody`).  That one-field arity delta between the seq
    BUILD and this map near-leaf IS the storage decision: `.seq` recurses (stores a body), `.map`
    projects (stores only the balance fact).  With this the seq shape side's four-constructor dispatch
    family is COMPLETE: `scalar`/`seqEmpty` leaves, this `map` near-leaf, and `.seq` via the BUILD move.

    Verified-but-unconsumed: references no sorry site, frontier sorry count unchanged; axiom-clean
    `[propext, Quot.sound]`. -/
theorem recseqentry_map_window (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo_hi : lo < hi) (h_hi_sz : hi < tokens.size)
    (h_open : tokens[lo]!.val = .flowMappingStart)
    (h_close : tokens[hi]!.val = .flowMappingEnd)
    (h_wb : WellBracketed ((tokens.toList.take hi).drop (lo + 1))) :
    RecSeqEntry ((tokens.toList.take (hi + 1)).drop lo) := by
  have h_hi_len : hi < tokens.toList.length := by rw [Array.length_toList]; exact h_hi_sz
  have h_lo_sz : lo < tokens.size := by omega
  -- rest-decomposition: the `interior ++ [cl]` tail (mirrors `located_entry_of_recseqbody`).
  have h_rest : (tokens.toList.take (hi + 1)).drop (lo + 1)
      = (tokens.toList.take hi).drop (lo + 1) ++ [tokens.toList[hi]] := by
    have h_ts : tokens.toList.take (hi + 1)
        = tokens.toList.take hi ++ [tokens.toList[hi]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem h_hi_len]; rfl
    rw [h_ts]
    have h_len : lo + 1 ≤ (tokens.toList.take hi).length := by rw [List.length_take]; omega
    rw [List.drop_append_of_le_length h_len]
  -- peel the opener: the opener-window is `tokens[lo] :: rest`.
  have h_peel : (tokens.toList.take (hi + 1)).drop lo
      = tokens.toList[lo]'(by rw [Array.length_toList]; omega)
        :: (tokens.toList.take (hi + 1)).drop (lo + 1) := by
    have hlen : lo < (tokens.toList.take (hi + 1)).length := by
      rw [List.length_take]; omega
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take] at h
    exact h
  -- target window now reads as `op :: (interior ++ [cl])`.
  rw [h_peel, h_rest]
  have h_op_val : (tokens.toList[lo]'(by rw [Array.length_toList]; omega)).val
      = .flowMappingStart := by
    have hb : tokens[lo]! = tokens.toList[lo]'(by rw [Array.length_toList]; omega) := by
      rw [getElem!_pos tokens lo h_lo_sz, Array.getElem_toList]
    rw [← hb]; exact h_open
  have h_cl_val : (tokens.toList[hi]'h_hi_len).val = .flowMappingEnd := by
    have hb : tokens[hi]! = tokens.toList[hi]'h_hi_len := by
      rw [getElem!_pos tokens hi h_hi_sz, Array.getElem_toList]
    rw [← hb]; exact h_close
  exact RecSeqEntry.map _ _ _ h_op_val h_cl_val h_wb

/-- **Map-pair window assembler** (Phase J — the entry-boundary location's *shape side*, MAP axis —
    the map mirror of the now-complete seq dispatch family).  Where the seq shape side is a four-way
    dispatch on a single head token (`recseqentry_{scalar,seqempty,map}_window` + the BUILD move for
    the recursive `.seq`, Reflections 265–267), the map body's first item is a whole key/value PAIR
    `.key <block_k> .value <block_v>` (`RecMapPair`).  So the map shape side is **not** a per-constructor
    dispatch at all — it is ONE assembler that GLUES two already-located `RecSeqEntry` blocks with the
    depth-`0` `.key`/`.value` markers.  Given a key marker `tokens[lo] = .key`, the key block over
    `[lo+1, kv)` as a `RecSeqEntry`, a value marker `tokens[kv] = .value`, and the value block over
    `[kv+1, m)` as a `RecSeqEntry`, the pair window `(tokens.toList.take m).drop lo` is a `RecMapPair`.

    This is where the seq side's completed four-constructor dispatch is *consumed*: the key and value
    blocks are arbitrary `RecSeqEntry`s — a scalar, an empty bracket, a nested sequence (via the seq
    BUILD move), or a nested mapping (the `map` near-leaf) — so the map shape side adds NO new
    per-constructor classification; the seq dispatch already covers every block shape.  Its only new
    work is the pair glue, and *that* is itself a composition of two ALREADY-landed positional patterns:
    the segment split at the `.value` separator (`recseqbody_cons_window`'s ADVANCE plumbing —
    `List.take_append_drop`/`take_take`/`drop_drop`, here splitting the pair interior `[lo+1, m)` at
    `kv`) and the opener peel of `tokens[lo]` (`List.getElem_cons_drop` + `List.getElem_take`, the BUILD
    move's head peel).  Terminated by `RecMapPair.mk`, whose `kt :: (block_k ++ vt :: block_v)` index is
    exactly the peeled-and-split window, with both marker values transported from `tokens[·]!` via
    `getElem!_pos`/`Array.getElem_toList`.

    So the map shape side costs no fresh structural insight — it reuses the seq dispatch (as its two
    sub-blocks) and the ADVANCE+BUILD plumbing (as its one glue), the parallel-type re-split (the map
    leaf is a PAIR, not a single bracketed item) surfacing here as *composition* rather than a new
    family.  Verified-but-unconsumed: takes the two `RecSeqEntry` blocks as hypotheses (agnostic to
    their production — the map locate supplies them by recursing the key/value substructure), references
    no sorry site, frontier sorry count unchanged; axiom-clean `[propext, Classical.choice, Quot.sound]`
    (the `Classical.choice` enters through the reused ADVANCE segment-split plumbing, where the simpler
    one-token and two-token seq leaves stayed at `[propext, Quot.sound]`). -/
theorem recmappair_window (tokens : Array (Positioned YamlToken)) (lo kv m : Nat)
    (h_lo_kv : lo < kv) (h_kv_m : kv < m) (h_m_sz : m ≤ tokens.size)
    (h_key : tokens[lo]!.val = .key)
    (h_value : tokens[kv]!.val = .value)
    (h_ke : RecSeqEntry ((tokens.toList.take kv).drop (lo + 1)))
    (h_ve : RecSeqEntry ((tokens.toList.take m).drop (kv + 1))) :
    RecMapPair ((tokens.toList.take m).drop lo) := by
  have h_lo_sz : lo < tokens.size := by omega
  have h_kv_sz : kv < tokens.size := by omega
  have h_lo_len : lo < tokens.toList.length := by rw [Array.length_toList]; exact h_lo_sz
  have h_kv_len : kv < tokens.toList.length := by rw [Array.length_toList]; exact h_kv_sz
  -- segment split: the pair interior `[lo+1, m)` divides at the `.value` marker `kv`
  -- (`recseqbody_cons_window`'s ADVANCE plumbing, with `hi := m`, `lo := lo+1`, `m := kv`).
  have hA : (tokens.toList.take m).drop (lo + 1)
      = (tokens.toList.take kv).drop (lo + 1) ++ (tokens.toList.take m).drop kv := by
    rw [← List.take_append_drop (kv - (lo + 1)) ((tokens.toList.take m).drop (lo + 1))]
    congr 1
    · rw [List.drop_take, List.drop_take, List.take_take,
        Nat.min_eq_left (show kv - (lo + 1) ≤ m - (lo + 1) by omega)]
    · rw [List.drop_drop, Nat.add_sub_cancel' (show lo + 1 ≤ kv by omega)]
  -- separator peel: the `.value` marker at `kv` heads the value half `[kv, m)`.
  have hB : (tokens.toList.take m).drop kv
      = tokens.toList[kv]'h_kv_len :: (tokens.toList.take m).drop (kv + 1) := by
    have hlen : kv < (tokens.toList.take m).length := by
      rw [List.length_take,
        Nat.min_eq_left (show m ≤ tokens.toList.length by rw [Array.length_toList]; omega)]
      exact h_kv_m
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take] at h
    exact h
  -- opener peel: the `.key` marker at `lo` heads the whole pair window `[lo, m)`.
  have h_peel : (tokens.toList.take m).drop lo
      = tokens.toList[lo]'h_lo_len :: (tokens.toList.take m).drop (lo + 1) := by
    have hlen : lo < (tokens.toList.take m).length := by
      rw [List.length_take,
        Nat.min_eq_left (show m ≤ tokens.toList.length by rw [Array.length_toList]; omega)]
      omega
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take] at h
    exact h
  -- whole window now reads as `kt :: (block_k ++ vt :: block_v)`.
  rw [h_peel, hA, hB]
  have h_kt_val : (tokens.toList[lo]'h_lo_len).val = .key := by
    have hb : tokens[lo]! = tokens.toList[lo]'h_lo_len := by
      rw [getElem!_pos tokens lo h_lo_sz, Array.getElem_toList]
    rw [← hb]; exact h_key
  have h_vt_val : (tokens.toList[kv]'h_kv_len).val = .value := by
    have hb : tokens[kv]! = tokens.toList[kv]'h_kv_len := by
      rw [getElem!_pos tokens kv h_kv_sz, Array.getElem_toList]
    rw [← hb]; exact h_value
  exact RecMapPair.mk _ _ _ _ h_kt_val h_ke h_vt_val h_ve

/-- **Scalar head-dispatch step** (Phase J — the seq locate DRIVER's head-dispatch, first branch).
    The locate recursion's driver, after `firstEntryBoundary` (the input side) pins the least boundary
    marker `m` of a balanced body-interior window `[lo, hi)`, must classify the first item `[lo, m)` by
    its head token and fire the matching shape-side lift.  This is that dispatch's *scalar branch*, and
    — exactly as the shape side itself was built leaf-first (`recseqentry_scalar_window` ahead of the
    `seqEmpty`/`map`/`seq` lifts) — it is the dispatch's leaf, landing ahead of the bracket branches.

    Where the four shape-side lifts each take their split point as a *given* (`recseqentry_scalar_window`
    is stated at the fixed window `[lo, lo+1)`), the dispatch's job is to *derive* the split point from
    the locator's minimality.  A scalar head contributes bracket delta `0` (`flowBracketDelta_scalar`),
    so `balance lo (lo+1) = 0` (`flowBracketBalance_single`); given the grammar substrate `h_succ` —
    the scalar entry is *complete*, i.e. position `lo+1` is the window end or a `.flowEntry` separator —
    `lo+1` is itself a *boundary marker*.  `firstEntryBoundary` returned `m` as the **least** marker in
    `(lo, hi]`, so `m ≤ lo+1`; with `lo < m` that forces `m = lo+1`, and the located window `[lo, m)`
    *is* the one-token scalar window the leaf lift `recseqentry_scalar_window` classifies.

    This is the bridge the shape-side family could not state on its own: the lifts produce the entry at
    a *fixed* arity, the locator produces a *variable* marker `m`, and the dispatch is what proves the
    two coincide.  The grammar fact `h_succ` is the *trailing-separator* substrate the driver will
    recover per-window (the body's `_h_body_succ`-style value-end successor, via `WellTyped_subrange`);
    here it is taken as a hypothesis, in the verified-but-unconsumed discipline — the lemma references
    no sorry site, so the frontier sorry count is unchanged at 4.

    Axis note (R264 discriminator): it names a collection-specific deliverable type (`RecSeqEntry`,
    through `recseqentry_scalar_window`), so it is seq-specific and re-splits across the map axis — the
    map dispatch's leaf is the scalar-key/scalar-value PAIR (`recmappair_window`), not this one-token
    singleton.  But the *minimality → split-point* argument is shared shape; the map mirror reuses it. -/
theorem recseqentry_scalar_dispatch (tokens : Array (Positioned YamlToken)) (lo hi m : Nat)
    (h_lo_sz : lo < tokens.size)
    (h_lo_m : lo < m) (_h_m_hi : m ≤ hi)
    (h_m_least : ∀ k, lo < k → k < m →
      ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry)))
    (h_scalar : ∃ c s, tokens[lo]!.val = .scalar c s)
    (h_succ : lo + 1 = hi ∨ tokens[lo + 1]!.val = .flowEntry) :
    m = lo + 1 ∧ RecSeqEntry ((tokens.toList.take m).drop lo) := by
  have h_lo_len : lo < tokens.toList.length := by rw [Array.length_toList]; exact h_lo_sz
  obtain ⟨c, s, hcs⟩ := h_scalar
  -- The scalar head contributes bracket delta 0, so the one-token range `[lo, lo+1)` is balanced.
  have h_val : (tokens.toList[lo]'h_lo_len).val = .scalar c s := by
    have hb : tokens[lo]! = tokens.toList[lo]'h_lo_len := by
      rw [getElem!_pos tokens lo h_lo_sz, Array.getElem_toList]
    rw [← hb]; exact hcs
  have h_bal1 : flowBracketBalance tokens lo (lo + 1) = 0 := by
    rw [flowBracketBalance_single tokens lo h_lo_len, h_val, flowBracketDelta_scalar]
  -- `lo+1` is a boundary marker (balanced + completes the entry), so the least marker `m` is at most it.
  have h_marker1 : flowBracketBalance tokens lo (lo + 1) = 0 ∧
      (lo + 1 = hi ∨ tokens[lo + 1]!.val = .flowEntry) := ⟨h_bal1, h_succ⟩
  have h_m_eq : m = lo + 1 := by
    rcases Nat.lt_or_ge (lo + 1) m with hlt | hge
    · exact absurd h_marker1 (h_m_least (lo + 1) (by omega) hlt)
    · omega
  refine ⟨h_m_eq, ?_⟩
  rw [h_m_eq]
  exact recseqentry_scalar_window tokens lo h_lo_sz ⟨c, s, hcs⟩

/-- **Empty-sequence head-dispatch step** (Phase J — the seq locate DRIVER's head-dispatch, second
    branch).  The dispatch's second leaf, mirroring `recseqentry_scalar_dispatch` for the empty
    flow-sequence `[ ]` head: given an opener `tokens[lo] = .flowSequenceStart` immediately followed by
    a closer `tokens[lo+1] = .flowSequenceEnd`, it derives the split point `m = lo + 2` from the
    locator's facts and fires the leaf lift `recseqentry_seqempty_window`.

    Here the dispatch reveals an ASYMMETRY the scalar branch hid.  The scalar entry ends at the
    *earliest* candidate `lo+1`, so leastness alone pinned it: `lo+1` is a marker, `m` is the least
    marker, `lo < m` ⟹ `m = lo+1`.  The empty bracket spans TWO tokens, and crucially the intermediate
    position `lo+1` is **not** a marker — the opener drives the running balance to `+1`
    (`flowBracketDelta_flowSequenceStart`), so `balance lo (lo+1) = 1 ≠ 0`.  Leastness (`h_m_least`,
    quantified over `(lo, m)`) says nothing about `m` itself and so PERMITS `m = lo+1`; minimality alone
    cannot push the split past the un-balanced opener.  To exclude `m = lo+1` the dispatch must consume
    the locator's OTHER output — that `m` is *itself* a boundary marker (`h_m_marker`, `balance lo m = 0`
    ∧ completes the entry) — which `balance lo (lo+1) = 1` contradicts, forcing `m ≠ lo+1`.  Combined
    with `m ≤ lo+2` (minimality against the genuine marker `lo+2`, where the closer returns the balance
    to `0`: `+1` then `flowBracketDelta_flowSequenceEnd = -1`, composed) and `lo < m`, this gives
    `m = lo+2`.

    So the head-dispatch is where the *two* halves of `firstEntryBoundary`'s output split by branch: the
    one-token scalar leaf needs only the LEAST clause, every multi-token bracket leaf needs the MARKER
    clause too (to step over its own interior non-markers).  The marker hypothesis is exactly the
    `firstEntryBoundary` conjunct the driver carries for free; here it is taken as a hypothesis, in the
    verified-but-unconsumed discipline — references no sorry site, frontier sorry count unchanged at 4;
    axiom-clean `[propext, Quot.sound]`. -/
theorem recseqentry_seqempty_dispatch (tokens : Array (Positioned YamlToken)) (lo hi m : Nat)
    (h_lo1_sz : lo + 1 < tokens.size)
    (h_lo_m : lo < m) (_h_m_hi : m ≤ hi)
    (h_m_marker : flowBracketBalance tokens lo m = 0 ∧ (m = hi ∨ tokens[m]!.val = .flowEntry))
    (h_m_least : ∀ k, lo < k → k < m →
      ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry)))
    (h_open : tokens[lo]!.val = .flowSequenceStart)
    (h_close : tokens[lo + 1]!.val = .flowSequenceEnd)
    (h_succ : lo + 2 = hi ∨ tokens[lo + 2]!.val = .flowEntry) :
    m = lo + 2 ∧ RecSeqEntry ((tokens.toList.take m).drop lo) := by
  have h_lo_sz : lo < tokens.size := by omega
  have h_lo_len : lo < tokens.toList.length := by rw [Array.length_toList]; exact h_lo_sz
  have h_lo1_len : lo + 1 < tokens.toList.length := by rw [Array.length_toList]; exact h_lo1_sz
  -- head values transported from `tokens[·]!` to the `toList` indexing the balance lemmas use.
  have h_op_val : (tokens.toList[lo]'h_lo_len).val = .flowSequenceStart := by
    have hb : tokens[lo]! = tokens.toList[lo]'h_lo_len := by
      rw [getElem!_pos tokens lo h_lo_sz, Array.getElem_toList]
    rw [← hb]; exact h_open
  have h_cl_val : (tokens.toList[lo + 1]'h_lo1_len).val = .flowSequenceEnd := by
    have hb : tokens[lo + 1]! = tokens.toList[lo + 1]'h_lo1_len := by
      rw [getElem!_pos tokens (lo + 1) h_lo1_sz, Array.getElem_toList]
    rw [← hb]; exact h_close
  -- the opener contributes +1, so `lo+1` is NOT balanced — it cannot be the marker.
  have h_bal1 : flowBracketBalance tokens lo (lo + 1) = 1 := by
    rw [flowBracketBalance_single tokens lo h_lo_len, h_op_val, flowBracketDelta_flowSequenceStart]
  -- the closer returns the depth to 0 at `lo+2`: `balance lo (lo+2) = 1 + (-1) = 0`.
  have h_single2 : flowBracketBalance tokens (lo + 1) (lo + 2) = -1 := by
    rw [flowBracketBalance_single tokens (lo + 1) h_lo1_len, h_cl_val,
      flowBracketDelta_flowSequenceEnd]
  have h_bal2 : flowBracketBalance tokens lo (lo + 2) = 0 := by
    rw [flowBracketBalance_compose tokens lo (lo + 1) (lo + 2) (by omega) (by omega),
      h_bal1, h_single2]; decide
  -- `lo+2` is a genuine boundary marker (balanced + completes the entry, via `h_succ`).
  have h_marker2 : flowBracketBalance tokens lo (lo + 2) = 0 ∧
      (lo + 2 = hi ∨ tokens[lo + 2]!.val = .flowEntry) := ⟨h_bal2, h_succ⟩
  -- minimality ⟹ `m ≤ lo+2`; the marker clause excludes `m = lo+1` (its balance is 1, not 0).
  have h_m_le : m ≤ lo + 2 := by
    rcases Nat.lt_or_ge (lo + 2) m with hlt | hge
    · exact absurd h_marker2 (h_m_least (lo + 2) (by omega) hlt)
    · exact hge
  have h_m_ne1 : m ≠ lo + 1 := by
    intro h
    have hmb := h_m_marker.1
    rw [h, h_bal1] at hmb
    omega
  have h_m_eq : m = lo + 2 := by omega
  refine ⟨h_m_eq, ?_⟩
  rw [h_m_eq]
  exact recseqentry_seqempty_window tokens lo h_lo1_sz h_open h_close

/-- **Bracket head-dispatch resolution** (Phase J — the seq locate DRIVER's head-dispatch, the shared
    spine of the two BRACKET branches).  The scalar/`seqEmpty` leaves above pin the split point at a
    *fixed* arity (`lo+1`, `lo+2`); a bracket-headed entry — a nested sequence `[ … ]` or mapping
    `{ … }` — spans a *variable* interior, so its split point `m` is wherever the matching close sits,
    `+1`.  This lemma is that resolution, written ONCE and reused by both the `seq` (recursive) and `map`
    (near-leaf) branches, since the minimality→split argument is shape-shared (R264): it is stated over
    the bracket *delta* (`flowBracketDelta tokens[lo]!.val = 1`), not the specific opener token.

    Its hypotheses are *exactly* the five outputs of the generic `flowBracketBalance_matching_close`
    (taken at the depth-0 opener `k := lo`) plus the two `firstEntryBoundary` conjuncts — so it consumes
    the locator verbatim.  `matching_close` supplies the close position `j` (`lo < j < hi`), its closer
    delta (`-1`), the inner balance (`balance (lo+1) j = 0`), AND — crucially — the strict-positivity
    invariant `∀ i, lo < i → i ≤ j → balance lo i ≥ 1` that the *typed* wrappers
    `flowBracketBalance_matching_close_{seq,map}` DROP.  That invariant is what the `seqEmpty` branch had
    hard-coded as the single fact `balance lo (lo+1) = 1`: it is the general statement that the running
    depth never returns to `0` anywhere strictly inside the bracket, so no interior position can be a
    boundary marker.

    The resolution then runs the same two-sided squeeze the `seqEmpty` leaf ran, now at the variable
    `j+1`.  Composing the opener (`+1`) and the closer at `j` (`-1`) around the balanced interior gives
    `balance lo (j+1) = 0`; with the grammar substrate `h_succ` (position `j+1` ends the window or is a
    `.flowEntry` — the completed bracket entry's successor), `j+1` is a genuine boundary marker, so
    minimality forces `m ≤ j+1` (UPPER bound, the LEAST clause).  Conversely the positivity invariant
    gives `balance lo i ≥ 1` for every `lo < i ≤ j`, contradicting the MARKER clause `balance lo m = 0`
    unless `m > j` — the LOWER bound `m ≥ j+1`.  Together `m = j+1`.  This is the precise generalization
    the dependency map flagged the bracket branches owe: the LEAST clause bounds `m` above, the MARKER
    clause (via positivity) bounds it below, and the split lands exactly past the matching close.

    Verified-but-unconsumed: references no sorry site, frontier sorry count unchanged at 4; produces only
    the arithmetic identity `m = j+1`, agnostic to which bracket (`seq` vs `map`) — the two branches
    layer the close-token type and the window lift on top.  Axiom-clean `[propext, Classical.choice,
    Quot.sound]` (no `sorryAx`); the `Classical.choice` enters through `flowBracketBalance_compose`'s
    `List.foldl` machinery, exactly as in the `seqEmpty` leaf and unlike the compose-free scalar leaf. -/
theorem firstEntryBoundary_bracket_resolve (tokens : Array (Positioned YamlToken)) (lo hi m j : Nat)
    (h_hi_sz : hi ≤ tokens.size)
    (h_lo_m : lo < m) (_h_m_hi : m ≤ hi)
    (h_m_marker : flowBracketBalance tokens lo m = 0 ∧ (m = hi ∨ tokens[m]!.val = .flowEntry))
    (h_m_least : ∀ k, lo < k → k < m →
      ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry)))
    (h_open_delta : flowBracketDelta tokens[lo]!.val = 1)
    (h_lo_j : lo < j) (h_j_hi : j < hi)
    (h_j_close_delta : flowBracketDelta tokens[j]!.val = -1)
    (h_inner : flowBracketBalance tokens (lo + 1) j = 0)
    (h_j_pos : ∀ i, lo < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1)
    (h_succ : j + 1 = hi ∨ tokens[j + 1]!.val = .flowEntry) :
    m = j + 1 := by
  have h_lo_sz : lo < tokens.size := by omega
  have h_j_sz : j < tokens.size := by omega
  have h_lo_len : lo < tokens.toList.length := by rw [Array.length_toList]; exact h_lo_sz
  have h_j_len : j < tokens.toList.length := by rw [Array.length_toList]; exact h_j_sz
  -- opener/closer deltas, transported from `tokens[·]!` to the `toList` indexing the balance lemmas use.
  have h_op_delta_list : flowBracketDelta (tokens.toList[lo]'h_lo_len).val = 1 := by
    have hb : tokens[lo]! = tokens.toList[lo]'h_lo_len := by
      rw [getElem!_pos tokens lo h_lo_sz, Array.getElem_toList]
    rw [← hb]; exact h_open_delta
  have h_cl_delta_list : flowBracketDelta (tokens.toList[j]'h_j_len).val = -1 := by
    have hb : tokens[j]! = tokens.toList[j]'h_j_len := by
      rw [getElem!_pos tokens j h_j_sz, Array.getElem_toList]
    rw [← hb]; exact h_j_close_delta
  -- balance just after the opener is +1; the closer at `j` returns it to 0.
  have h_bal_lo1 : flowBracketBalance tokens lo (lo + 1) = 1 := by
    rw [flowBracketBalance_single tokens lo h_lo_len]; exact h_op_delta_list
  have h_single_j : flowBracketBalance tokens j (j + 1) = -1 := by
    rw [flowBracketBalance_single tokens j h_j_len]; exact h_cl_delta_list
  have h_bal_lo_j : flowBracketBalance tokens lo j = 1 := by
    rw [flowBracketBalance_compose tokens lo (lo + 1) j (by omega) (by omega), h_bal_lo1, h_inner]
    decide
  have h_bal_j1 : flowBracketBalance tokens lo (j + 1) = 0 := by
    rw [flowBracketBalance_compose tokens lo j (j + 1) (by omega) (by omega), h_bal_lo_j, h_single_j]
    decide
  -- `j+1` is a genuine boundary marker (balanced + completes the entry, via `h_succ`).
  have h_marker_j1 : flowBracketBalance tokens lo (j + 1) = 0 ∧
      (j + 1 = hi ∨ tokens[j + 1]!.val = .flowEntry) := ⟨h_bal_j1, h_succ⟩
  -- UPPER bound: minimality against the marker `j+1` (the LEAST clause).
  have h_m_le : m ≤ j + 1 := by
    rcases Nat.lt_or_ge (j + 1) m with hlt | hge
    · exact absurd h_marker_j1 (h_m_least (j + 1) (by omega) hlt)
    · exact hge
  -- LOWER bound: positivity forbids a depth-0 marker at any `lo < m ≤ j` (the MARKER clause).
  have h_m_ge : j + 1 ≤ m := by
    rcases Nat.lt_or_ge j m with hjm | hmj
    · omega
    · have hpos := h_j_pos m h_lo_m hmj
      rw [h_m_marker.1] at hpos
      omega
  omega

/-- **Nested-mapping head-dispatch step** (Phase J — the seq locate DRIVER's head-dispatch, the first
    of the two BRACKET branches, and the cheaper one — the NEAR-leaf).  After the two fixed-arity leaves
    (`recseqentry_scalar_dispatch` at `m = lo+1`, `recseqentry_seqempty_dispatch` at `m = lo+2`), this is
    the dispatch step for a seq item whose head `tokens[lo]` is a `.flowMappingStart` — a nested mapping
    `{ … }` spanning a *variable* interior `[lo+1, j)` up to its matching close `j`.  It is the point at
    which the shared resolution `firstEntryBoundary_bracket_resolve` and the near-leaf window lift
    `recseqentry_map_window` are first composed into one dispatch step, mirroring how the scalar/`seqEmpty`
    branches each glued their leaf-arity resolution to their leaf window lift.

    Two moves, exactly the structure of the two leaf dispatches but with the split point now *variable*:

      • **resolve** the split point.  The two leaf branches computed `m` from a fixed offset; the bracket
        branch instead calls `firstEntryBoundary_bracket_resolve` — fed the locator's two conjuncts
        (`h_m_marker`/`h_m_least`), the opener delta `+1` and closer delta `-1` (rewritten from `h_open`/
        `h_close` through `flowBracketDelta_flowMappingStart`/`_flowMappingEnd`), the inner balance, the
        strict-positivity invariant, and the successor `h_succ` — to pin `m = j + 1`.  The positivity
        invariant is the generalization of the `seqEmpty` branch's hard-coded `balance lo (lo+1) = 1`:
        here it steps the marker past the *whole* bracket interval, not one token.

      • **lift** the window.  With `m = j + 1`, the window `(tokens.toList.take m).drop lo` is the
        opener-window `[lo, j+1)`, and `recseqentry_map_window tokens lo j` (its `hi := j`) classifies it
        as a `RecSeqEntry.map` from the head/close tokens and the interior `WellBracketed`.

    This is a NEAR-leaf, not a recursion edge: `RecSeqEntry.map` stores only `WellBracketed interior`
    (R244), so the dispatch consumes the interior balance fact directly and never calls the locate
    recursion on the nested mapping.  That is precisely why it lands BEFORE the `seq`-bracket branch: the
    `.flowSequenceStart` head needs the recursive oracle (the inner `RecSeqBody` via the BUILD move
    `located_entry_of_recseqbody`), which only exists once the `Nat.strongRecOn` driver is in place; the
    `.flowMappingStart` head terminates at `WellBracketed` and so needs no oracle.  It takes the close
    position `j`, the interior balance/positivity, and the interior `WellBracketed` as hypotheses — the
    driver will supply them from `flowBracketBalance_matching_close` (positions + positivity), its `_map`
    typed wrapper (the close token), and the interior's well-bracketedness — in the verified-but-unconsumed
    discipline: references no sorry site, frontier sorry count unchanged at 4.  Axiom-clean
    `[propext, Classical.choice, Quot.sound]` (no `sorryAx`); the `Classical.choice` enters through
    `firstEntryBoundary_bracket_resolve`'s `flowBracketBalance_compose` machinery, while
    `recseqentry_map_window`'s window algebra stays at `[propext, Quot.sound]`. -/
theorem recseqentry_map_dispatch (tokens : Array (Positioned YamlToken)) (lo hi m j : Nat)
    (h_hi_sz : hi ≤ tokens.size)
    (h_lo_m : lo < m) (h_m_hi : m ≤ hi)
    (h_m_marker : flowBracketBalance tokens lo m = 0 ∧ (m = hi ∨ tokens[m]!.val = .flowEntry))
    (h_m_least : ∀ k, lo < k → k < m →
      ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry)))
    (h_open : tokens[lo]!.val = .flowMappingStart)
    (h_lo_j : lo < j) (h_j_hi : j < hi)
    (h_close : tokens[j]!.val = .flowMappingEnd)
    (h_inner : flowBracketBalance tokens (lo + 1) j = 0)
    (h_j_pos : ∀ i, lo < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1)
    (h_wb : WellBracketed ((tokens.toList.take j).drop (lo + 1)))
    (h_succ : j + 1 = hi ∨ tokens[j + 1]!.val = .flowEntry) :
    m = j + 1 ∧ RecSeqEntry ((tokens.toList.take m).drop lo) := by
  -- opener/closer deltas, read off the head/close tokens.
  have h_open_delta : flowBracketDelta tokens[lo]!.val = 1 := by
    rw [h_open]; exact flowBracketDelta_flowMappingStart
  have h_close_delta : flowBracketDelta tokens[j]!.val = -1 := by
    rw [h_close]; exact flowBracketDelta_flowMappingEnd
  -- resolve: the shared bracket spine pins the split point past the matching close.
  have h_m_eq : m = j + 1 :=
    firstEntryBoundary_bracket_resolve tokens lo hi m j h_hi_sz h_lo_m h_m_hi
      h_m_marker h_m_least h_open_delta h_lo_j h_j_hi h_close_delta h_inner h_j_pos h_succ
  refine ⟨h_m_eq, ?_⟩
  -- lift: with `m = j+1` the window is the opener-window `[lo, j+1)`, a `RecSeqEntry.map` near-leaf.
  rw [h_m_eq]
  exact recseqentry_map_window tokens lo j h_lo_j (by omega) h_open h_close h_wb

/-- **Recursive-sequence head-dispatch step** (Phase J — the seq locate DRIVER's head-dispatch, the
    SECOND of the two BRACKET branches, and the recursive one).  Verbatim sibling of
    `recseqentry_map_dispatch` (R275) over the `.flowSequence{Start,End}` head/close tokens: the
    dispatch step for a seq item whose head `tokens[lo]` is a `.flowSequenceStart` — a *nested
    flow-sequence* `[ … ]` spanning a variable interior `[lo+1, j)` up to its matching close `j`.  The
    two-move shape is identical to the map branch:

      • **resolve** the split point: the *same* axis-agnostic
        `firstEntryBoundary_bracket_resolve` (R264/R274) — fed the locator's two conjuncts, the opener
        delta `+1` and closer delta `-1` (here through `flowBracketDelta_flowSequence{Start,End}`), the
        inner balance, the strict-positivity invariant, and `h_succ` — pins `m = j + 1`.  This half is
        shared verbatim with the map branch; the resolution names no axis (R264).

      • **lift** the window: with `m = j + 1`, the opener-window `[lo, j+1)` is classified by the BUILD
        move `located_entry_of_recseqbody` (its `lo := lo+1`, `hi := j`, so its opener index
        `(lo+1)-1` reduces to `lo`), which assembles a `RecSeqEntry.seq` from the head/close tokens and
        the *recursive* inner `RecSeqBody`.

    The asymmetry with the map branch is exactly the R275/R244 storage fact, and it surfaces HERE as a
    single hypothesis swap: where the map branch consumed the interior `WellBracketed` (a flat
    decidable fact suppliable inline), this branch consumes the interior `RecSeqBody`
    (`h_rec : RecSeqBody ((tokens.toList.take j).drop (lo + 1))`) — the locate recursion's own output,
    its *oracle*.  So although the dispatch *lemma* is perfectly standalone (it takes the inner body as
    a parameter, just as the map branch takes `WellBracketed`), its eventual *instantiation inside the
    driver* is what waits for the `Nat.strongRecOn` recursion: the driver supplies `h_rec` from its
    recursive call on the strictly-smaller interior window.  This refines R275's framing — both bracket
    dispatch lemmas land standalone; the storage asymmetry is purely in whether the body-hypothesis is
    dischargeable *outside* the recursion (map: yes, inline; seq: no, only by the oracle).  With this,
    all four `RecSeqEntry` constructors — `scalar`, `seqEmpty`, `map`, `seq` — have a head-dispatch
    step, completing the dispatch family; only the driver that threads them remains.
    Verified-but-unconsumed: references no sorry site, frontier sorry count unchanged at 4.  Axiom-clean
    `[propext, Classical.choice, Quot.sound]` (no `sorryAx`); the `Classical.choice` enters through
    `firstEntryBoundary_bracket_resolve`'s `flowBracketBalance_compose` machinery. -/
theorem recseqentry_seq_dispatch (tokens : Array (Positioned YamlToken)) (lo hi m j : Nat)
    (h_hi_sz : hi ≤ tokens.size)
    (h_lo_m : lo < m) (h_m_hi : m ≤ hi)
    (h_m_marker : flowBracketBalance tokens lo m = 0 ∧ (m = hi ∨ tokens[m]!.val = .flowEntry))
    (h_m_least : ∀ k, lo < k → k < m →
      ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry)))
    (h_open : tokens[lo]!.val = .flowSequenceStart)
    (h_lo_j : lo < j) (h_j_hi : j < hi)
    (h_close : tokens[j]!.val = .flowSequenceEnd)
    (h_inner : flowBracketBalance tokens (lo + 1) j = 0)
    (h_j_pos : ∀ i, lo < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1)
    (h_rec : RecSeqBody ((tokens.toList.take j).drop (lo + 1)))
    (h_succ : j + 1 = hi ∨ tokens[j + 1]!.val = .flowEntry) :
    m = j + 1 ∧ RecSeqEntry ((tokens.toList.take m).drop lo) := by
  -- opener/closer deltas, read off the head/close tokens (the seq axis).
  have h_open_delta : flowBracketDelta tokens[lo]!.val = 1 := by
    rw [h_open]; exact flowBracketDelta_flowSequenceStart
  have h_close_delta : flowBracketDelta tokens[j]!.val = -1 := by
    rw [h_close]; exact flowBracketDelta_flowSequenceEnd
  -- resolve: the SAME shared bracket spine pins the split point past the matching close.
  have h_m_eq : m = j + 1 :=
    firstEntryBoundary_bracket_resolve tokens lo hi m j h_hi_sz h_lo_m h_m_hi
      h_m_marker h_m_least h_open_delta h_lo_j h_j_hi h_close_delta h_inner h_j_pos h_succ
  refine ⟨h_m_eq, ?_⟩
  -- lift: with `m = j+1` the window is the opener-window `[lo, j+1)`, a recursive `RecSeqEntry.seq`
  -- built by the BUILD move from the inner-window `RecSeqBody` oracle.
  rw [h_m_eq]
  exact located_entry_of_recseqbody tokens (lo + 1) j (by omega) (by omega) (by omega)
    h_open h_close h_rec

/-- **Full seq-bracket close locator** (Phase J — the seq locate DRIVER's head-dispatch *shape-INPUT*:
    locating where a bracket-headed item ends, the input half of the bracket-head classification).
    The four dispatch steps above each take the matching close `j` and its facts as *hypotheses*; this
    lemma is their supplier for the `seq`-bracket head — given a depth-`0` flow-sequence opener at the
    window head `tokens[lo]`, it locates the matching close `j` and returns the **complete** fact bundle
    `recseqentry_seq_dispatch` consumes: position (`lo < j < hi`), the close token
    (`tokens[j] = .flowSequenceEnd`), the inner balance (`balance (lo+1) j = 0`), and the
    strict-positivity invariant (`∀ i, lo < i ≤ j → balance lo i ≥ 1`).

    This is the R274-coda problem made concrete (cf. [[ref-array-wrapper-window-generalization]]): the
    bundle the dispatch needs is *split across two lossy sources*.  The generic
    `flowBracketBalance_matching_close` (at the depth-`0` opener `k := lo`) carries the positivity
    invariant and the inner balance but *not* the close token type (only its delta `-1`, which could be
    `]` or `}`); the typed wrappers `flowBracketBalance_matching_close_{seq,map}` carry the close token
    but *drop* positivity.  Calling them independently yields two existentials over possibly-different
    `j`'s.  The fix is to reach past the typed wrapper to its *core*: run the generic locator once to fix
    the unique `j` *with* positivity, then feed that same `j`'s facts to `matching_close_typed_core`
    (`b := true`, the seq opener pushes `[true]`) + `btStep_pop_eq_seqEnd` to read the close token off it.
    One `j`, all five facts — the typed wrapper's positivity loss healed at the source.

    It mirrors seq/map (it names the close token `.flowSequenceEnd`), so per the input/shape re-split it
    is the seq half; the `map` mirror over `.flowMappingEnd` is the symmetric next brick.
    Verified-but-unconsumed (R225): references no sorry site, frontier sorry count unchanged at 4.
    Axiom-clean `[propext, Classical.choice, Quot.sound]` (no `sorryAx`); the `Classical.choice` enters
    through `flowBracketBalance_matching_close`'s `flowBracketBalance_compose`/`List.foldl` machinery. -/
theorem matchingClose_full_seq (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo_hi : lo < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_open : tokens[lo]!.val = .flowSequenceStart)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo)) :
    ∃ j, lo < j ∧ j < hi ∧ tokens[j]!.val = .flowSequenceEnd ∧
      flowBracketBalance tokens (lo + 1) j = 0 ∧
      (∀ i, lo < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) := by
  have h_k_depth : flowBracketBalance tokens lo lo = 0 := by
    unfold flowBracketBalance; rw [if_pos (Nat.le_refl lo)]
  have h_open_delta : flowBracketDelta tokens[lo]!.val = 1 := by
    rw [h_open]; exact flowBracketDelta_flowSequenceStart
  -- generic locator (at `k := lo`): fixes the unique `j`, carries inner balance + positivity.
  obtain ⟨j, h_lo_j, h_j_hi, _h_j_delta, h_inner, h_pos⟩ :=
    flowBracketBalance_matching_close tokens lo lo hi (Nat.le_refl lo) h_lo_hi h_hi_sz
      h_k_depth h_open_delta h_total h_dyck
  -- typed core at the *same* `j`: read the close token `.flowSequenceEnd` off the `[true]` pop.
  have h_k_push : btStep tokens[lo]! [] = some [true] := by unfold btStep; rw [h_open]
  have h_pop := matching_close_typed_core tokens lo lo j hi true (Nat.le_refl lo) h_lo_j h_j_hi
    h_hi_sz h_k_depth h_k_push h_inner _h_j_delta h_pos h_wt
  exact ⟨j, h_lo_j, h_j_hi, btStep_pop_eq_seqEnd _ h_pop, h_inner, h_pos⟩

/-- **Full map-bracket close locator** (Phase J — the seq locate DRIVER's head-dispatch *shape-INPUT*,
    the `map` mirror of `matchingClose_full_seq`).  Given a depth-`0` flow-MAPPING opener at the window
    head `tokens[lo]`, it locates the matching close `j` and returns the **complete** fact bundle
    `recseqentry_map_dispatch` consumes: position (`lo < j < hi`), the close token
    (`tokens[j] = .flowMappingEnd`), the inner balance (`balance (lo+1) j = 0`), and the
    strict-positivity invariant (`∀ i, lo < i ≤ j → balance lo i ≥ 1`).

    Verbatim sibling of the seq locator (cf. [[ref-array-wrapper-window-generalization]] R277 coda): the
    bundle is split across the same two lossy sources, and the same fix applies — run the generic
    `flowBracketBalance_matching_close` once at the depth-`0` opener `k := lo` to fix the unique `j`
    *with* positivity + inner balance, then feed that same `j`'s facts to `matching_close_typed_core`
    (`b := false`, the map opener pushes `[false]`) + `btStep_pop_eq_mapEnd` to read the close token
    `.flowMappingEnd` off it.  The typed wrapper `flowBracketBalance_matching_close_map` is never called;
    only its core is.  The lone collection-specific deltas vs the seq locator: the head token
    `.flowMappingStart`, the pushed stack bottom `false`, the close-reader `btStep_pop_eq_mapEnd`, and the
    returned token `.flowMappingEnd`.

    Verified-but-unconsumed (R225): references no sorry site, frontier sorry count unchanged at 4.
    Axiom-clean `[propext, Classical.choice, Quot.sound]` (no `sorryAx`); `Classical.choice` enters
    through `flowBracketBalance_matching_close`'s `flowBracketBalance_compose`/`List.foldl` machinery. -/
theorem matchingClose_full_map (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo_hi : lo < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_open : tokens[lo]!.val = .flowMappingStart)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo)) :
    ∃ j, lo < j ∧ j < hi ∧ tokens[j]!.val = .flowMappingEnd ∧
      flowBracketBalance tokens (lo + 1) j = 0 ∧
      (∀ i, lo < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) := by
  have h_k_depth : flowBracketBalance tokens lo lo = 0 := by
    unfold flowBracketBalance; rw [if_pos (Nat.le_refl lo)]
  have h_open_delta : flowBracketDelta tokens[lo]!.val = 1 := by
    rw [h_open]; exact flowBracketDelta_flowMappingStart
  -- generic locator (at `k := lo`): fixes the unique `j`, carries inner balance + positivity.
  obtain ⟨j, h_lo_j, h_j_hi, _h_j_delta, h_inner, h_pos⟩ :=
    flowBracketBalance_matching_close tokens lo lo hi (Nat.le_refl lo) h_lo_hi h_hi_sz
      h_k_depth h_open_delta h_total h_dyck
  -- typed core at the *same* `j`: read the close token `.flowMappingEnd` off the `[false]` pop.
  have h_k_push : btStep tokens[lo]! [] = some [false] := by unfold btStep; rw [h_open]
  have h_pop := matching_close_typed_core tokens lo lo j hi false (Nat.le_refl lo) h_lo_j h_j_hi
    h_hi_sz h_k_depth h_k_push h_inner _h_j_delta h_pos h_wt
  exact ⟨j, h_lo_j, h_j_hi, btStep_pop_eq_mapEnd _ h_pop, h_inner, h_pos⟩

/-- **First-item classify unifier** (Phase J — the seq locate DRIVER's grammar-bearing CLASSIFY half,
    folded into one lemma; the brick that finally NAMES the grammar substrate the driver threads).
    The driver's per-window work bifurcates (R279/R280) into a grammar-free ASSEMBLE half
    (`recseqbody_window_assemble` — fold the located entry + the tail oracle into the whole-window
    `RecSeqBody`) and a grammar-BEARING CLASSIFY half (run `firstEntryBoundary` → pin the split `m` →
    head-dispatch the four branches → lift `[lo, m)` into a `RecSeqEntry`).  The four dispatch steps
    (`recseqentry_{scalar,seqempty,map,seq}_dispatch`) each handle ONE head shape, taking their own
    head/close/successor facts as hypotheses; this lemma FOLDS all four — plus `firstEntryBoundary`
    itself — into a single signature whose one new hypothesis is the four-way **head-shape
    disjunction** `h_head`.  That disjunction IS the grammar substrate of a seq body item, named
    explicitly for the first time: a body item is a *scalar*, an *empty sequence* `[ ]`, a *nested
    mapping* `{ … }`, or a *nested sequence* `[ … ]`, each disjunct carrying exactly the facts its
    dispatch consumes (the head token; for brackets the matching-close `j`, its inner balance, the
    strict-positivity invariant, and the close token; for the nested sequence the recursive oracle
    `RecSeqBody` on the interior; and in every case the entry's trailing-separator successor `h_succ`).

    This is the `fold-consumer-chain-to-producer-contract` pattern (cf.
    [[ref-fold-consumer-chain-to-producer-contract]]): the four joint-by-joint dispatch lemmas
    collapse into one lemma whose hypotheses are *exactly* the producer's per-window contract.  The
    conclusion STRENGTHENS `firstEntryBoundary`'s output — it returns the same five facts about the
    split point `m` (`lo < m`, `m ≤ hi`, balance `lo..m = 0`, the marker disjunction, and the
    minimality clause) *plus* the `RecSeqEntry ((take m).drop lo)` classification of the located
    window.  This is the entry-boundary INPUT/SHAPE split (cf.
    [[ref-entry-boundary-input-shape-split]]) fused into a single deliverable: `firstEntryBoundary`
    is the INPUT (where the item ends), the dispatch is the SHAPE (what the item is), and the classify
    unifier delivers both about one `m`.

    The proof is the fold made literal: run `firstEntryBoundary` once to fix `m` and its five facts,
    then `rcases` the head disjunction and hand each branch to its matching dispatch, threading the
    SAME `m`-facts (the dispatch re-derives `m = <split>` internally from minimality + marker, and the
    located `RecSeqEntry` it returns is at *this* `m`).  The bracket branches feed the dispatch the
    pre-located `j` bundle — the genuinely-new fold of the *close-locators* (`matchingClose_full_seq`
    /`_map`) into the disjunction's two bracket disjuncts is deferred: here the `j`-facts are
    hypotheses, so the close-locator-folding and the `Nat.strongRecOn` oracle supply remain the two
    bricks ahead (R280's tee-up).

    Axis note (R264 discriminator): the disjunction names the `RecSeqBody` oracle and the conclusion
    names `RecSeqEntry`, both seq-specific deliverable types, so the unifier re-splits across the map
    axis — the map mirror folds the four `recmappair_*`-style dispatches over the `RecMapPair`/
    `RecMapBody` deliverables and is the symmetric next brick.  Verified-but-unconsumed (R225):
    references no sorry site, frontier sorry count unchanged at 4; axiom-clean `[propext,
    Classical.choice, Quot.sound]` (the `Classical.choice` enters through the bracket dispatches'
    `firstEntryBoundary_bracket_resolve` compose machinery). -/
theorem recseqentry_classify (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo_hi : lo < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_head :
      -- scalar leaf
      ((∃ c s, tokens[lo]!.val = .scalar c s) ∧
        (lo + 1 = hi ∨ tokens[lo + 1]!.val = .flowEntry)) ∨
      -- empty sequence `[ ]`
      (lo + 1 < tokens.size ∧ tokens[lo]!.val = .flowSequenceStart ∧
        tokens[lo + 1]!.val = .flowSequenceEnd ∧
        (lo + 2 = hi ∨ tokens[lo + 2]!.val = .flowEntry)) ∨
      -- nested mapping `{ … }`
      (∃ j, tokens[lo]!.val = .flowMappingStart ∧ lo < j ∧ j < hi ∧
        tokens[j]!.val = .flowMappingEnd ∧
        flowBracketBalance tokens (lo + 1) j = 0 ∧
        (∀ i, lo < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) ∧
        WellBracketed ((tokens.toList.take j).drop (lo + 1)) ∧
        (j + 1 = hi ∨ tokens[j + 1]!.val = .flowEntry)) ∨
      -- nested sequence `[ … ]` (recursive — consumes the locate oracle)
      (∃ j, tokens[lo]!.val = .flowSequenceStart ∧ lo < j ∧ j < hi ∧
        tokens[j]!.val = .flowSequenceEnd ∧
        flowBracketBalance tokens (lo + 1) j = 0 ∧
        (∀ i, lo < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) ∧
        RecSeqBody ((tokens.toList.take j).drop (lo + 1)) ∧
        (j + 1 = hi ∨ tokens[j + 1]!.val = .flowEntry))) :
    ∃ m, lo < m ∧ m ≤ hi ∧
      flowBracketBalance tokens lo m = 0 ∧
      (m = hi ∨ tokens[m]!.val = .flowEntry) ∧
      (∀ k, lo < k → k < m →
        ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry))) ∧
      RecSeqEntry ((tokens.toList.take m).drop lo) := by
  obtain ⟨m, h_lo_m, h_m_hi, h_m_bal, h_m_marker, h_m_least⟩ :=
    firstEntryBoundary tokens lo hi h_lo_hi h_total
  have h_lo_sz : lo < tokens.size := by omega
  refine ⟨m, h_lo_m, h_m_hi, h_m_bal, h_m_marker, h_m_least, ?_⟩
  rcases h_head with
    ⟨h_scalar, h_succ⟩ |
    ⟨h_lo1_sz, h_open, h_close, h_succ⟩ |
    ⟨j, h_open, h_lo_j, h_j_hi, h_close, h_inner, h_j_pos, h_wb, h_succ⟩ |
    ⟨j, h_open, h_lo_j, h_j_hi, h_close, h_inner, h_j_pos, h_rec, h_succ⟩
  · -- scalar: minimality alone pins `m = lo+1`.
    exact (recseqentry_scalar_dispatch tokens lo hi m h_lo_sz h_lo_m h_m_hi h_m_least
      h_scalar h_succ).2
  · -- empty sequence: the marker clause excludes the unbalanced `lo+1`, pinning `m = lo+2`.
    exact (recseqentry_seqempty_dispatch tokens lo hi m h_lo1_sz h_lo_m h_m_hi
      ⟨h_m_bal, h_m_marker⟩ h_m_least h_open h_close h_succ).2
  · -- nested mapping: the bracket spine pins `m = j+1`; near-leaf via `WellBracketed`.
    exact (recseqentry_map_dispatch tokens lo hi m j h_hi_sz h_lo_m h_m_hi
      ⟨h_m_bal, h_m_marker⟩ h_m_least h_open h_lo_j h_j_hi h_close h_inner h_j_pos h_wb h_succ).2
  · -- nested sequence: the same bracket spine pins `m = j+1`; recursive via the `RecSeqBody` oracle.
    exact (recseqentry_seq_dispatch tokens lo hi m j h_hi_sz h_lo_m h_m_hi
      ⟨h_m_bal, h_m_marker⟩ h_m_least h_open h_lo_j h_j_hi h_close h_inner h_j_pos h_rec h_succ).2

/-- **First-pair classify unifier** (Phase J — the MAP locate DRIVER's grammar-bearing CLASSIFY half,
    the symmetric mirror of `recseqentry_classify`; the brick that names the grammar substrate of a
    *map* body item).  Like the seq mirror it folds `firstEntryBoundary` (the INPUT side — locate the
    first item's extent `m`) with the shape side (classify `[lo, m)`) into one lemma whose new
    hypothesis `h_head` IS the named grammar substrate.  But the map substrate is shaped differently,
    and that asymmetry is the lesson: where a seq body item is one of FOUR head shapes (scalar / `[ ]`
    / `{ … }` / `[ … ]`, the four-way disjunction `recseqentry_classify` folds), a *map* body item has
    exactly ONE shape — a key/value PAIR `.key <block_k> .value <block_v>` (`RecMapPair`).  So the map
    substrate is a **conjunction, not a disjunction**: a `.key` head, a depth-`0` `.value` separator at
    some `kv`, and the two interior blocks as arbitrary `RecSeqEntry`s.  The four-way head variety has
    not vanished — it lives one level DOWN, inside the pair's two `RecSeqEntry` sub-blocks, where the
    seq classify already resolves it.  Naming the map grammar substrate thus reveals the map level adds
    no fresh head-shape classification at all: only the pair glue (`recmappair_window`) and the same
    minimality → split-point pin the seq dispatches do.

    That pin is the second half of the lesson.  The seq bracket dispatches got `m = j+1` from a *local*
    positivity invariant (`h_j_pos`: balance `≥ 1` strictly inside the bracket), which rules out any
    interior boundary for free.  A pair's interior is NOT uniformly positive — balance returns to `0`
    at the `.value` separator `kv` (and at every nested-entry end), saved from being a boundary only by
    the token there being `.value`/`.scalar`/a close, never `.flowEntry`.  No single balance invariant
    captures that, so the no-interior-boundary fact is supplied *directly* as the substrate's last
    conjunct (the `h_e_least` clause), in the same verified-but-unconsumed discipline by which the seq
    classify took its `j`-bundle as a hypothesis: producing it from the two `RecSeqEntry`s' structure
    is the next layer down.  Given it, the pin is pure trichotomy — `firstEntryBoundary`'s least
    boundary `m` and the substrate's pair end `e` are each `≤` the other (`m ≤ e` by `m`'s minimality
    on the boundary `e`; `e ≤ m` because `h_e_least` forbids the boundary `m` inside `(lo, e)`), so
    `m = e`, and `recmappair_window` lifts `[lo, e)` to a `RecMapPair`.

    The conclusion STRENGTHENS `firstEntryBoundary` exactly as the seq mirror does — the same five
    split-point facts plus the `RecMapPair ((take m).drop lo)` classification — the entry-boundary
    INPUT/SHAPE split (cf. [[ref-entry-boundary-input-shape-split]]) fused into one deliverable on the
    map axis.  This is again `fold-consumer-chain-to-producer-contract` (cf.
    [[ref-fold-consumer-chain-to-producer-contract]]), here folding `firstEntryBoundary` +
    `recmappair_window` + the pin.  With both axes' classify unifiers landed, the remaining Thread-A
    bricks are folding the close-locators into the bracket disjuncts (deriving `j` from the head) and
    the `Nat.strongRecOn` width-metric driver that supplies the bracket/tail/no-interior-boundary
    oracles and closes the loop.  Verified-but-unconsumed (R225): references no sorry site, frontier
    sorry count unchanged at 4; axiom-clean `[propext, Classical.choice, Quot.sound]` (the
    `Classical.choice` enters through `recmappair_window`'s reused ADVANCE segment-split plumbing). -/
theorem recmapentry_classify (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo_hi : lo < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_head :
      tokens[lo]!.val = .key ∧
      ∃ kv e, lo < kv ∧ kv < e ∧ e ≤ hi ∧
        tokens[kv]!.val = .value ∧
        RecSeqEntry ((tokens.toList.take kv).drop (lo + 1)) ∧
        RecSeqEntry ((tokens.toList.take e).drop (kv + 1)) ∧
        flowBracketBalance tokens lo e = 0 ∧
        (e = hi ∨ tokens[e]!.val = .flowEntry) ∧
        (∀ k, lo < k → k < e →
          ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry)))) :
    ∃ m, lo < m ∧ m ≤ hi ∧
      flowBracketBalance tokens lo m = 0 ∧
      (m = hi ∨ tokens[m]!.val = .flowEntry) ∧
      (∀ k, lo < k → k < m →
        ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry))) ∧
      RecMapPair ((tokens.toList.take m).drop lo) := by
  obtain ⟨m, h_lo_m, h_m_hi, h_m_bal, h_m_marker, h_m_least⟩ :=
    firstEntryBoundary tokens lo hi h_lo_hi h_total
  obtain ⟨h_key, kv, e, h_lo_kv, h_kv_e, h_e_hi, h_value, h_ke, h_ve, h_e_bal, h_e_marker, h_e_least⟩ :=
    h_head
  -- Pin the two split points: `firstEntryBoundary`'s least boundary `m` and the substrate's pair end
  -- `e` are mutually `≤` (each is a boundary the other's minimality clause forbids strictly inside).
  have h_m_e : m = e := by
    rcases Nat.lt_trichotomy m e with h | h | h
    · exact absurd ⟨h_m_bal, h_m_marker⟩ (h_e_least m h_lo_m h)
    · exact h
    · exact absurd ⟨h_e_bal, h_e_marker⟩ (h_m_least e (by omega) h)
  refine ⟨m, h_lo_m, h_m_hi, h_m_bal, h_m_marker, h_m_least, ?_⟩
  rw [h_m_e]
  exact recmappair_window tokens lo kv e h_lo_kv h_kv_e (by omega) h_key h_value h_ke h_ve

/-- **Head-derived nested-sequence bracket classify** (Phase J — the seq locate DRIVER's bracket
    disjunct with its split point `j` DERIVED from the head, no longer assumed).  `recseqentry_classify`
    (R281) folds the four head-dispatches but still ASSUMES, in each of its two bracket disjuncts, an
    `∃ j, …` carrying the matching close `j` and its position / close-token / inner-balance / positivity
    facts.  Those facts are exactly what the close-locator `matchingClose_full_seq` (R277) PRODUCES from
    the head alone — opener `tokens[lo]! = .flowSequenceStart`, total balance `0`, Dyck prefixes, and the
    window `WellTyped`.  This lemma folds that locator INTO the nested-sequence disjunct: it runs the
    locator to fix `j` *with* its full fact bundle, then hands that to `recseqentry_classify`'s fourth
    disjunct.  The split point is now an internal consequence of the head, not a substrate parameter.

    The genuinely new shape is the *oracle* hypothesis `h_oracle`, and it is a textbook instance of the
    producer-guarded quantifier (cf. [[ref-producer-guarded-quantifier]]).  Two facts the bracket
    disjunct needs — the recursive interior body `RecSeqBody ((take j).drop (lo+1))` and the trailing
    separator `h_succ` — depend on the located `j`, which does not exist until the locator runs *inside*
    this proof.  So they cannot be plain hypotheses about a known `j`; they must be a universal over `j`
    **guarded by exactly the locator's output predicate** (`lo < j`, `j < hi`, the close token, the inner
    balance, the strict-positivity invariant).  Carry that guard and the universal is dischargeable —
    apply it to the located `j` and its five facts.  Drop any guard conjunct and it becomes either too
    strong to supply (an unconditional `RecSeqBody` for every `j`) or unpinnable: the guard is what lets
    the driver supply the oracle ONLY at the unique matching close, where its recursion has run.  This is
    why folding the close-locator is not free book-keeping but a real interface move — it converts the
    assumed-`j` substrate into a head-only substrate at the cost of guarding the residual oracle.

    With this, the seq DRIVER's per-bracket-window obligation is head-only except for the guarded oracle,
    which the `Nat.strongRecOn` width-metric driver discharges from its recursive call on the strictly
    smaller interior `[lo+1, j)`.  Verified-but-unconsumed (R225): references no sorry site, frontier
    sorry count unchanged at 4; axiom-clean `[propext, Classical.choice, Quot.sound]` (`Classical.choice`
    enters through `matchingClose_full_seq`'s `flowBracketBalance_matching_close` and the bracket
    dispatch's `firstEntryBoundary_bracket_resolve` compose machinery). -/
theorem recseqentry_seqbracket_located (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo_hi : lo < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_open : tokens[lo]!.val = .flowSequenceStart)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo))
    (h_oracle : ∀ j, lo < j → j < hi → tokens[j]!.val = .flowSequenceEnd →
        flowBracketBalance tokens (lo + 1) j = 0 →
        (∀ i, lo < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) →
        RecSeqBody ((tokens.toList.take j).drop (lo + 1)) ∧
        (j + 1 = hi ∨ tokens[j + 1]!.val = .flowEntry)) :
    ∃ m, lo < m ∧ m ≤ hi ∧
      flowBracketBalance tokens lo m = 0 ∧
      (m = hi ∨ tokens[m]!.val = .flowEntry) ∧
      (∀ k, lo < k → k < m →
        ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry))) ∧
      RecSeqEntry ((tokens.toList.take m).drop lo) := by
  obtain ⟨j, h_lo_j, h_j_hi, h_close, h_inner, h_pos⟩ :=
    matchingClose_full_seq tokens lo hi h_lo_hi h_hi_sz h_open h_total h_dyck h_wt
  obtain ⟨h_rec, h_succ⟩ := h_oracle j h_lo_j h_j_hi h_close h_inner h_pos
  exact recseqentry_classify tokens lo hi h_lo_hi h_hi_sz h_total
    (Or.inr (Or.inr (Or.inr ⟨j, h_open, h_lo_j, h_j_hi, h_close, h_inner, h_pos, h_rec, h_succ⟩)))

/-- **Head-derived nested-mapping bracket classify** (Phase J — the seq locate DRIVER's *near-leaf*
    bracket disjunct, the `{ … }` mirror of `recseqentry_seqbracket_located`).  Verbatim sibling over the
    `.flowMapping{Start,End}` close token: folds the map close-locator `matchingClose_full_map` (R277)
    into `recseqentry_classify`'s THIRD disjunct, deriving the matching close `j` from the head opener
    `tokens[lo]! = .flowMappingStart` + window facts, then handing the full bundle to the classify.

    The lone structural difference from the seq sibling is the R244 storage fact surfacing in the guarded
    oracle: a nested mapping is a NEAR-leaf (`RecSeqEntry.map` stores only the interior `WellBracketed`,
    not a recursive body), so `h_oracle` returns `WellBracketed ((take j).drop (lo+1))` rather than the
    recursive `RecSeqBody`.  The producer-guarded-quantifier shape is identical (cf.
    [[ref-producer-guarded-quantifier]]): the trailing separator `h_succ` still depends on the located
    `j`, so the oracle must be guarded by the locator's output predicate even though the body fact is
    flat-decidable.  This confirms the close-locator fold is a structural interface move independent of
    whether the interior is recursive — the guard is forced by the *separator's* `j`-dependence, present
    on both bracket branches.  Verified-but-unconsumed (R225): references no sorry site, frontier sorry
    count unchanged at 4; axiom-clean `[propext, Classical.choice, Quot.sound]` (`Classical.choice` via
    `matchingClose_full_map` / the map dispatch's resolve machinery). -/
theorem recseqentry_mapbracket_located (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo_hi : lo < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_open : tokens[lo]!.val = .flowMappingStart)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo))
    (h_oracle : ∀ j, lo < j → j < hi → tokens[j]!.val = .flowMappingEnd →
        flowBracketBalance tokens (lo + 1) j = 0 →
        (∀ i, lo < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) →
        WellBracketed ((tokens.toList.take j).drop (lo + 1)) ∧
        (j + 1 = hi ∨ tokens[j + 1]!.val = .flowEntry)) :
    ∃ m, lo < m ∧ m ≤ hi ∧
      flowBracketBalance tokens lo m = 0 ∧
      (m = hi ∨ tokens[m]!.val = .flowEntry) ∧
      (∀ k, lo < k → k < m →
        ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry))) ∧
      RecSeqEntry ((tokens.toList.take m).drop lo) := by
  obtain ⟨j, h_lo_j, h_j_hi, h_close, h_inner, h_pos⟩ :=
    matchingClose_full_map tokens lo hi h_lo_hi h_hi_sz h_open h_total h_dyck h_wt
  obtain ⟨h_wb, h_succ⟩ := h_oracle j h_lo_j h_j_hi h_close h_inner h_pos
  exact recseqentry_classify tokens lo hi h_lo_hi h_hi_sz h_total
    (Or.inr (Or.inr (Or.inl ⟨j, h_open, h_lo_j, h_j_hi, h_close, h_inner, h_pos, h_wb, h_succ⟩)))

/-- **Head-shape dispatch — the per-window first-`RecSeqEntry` producer** (Phase J — sub-brick (i-c),
    the case-split assembly that routes the body window's head into the unified located first entry).
    Given a body window `[lo, hi)` carrying both shared guards (`FlowBodyWindow` + the deep content
    guard `FlowBodyContentDeep` + its entry-level projection `FlowBodyContent`) and the
    `windowWidth_strongRecOn` IH, this reads the head shape off `FlowBodyContent.headContentStart` and
    produces the located first entry — the same `∃ m, … ∧ RecSeqEntry ((take m).drop lo)` conclusion the
    four `recseqentry_*` located/classify forms deliver, now with the head shape DISPATCHED rather than
    assumed.  It is the inverse of `recseqentry_classify`: where classify CONSUMES a four-way `h_head`
    disjunction, this PRODUCES the appropriate disjunct from the guards and routes it.

    The dispatch reads the head as one of `isFlowContentStart`'s THREE shapes — scalar / `[` / `{` — not
    four: the empty-bracket leaf (`[ ]`) that `recseqentry_classify`'s second disjunct anticipates is
    *unreachable under the deep guard*.  `FlowBodyContentDeep.openerContentStart` asserts the token after
    any depth-`0` opener is content-start, so a `[`-headed entry never has `]` at `lo+1`; the empty case
    collapses into the nested-`[ … ]` branch, where the seq oracle discharges it vacuously (its
    interior-non-emptiness step derives the contradiction internally).  So the deep guard COLLAPSES the
    four-way head dispatch to three — the empty branch is not handled, it is excluded.

    * **scalar** — build `recseqentry_classify`'s scalar disjunct directly: the head is a scalar (delta
      `0`, so `balance lo (lo+1) = 0`) and its successor `h_succ` comes from `FlowBodyContent.bodySucc`
      at `lo` (a balanced non-`.flowEntry` prefix ends the entry).
    * **`[ … ]`** — route to `recseqentry_seqbracket_located`, feeding it the recursive oracle
      `recseqentry_seqbracket_oracle` (which draws its interior `RecSeqBody` from the IH).
    * **`{ … }`** — route to `recseqentry_mapbracket_located`, feeding it the near-leaf oracle
      `recseqentry_mapbracket_oracle` (interior `WellBracketed`, no IH).

    This is the genuine remaining grammar glue the 141st-revision map flagged, now that both bracket
    oracles and all four located/dispatch forms exist.  It still consumes `FlowBodyContent` as a
    hypothesis (its `bodySucc` is the one field the threaded deep guard does not project — sub-brick
    (i') establishes its provenance).  Verified-but-unconsumed (R225): references no sorry site, frontier
    sorry count unchanged at 4; axiom-clean `[propext, Classical.choice, Quot.sound]` (via the routed
    located forms' close-locators / oracle balance machinery). -/
theorem recseqentry_window_dispatch (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_window : FlowBodyWindow tokens lo hi)
    (h_deep : FlowBodyContentDeep tokens lo hi)
    (h_content : FlowBodyContent tokens lo hi)
    (Q : Nat → Prop) (h_q_descend : tokens[lo]!.val = .flowSequenceStart → Q (lo + 1))
    (h_ih : ∀ lo' hi', hi' - lo' < hi - lo →
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' → Q lo' →
        tokens[hi']!.val = .flowSequenceEnd →
        RecSeqBody ((tokens.toList.take hi').drop lo')) :
    ∃ m, lo < m ∧ m ≤ hi ∧
      flowBracketBalance tokens lo m = 0 ∧
      (m = hi ∨ tokens[m]!.val = .flowEntry) ∧
      (∀ k, lo < k → k < m →
        ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry))) ∧
      RecSeqEntry ((tokens.toList.take m).drop lo) := by
  have h_lo_hi : lo < hi := h_window.lo_lt_hi
  have h_total : flowBracketBalance tokens lo hi = 0 := h_window.balanced
  have h_dyck := h_window.dyck
  have h_wt := h_window.wellTyped
  have h_hi_sz : hi ≤ tokens.size := Nat.le_of_lt h_window.hi_lt
  have h_lo_sz : lo < tokens.size := by omega
  have h_head_cs : isFlowContentStart tokens[lo]!.val := h_content.headContentStart
  unfold isFlowContentStart at h_head_cs
  rcases h_head_cs with ⟨c, s, hcs⟩ | h_open | h_open
  · -- scalar leaf: delta `0`, successor from `bodySucc`, fed to `recseqentry_classify`'s first disjunct.
    have h_lo_len : lo < tokens.toList.length := by rw [Array.length_toList]; exact h_lo_sz
    have h_val : (tokens.toList[lo]'h_lo_len).val = .scalar c s := by
      have hb : tokens[lo]! = tokens.toList[lo]'h_lo_len := by
        rw [getElem!_pos tokens lo h_lo_sz, Array.getElem_toList]
      rw [← hb]; exact hcs
    have h_bal1 : flowBracketBalance tokens lo (lo + 1) = 0 := by
      rw [flowBracketBalance_single tokens lo h_lo_len, h_val, flowBracketDelta_scalar]
    have h_ne_fe : tokens[lo]!.val ≠ .flowEntry := by rw [hcs]; intro h; cases h
    have h_succ : lo + 1 = hi ∨ tokens[lo + 1]!.val = .flowEntry := by
      rcases h_content.bodySucc lo (Nat.le_refl lo) h_lo_hi h_bal1 h_ne_fe with h | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr h
    exact recseqentry_classify tokens lo hi h_lo_hi h_hi_sz h_total
      (Or.inl ⟨⟨c, s, hcs⟩, h_succ⟩)
  · -- nested sequence `[ … ]` (empty `[]` excluded by the deep guard, handled inside the seq oracle).
    exact recseqentry_seqbracket_located tokens lo hi h_lo_hi h_hi_sz h_open h_total h_dyck h_wt
      (recseqentry_seqbracket_oracle tokens lo hi h_window h_deep h_content h_open
        Q (h_q_descend h_open) h_ih)
  · -- nested mapping `{ … }`: the near-leaf oracle, no IH.
    exact recseqentry_mapbracket_located tokens lo hi h_lo_hi h_hi_sz h_open h_total h_dyck h_wt
      (recseqentry_mapbracket_oracle tokens lo hi h_window h_content h_open)

/-- **Head-derived map-pair classify** (Phase J — the map locate DRIVER's pair classify with its two
    `RecSeqEntry` sub-blocks DERIVED from per-sub-window oracles rather than assumed whole).  The map
    mirror of `recseqentry_seqbracket_located` (R283), and the mirror is *asymmetric* in a way that
    sharpens the producer-guarded-quantifier lesson.

    On the seq side R283 folded the close-locator `matchingClose_full_seq` (R277) so the bracket's
    matching close `j` is DERIVED from the head opener + window facts — a balance-pure locator runs
    *inside* the proof, and the only residual is a guarded oracle for the witness-dependent interior +
    separator.  The map pair has no such derivable position.  A pair `.key K .value V` returns balance
    to `0` at the depth-0 `.value` separator `kv` — but ALSO at every nested-entry end inside `K` and
    `V`; only the *token* at `kv` being `.value` distinguishes it (R282).  So there is no balance-pure
    `.value`-locator to run, and the `kv`/`e` skeleton (the depth-0 value separator and the pair end,
    with their balance / marker / minimality facts) must be SUPPLIED as a hypothesis `h_skeleton`,
    exactly the directly-supplied conjunct R282 named.

    What still moves across the interface is the heavy half: the pair's two `RecSeqEntry` sub-blocks —
    the key block `[lo+1, kv)` and the value block `[kv+1, e)`.  Each is delivered by a guarded oracle
    (`h_key_oracle` / `h_val_oracle` — the "two sub-block locators"), a universal over `kv`/`e`
    **guarded by exactly the skeleton's located-position predicate**, discharged by the `Nat.strongRecOn`
    driver's recursive call on the strictly-smaller sub-window.  This is [[ref-producer-guarded-quantifier]]
    on the map axis: the two `RecSeqEntry`s are witness-dependent on `kv`/`e`, which are not named at the
    call site (they live under `h_skeleton`'s `∃`), so they cannot be plain hypotheses — they must be
    guarded universals the proof instantiates at the obtained `kv`/`e`.

    The lesson (R284): the close-locator fold has TWO separable halves — the POSITION half (where the
    sub-blocks split) and the SUB-DELIVERABLE half (the `RecSeqEntry`s themselves).  The position half is
    balance-derivable on the seq axis (run the locator) but only SUPPLIABLE on the map axis (R282 — the
    `.value` separator is balance-invisible); the sub-deliverable half is a producer-guarded oracle on
    BOTH axes.  So the producer-guarded-quantifier pattern governs the witness-dependent sub-deliverable
    regardless of whether its split position is derivable — the map fold derives strictly less than the
    seq fold (positions stay assumed) yet guards its residual identically.  Verified-but-unconsumed
    (R225): references no sorry site, frontier sorry count unchanged at 4; axiom-clean
    `[propext, Classical.choice, Quot.sound]` (via `recmapentry_classify`'s `recmappair_window` /
    `firstEntryBoundary` machinery). -/
theorem recmapentry_pair_located (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo_hi : lo < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_key : tokens[lo]!.val = .key)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_skeleton : ∃ kv e, lo < kv ∧ kv < e ∧ e ≤ hi ∧
      tokens[kv]!.val = .value ∧
      flowBracketBalance tokens lo e = 0 ∧
      (e = hi ∨ tokens[e]!.val = .flowEntry) ∧
      (∀ k, lo < k → k < e →
        ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry))))
    (h_key_oracle : ∀ kv e, lo < kv → kv < e → e ≤ hi → tokens[kv]!.val = .value →
      flowBracketBalance tokens lo e = 0 →
      (e = hi ∨ tokens[e]!.val = .flowEntry) →
      (∀ k, lo < k → k < e →
        ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry))) →
      RecSeqEntry ((tokens.toList.take kv).drop (lo + 1)))
    (h_val_oracle : ∀ kv e, lo < kv → kv < e → e ≤ hi → tokens[kv]!.val = .value →
      flowBracketBalance tokens lo e = 0 →
      (e = hi ∨ tokens[e]!.val = .flowEntry) →
      (∀ k, lo < k → k < e →
        ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry))) →
      RecSeqEntry ((tokens.toList.take e).drop (kv + 1))) :
    ∃ m, lo < m ∧ m ≤ hi ∧
      flowBracketBalance tokens lo m = 0 ∧
      (m = hi ∨ tokens[m]!.val = .flowEntry) ∧
      (∀ k, lo < k → k < m →
        ¬ (flowBracketBalance tokens lo k = 0 ∧ (k = hi ∨ tokens[k]!.val = .flowEntry))) ∧
      RecMapPair ((tokens.toList.take m).drop lo) := by
  obtain ⟨kv, e, h_lo_kv, h_kv_e, h_e_hi, h_value, h_e_bal, h_e_marker, h_e_least⟩ := h_skeleton
  have h_ke := h_key_oracle kv e h_lo_kv h_kv_e h_e_hi h_value h_e_bal h_e_marker h_e_least
  have h_ve := h_val_oracle kv e h_lo_kv h_kv_e h_e_hi h_value h_e_bal h_e_marker h_e_least
  exact recmapentry_classify tokens lo hi h_lo_hi h_hi_sz h_total
    ⟨h_key, kv, e, h_lo_kv, h_kv_e, h_e_hi, h_value, h_ke, h_ve, h_e_bal, h_e_marker, h_e_least⟩

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

/-- **Located-`RecMapBody` → `MapBodyProps` consumer joint** (Phase J, map side).  The map mirror of
    `seqBodyProps_of_recseqbody_window`: given a guarded balanced flow-MAPPING subrange `[lo, hi)`
    (close `.flowMappingEnd`, total balance `0`, Dyck prefixes, interior `WellTyped`) whose array
    window `(tokens.toList.take (hi+1)).drop lo` is a bracket entry's `interior ++ [cl]`, AND the
    map descent has handed back that `interior`'s recursive structure `RecMapBody interior`,
    assemble `MapBodyProps tokens lo hi`.

    The window identity `interior_window_eq` rewrites the structural `interior` into the positionally
    windowed `(tokens.toList.take hi).drop lo`, so `RecMapBody.toSafeBody` delivers exactly the
    windowed `SafeBody (· = .key)` that `mapBodyProps_of_windowed_safebody` consumes — closing the
    back half of the map descent-locator.  Unlike the seq mirror there is no `SafeBodyUnit` and no
    separate `content_start` input (M1 `key_start` comes from `SafeBody.head_Q` inside the windowed
    joint); but the six pair-INTERIOR primitives stay as inputs, because the `.key`-headed `SafeBody`
    only constrains the pair-BOUNDARY structure and the depth-0 `.value` alternation lives below its
    resolution (Reflection 232).  So this collapses the map back-half's `SafeBody` input into a
    `RecMapBody` input — the producer now only has to deliver one `RecMapBody`, exactly as the seq
    producer delivers one `RecSeqBody` — while honestly leaving the six interior primitives as the
    map's extra residual.  What remains upstream is the map *locate* (pair a guarded flow-mapping
    subrange's body window to the `RecMapBody` the map producer emits) plus those six primitives. -/
theorem mapBodyProps_of_recmapbody_window (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (interior : List (Positioned YamlToken)) (cl : Positioned YamlToken)
    (h_lo_hi : lo ≤ hi) (h_hi_sz : hi < tokens.size)
    (h_tpe : tokens[hi]!.val = .flowMappingEnd)
    (h_outer_bal : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt_interior : WellTyped ((tokens.toList.take hi).drop lo))
    (h_window : (tokens.toList.take (hi + 1)).drop lo = interior ++ [cl])
    (h_rec : RecMapBody interior)
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
  have h_eq : interior = (tokens.toList.take hi).drop lo :=
    interior_window_eq tokens lo hi interior cl h_lo_hi h_hi_sz h_window
  exact mapBodyProps_of_windowed_safebody tokens lo hi (Nat.le_of_lt h_hi_sz) h_tpe
    h_outer_bal h_dyck h_wt_interior (h_eq ▸ h_rec.toSafeBody)
    h_key_content h_key_scalar_value h_value_content h_value_scalar_succ
    h_key_bracket_succ h_value_bracket_succ

/-- **Located-entry → `MapBodyProps` consumer joint** (Phase J, map side — the descent-locator's
    FRONT-END consumer).  The map mirror of `seqBodyProps_of_located_entry` (Reflection 237): it
    consumes the descent-locator's raw, earliest output — `RecMapEntry` of the absolute opener-window
    `(tokens.toList.take (hi+1)).drop (lo-1)` of a guarded balanced flow-MAPPING subrange `[lo, hi)`
    — and assembles `MapBodyProps tokens lo hi`, adding no structural content beyond the same opener-
    peel coordinate arithmetic the seq front-end does:

    * **peel the opener** — `(take (hi+1)).drop (lo-1) = tokens[lo-1] :: (take (hi+1)).drop lo`
      (`List.getElem_cons_drop`, using `1 ≤ lo`);
    * **decompose the rest** — `(take (hi+1)).drop lo = (take hi).drop lo ++ [tokens[hi]]`
      (`List.take_add_one` + `List.drop_append_of_le_length`), exposing the interior window
      `(take hi).drop lo` and the closer `tokens[hi]`;
    * **descend** via `RecMapEntry.map_interior`: the non-empty disjunct `RecMapBody` feeds the back
      half `mapBodyProps_of_recmapbody_window`, the empty disjunct `interior = []` forces `lo = hi`
      (`List.length_drop`/`List.length_take`) and routes to the vacuous leaf `mapBodyProps_empty`.

    The two faithful-mirror asymmetries with the seq front-end (Reflections 232 / 241) reappear in
    the *signature*, not the proof: (a) NO `content_start` recovery and NO `h_open` — the map back-half
    recovers M1 `key_start` internally from `SafeBody.head_Q`, and the `RecMapEntry` type internalizes
    the `.flowMappingStart` opener guard, so the seq front-end's content-start plumbing and explicit
    opener hypothesis simply vanish; (b) the six pair-INTERIOR primitives stay as pass-through inputs,
    because the `.key`-headed `SafeBody` constrains only the pair BOUNDARY and the depth-0 `.value`
    alternation lives below its resolution (Reflection 232, load-bearing).  With this, the map-side
    Phase-J residual collapses to the pure *locate correspondence* — "for every guarded balanced
    flow-mapping subrange, its opener-window is a `RecMapEntry`" — plus those six primitives; no
    positional plumbing remains downstream of locate.  Completes the map consumer-joint family,
    symmetric to the seq side's back-half (R236) + front-end (R237) pair. -/
theorem mapBodyProps_of_located_entry (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi_sz : hi < tokens.size)
    (h_tpe : tokens[hi]!.val = .flowMappingEnd)
    (h_outer_bal : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt_interior : WellTyped ((tokens.toList.take hi).drop lo))
    (h_entry : RecMapEntry ((tokens.toList.take (hi + 1)).drop (lo - 1)))
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
  have h_hi_len : hi < tokens.toList.length := by rw [Array.length_toList]; exact h_hi_sz
  -- rest-decomposition: the `interior ++ [cl]` slice the back half is keyed on.
  have h_rest : (tokens.toList.take (hi + 1)).drop lo
      = (tokens.toList.take hi).drop lo ++ [tokens.toList[hi]] := by
    have h_ts : tokens.toList.take (hi + 1)
        = tokens.toList.take hi ++ [tokens.toList[hi]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem h_hi_len]; rfl
    rw [h_ts]
    have h_len : lo ≤ (tokens.toList.take hi).length := by rw [List.length_take]; omega
    rw [List.drop_append_of_le_length h_len]
  -- peel the opener: the opener-window is `tokens[lo-1] :: rest`.
  have h_peel : (tokens.toList.take (hi + 1)).drop (lo - 1)
      = tokens.toList[lo - 1]'(by rw [Array.length_toList]; omega)
        :: (tokens.toList.take (hi + 1)).drop lo := by
    have hlen : lo - 1 < (tokens.toList.take (hi + 1)).length := by
      rw [List.length_take]; omega
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take] at h
    rw [show lo - 1 + 1 = lo from by omega] at h
    exact h
  -- the located entry now reads as `op :: (interior_w ++ [cl])`.
  rw [h_peel, h_rest] at h_entry
  -- descend one nesting level (no opener guard — `RecMapEntry` internalizes it).
  rcases RecMapEntry.map_interior h_entry rfl with h_rec | h_empty
  · -- non-empty interior: feed the back half (M1 recovered internally there).
    exact mapBodyProps_of_recmapbody_window tokens lo hi ((tokens.toList.take hi).drop lo)
      tokens.toList[hi] h_lo_hi h_hi_sz h_tpe h_outer_bal h_dyck h_wt_interior h_rest h_rec
      h_key_content h_key_scalar_value h_value_content h_value_scalar_succ
      h_key_bracket_succ h_value_bracket_succ
  · -- empty interior: `(take hi).drop lo = []` forces `lo = hi`.
    have hlen_take : (tokens.toList.take hi).length = hi := by rw [List.length_take]; omega
    have hl : ((tokens.toList.take hi).drop lo).length
        = (tokens.toList.take hi).length - lo := List.length_drop
    rw [h_empty, hlen_take] at hl
    simp only [List.length_nil] at hl
    exact mapBodyProps_empty tokens lo hi (by omega)

/-- **Located-entry → inner-window `RecMapBody` descent** (Phase J, map side — the *navigation
    recursion's* per-level descent step; the symmetric map mirror of `recseqbody_window_of_located_entry`,
    R260, born one session later exactly as R255→R256 / R258→R259).  The array-window form of
    `RecMapEntry.map_interior`: given a guarded flow-MAPPING subrange `[lo, hi)` whose opener-window
    `(tokens.toList.take (hi+1)).drop (lo-1)` has been matched to a `RecMapEntry` (the map locate's
    per-window deliverable), descend ONE nesting level to the interior window's recursive structure:
    `RecMapBody ((tokens.toList.take hi).drop lo)` (the non-empty case) OR `lo = hi` (the empty `{}`
    case the no-`nil` `RecMapBody` structurally cannot represent — the Reflection 233 producer-contract
    split).

    This is the constructive *descent* counterpart of the consumer joint `mapBodyProps_of_located_entry`:
    that lemma runs the same opener-peel / rest-decomposition and then *consumes* the descended
    `RecMapBody` (via `mapBodyProps_of_recmapbody_window`) straight into the terminal `MapBodyProps`;
    this one *stops at the descended `RecMapBody`*, so the navigation recursion can take that
    inner-window body as the IH input one nesting level down.  Its non-empty disjunct
    `RecMapBody ((tokens.toList.take hi).drop lo)` is *exactly* the `flowSubrangesOk_of_window_producers`
    `h_map_rec` deliverable at a window that is itself a top-level nested-mapping entry — so once the
    locate matches a guarded subrange's opener-window to its `RecMapEntry`, this lemma finishes the
    map producer obligation at that window with no further structural work.

    The proof is the opener-peel (`List.getElem_cons_drop`, using `1 ≤ lo`) + rest-decomposition
    (`List.take_add_one` + `List.drop_append_of_le_length`) of `mapBodyProps_of_located_entry` run
    verbatim, terminated by `RecMapEntry.map_interior` (the empty disjunct forced to `lo = hi` by the
    `List.length_drop`/`List.length_take` length argument) instead of the back-half consumer.  Unlike
    its seq sibling it needs **no** `h_open` hypothesis and **no** `h_op_val` derivation — both
    `RecMapEntry` constructors are `{ … }` frames, so the entry *internalizes* the `.flowMappingStart`
    opener guard `RecSeqEntry.seq_interior` needed supplied externally (R244/R246 storage asymmetry,
    here a *dropped* hypothesis: the map descend mirror is one hypothesis shorter than the seq one).
    Verified-but-unconsumed (R225): references no sorry site, frontier sorry count unchanged. -/
theorem recmapbody_window_of_located_entry (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi_sz : hi < tokens.size)
    (h_entry : RecMapEntry ((tokens.toList.take (hi + 1)).drop (lo - 1))) :
    RecMapBody ((tokens.toList.take hi).drop lo) ∨ lo = hi := by
  have h_hi_len : hi < tokens.toList.length := by rw [Array.length_toList]; exact h_hi_sz
  -- rest-decomposition: the `interior ++ [cl]` slice the descent is keyed on.
  have h_rest : (tokens.toList.take (hi + 1)).drop lo
      = (tokens.toList.take hi).drop lo ++ [tokens.toList[hi]] := by
    have h_ts : tokens.toList.take (hi + 1)
        = tokens.toList.take hi ++ [tokens.toList[hi]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem h_hi_len]; rfl
    rw [h_ts]
    have h_len : lo ≤ (tokens.toList.take hi).length := by rw [List.length_take]; omega
    rw [List.drop_append_of_le_length h_len]
  -- peel the opener: the opener-window is `tokens[lo-1] :: rest`.
  have h_peel : (tokens.toList.take (hi + 1)).drop (lo - 1)
      = tokens.toList[lo - 1]'(by rw [Array.length_toList]; omega)
        :: (tokens.toList.take (hi + 1)).drop lo := by
    have hlen : lo - 1 < (tokens.toList.take (hi + 1)).length := by
      rw [List.length_take]; omega
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take] at h
    rw [show lo - 1 + 1 = lo from by omega] at h
    exact h
  -- the located entry now reads as `op :: (interior_w ++ [cl])`.
  rw [h_peel, h_rest] at h_entry
  -- descend one nesting level via the array-window form of `map_interior` (no opener guard —
  -- `RecMapEntry` internalizes the `.flowMappingStart` guard, so no `h_open`/`h_op_val` needed).
  rcases RecMapEntry.map_interior h_entry rfl with h_rec | h_empty
  · left; exact h_rec
  · -- empty interior: `(take hi).drop lo = []` forces `lo = hi`.
    right
    have hlen_take : (tokens.toList.take hi).length = hi := by rw [List.length_take]; omega
    have hl : ((tokens.toList.take hi).drop lo).length
        = (tokens.toList.take hi).length - lo := List.length_drop
    rw [h_empty, hlen_take] at hl
    simp only [List.length_nil] at hl
    omega

/-- **Located map-entry producer** (Phase J, map side — the constructive dual of
    `mapBodyProps_of_located_entry`, the symmetric mirror of `located_entry_of_recseqbody`).  Given
    the inner-window `RecMapBody ((take hi).drop lo)` — the map locate's recursive deliverable one
    nesting level down — plus the opener `tokens[lo-1] = .flowMappingStart` and closer
    `tokens[hi] = .flowMappingEnd`, *build* the located `RecMapEntry ((take (hi+1)).drop (lo-1))` of
    the opener-window — exactly the `MapLocated.entry` field the locate must deliver at this level.

    Same positional slicing as the consumer `mapBodyProps_of_located_entry` (rest-decomposition
    `h_rest` + opener peel `h_peel`, copied verbatim), run in the opposite direction: where the
    consumer rewrites the located entry into `op :: (interior ++ [cl])` shape and `map_interior`-descends
    (the eliminator), this rewrites the *target* into that shape and applies `RecMapEntry.map` (the
    constructor).  Unlike the seq mirror `located_entry_of_recseqbody`, `RecMapEntry.map` stores **no**
    `WellBracketed interior` field — the map entry's balance is recovered post-hoc by the projection
    `RecMapEntry.toWellBracketed` (R242/R244), so the constructor takes only the opener/closer facts
    and the recursive `RecMapBody`.  Effect: reduces the map-side `MapLocated.entry` obligation from
    "produce the located entry" to "produce the inner-window `RecMapBody`", the exact recursive
    deliverable the map locate descends on (its six pair-interior primitives and `pos`/`dyck`/`wt`
    fields are supplied separately, not by this entry assembler).  See Reflection 245. -/
theorem located_mapentry_of_recmapbody (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi_sz : hi < tokens.size)
    (h_open : tokens[lo - 1]!.val = .flowMappingStart)
    (h_close : tokens[hi]!.val = .flowMappingEnd)
    (h_rec : RecMapBody ((tokens.toList.take hi).drop lo)) :
    RecMapEntry ((tokens.toList.take (hi + 1)).drop (lo - 1)) := by
  have h_hi_len : hi < tokens.toList.length := by rw [Array.length_toList]; exact h_hi_sz
  have h_lo1_sz : lo - 1 < tokens.size := by omega
  -- rest-decomposition: the `interior ++ [cl]` tail (mirrors `mapBodyProps_of_located_entry`).
  have h_rest : (tokens.toList.take (hi + 1)).drop lo
      = (tokens.toList.take hi).drop lo ++ [tokens.toList[hi]] := by
    have h_ts : tokens.toList.take (hi + 1)
        = tokens.toList.take hi ++ [tokens.toList[hi]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem h_hi_len]; rfl
    rw [h_ts]
    have h_len : lo ≤ (tokens.toList.take hi).length := by rw [List.length_take]; omega
    rw [List.drop_append_of_le_length h_len]
  -- peel the opener: the opener-window is `tokens[lo-1] :: rest`.
  have h_peel : (tokens.toList.take (hi + 1)).drop (lo - 1)
      = tokens.toList[lo - 1]'(by rw [Array.length_toList]; omega)
        :: (tokens.toList.take (hi + 1)).drop lo := by
    have hlen : lo - 1 < (tokens.toList.take (hi + 1)).length := by
      rw [List.length_take]; omega
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take] at h
    rw [show lo - 1 + 1 = lo from by omega] at h
    exact h
  -- target window now reads as `op :: (interior ++ [cl])`.
  rw [h_peel, h_rest]
  have h_op_val : (tokens.toList[lo - 1]'(by rw [Array.length_toList]; omega)).val
      = .flowMappingStart := by
    have hb : tokens[lo - 1]! = tokens.toList[lo - 1]'(by rw [Array.length_toList]; omega) := by
      rw [getElem!_pos tokens (lo - 1) h_lo1_sz, Array.getElem_toList]
    rw [← hb]; exact h_open
  have h_cl_val : (tokens.toList[hi]'h_hi_len).val = .flowMappingEnd := by
    have hb : tokens[hi]! = tokens.toList[hi]'h_hi_len := by
      rw [getElem!_pos tokens hi h_hi_sz, Array.getElem_toList]
    rw [← hb]; exact h_close
  exact RecMapEntry.map _ _ _ h_op_val h_cl_val h_rec

/-! ### Locate deliverables and the `FlowSubrangesOk` assembler (Phase J — locate consumer joint)

The two `*_of_located_entry` joints above reduce, per guarded window, "produce `SeqBodyProps`/
`MapBodyProps`" to "the opener-window is a `RecSeqEntry`/`RecMapEntry`" (plus, on the map side, the
six pair-interior primitives).  What still separates them from the `FlowSubrangesOk tokens` the two
`scanFiltered_emit{Seq,Map}_nonempty_structure` sorry sites consume is the *universal packaging*:
`FlowSubrangesOk` quantifies over **all** `lo hi` with the bracket guards, and each field must also
supply the joint's `1 ≤ lo` / Dyck / `WellTyped` inputs, which the field's own hypotheses do not
carry.

`SeqLocated`/`MapLocated` name the **locate recursion's per-window deliverable** as a bundled type:
exactly the joint inputs the field does not provide (`1 ≤ lo`, the Dyck floor, the windowed
`WellTyped`, the located `Rec{Seq,Map}Entry`, and — map only — the six pair-interior primitives).
These ARE the future locate's intended return types.  Building their consumer NOW — the
`FlowSubrangesOk` assembler — is the consumer-joint-before-producer move (Reflection 231 family) at
the final structural boundary: it costs nothing (the per-window joints already exist), cannot regress
(fully proven, standalone, does not touch the sorry sites), and collapses the entire residual
downstream of locate — both sorry sites, both fields — into the single typed obligation "produce the
two locators."  After this the whole Phase-J residual is just: the locate recursion delivering
`SeqLocated`/`MapLocated` at every guarded window (fed by the emit-producer's top-level
`RecSeqBody`/`RecMapBody`). -/

/-- **Seq-side locate deliverable.**  The per-window output the seq locate must produce at a guarded
    balanced flow-SEQUENCE subrange `[lo, hi)` — precisely the inputs `seqBodyProps_of_located_entry`
    needs beyond the `FlowSubrangesOk.seq` field's own bracket guards. -/
structure SeqLocated (tokens : Array (Positioned YamlToken)) (lo hi : Nat) : Prop where
  pos : 1 ≤ lo
  dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0
  wt : WellTyped ((tokens.toList.take hi).drop lo)
  entry : RecSeqEntry ((tokens.toList.take (hi + 1)).drop (lo - 1))

/-- **Map-side locate deliverable.**  The map mirror of `SeqLocated`: the per-window output the map
    locate must produce at a guarded balanced flow-MAPPING subrange `[lo, hi)`, bundling the located
    `RecMapEntry` together with the six pair-interior primitives `mapBodyProps_of_located_entry`
    threads through (the load-bearing depth-0 `.value` alternation below the `.key`-headed
    `SafeBody`'s resolution, Reflection 232). -/
structure MapLocated (tokens : Array (Positioned YamlToken)) (lo hi : Nat) : Prop where
  pos : 1 ≤ lo
  dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0
  wt : WellTyped ((tokens.toList.take hi).drop lo)
  entry : RecMapEntry ((tokens.toList.take (hi + 1)).drop (lo - 1))
  key_content : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .key →
    k + 1 < hi ∧ isFlowContentStart tokens[k + 1]!.val
  key_scalar_value : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .key →
    (∃ c s, tokens[k + 1]!.val = .scalar c s) →
    k + 2 < hi ∧ tokens[k + 2]!.val = .value
  value_content : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .value →
    k + 1 < hi ∧ isFlowContentStart tokens[k + 1]!.val
  value_scalar_succ : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .value →
    (∃ c s, tokens[k + 1]!.val = .scalar c s) →
    k + 2 ≤ hi ∧
    (tokens[k + 2]!.val = .flowEntry ∨
     (tokens[k + 2]!.val = .flowMappingEnd ∧ k + 2 = hi))
  key_bracket_succ : ∀ k j, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .key →
    k + 1 < j → j < hi →
    flowBracketDelta tokens[j]!.val = -1 →
    flowBracketBalance tokens lo (j + 1) = 0 →
    j + 1 < hi ∧ tokens[j + 1]!.val = .value
  value_bracket_succ : ∀ k j, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .value →
    k + 1 < j → j < hi →
    flowBracketDelta tokens[j]!.val = -1 →
    flowBracketBalance tokens lo (j + 1) = 0 →
    j + 1 ≤ hi ∧
    (tokens[j + 1]!.val = .flowEntry ∨
     (tokens[j + 1]!.val = .flowMappingEnd ∧ j + 1 = hi))

/-- **The per-window Dyck floor is a free projection of the inner-window structure** (Phase J — the
    locate's `dyck` field is not a threaded invariant but a projection of the recursive deliverable).
    `WellBracketed l` is *definitionally* `pbalance l = 0 ∧ ∀ i, pbalance (l.take i) ≥ 0`, and its
    second conjunct — every prefix balance of the inner-window list is `≥ 0` — is, position-for-position
    via `flowBracketBalance_eq_pbalance`, exactly the `SeqLocated`/`MapLocated` `dyck` field
    `∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0`.  So once the locate has produced the
    inner-window `RecSeqBody`/`RecMapBody`, its `WellBracketed` projection
    (`RecSeqBody.toWellBracketed` / `RecMapBody.toWellBracketed`) *hands back the windowed Dyck for
    free*: the locate need not separately establish or thread a local Dyck floor at each window.  This
    is the R244 stored-vs-projected split surfacing at the locate's invariant set: of the three
    invariants the locate was thought to maintain (`1 ≤ lo`, Dyck, `WellTyped`), the Dyck one collapses
    into the deliverable because `WellBracketed` *is* projected from `Rec…Body`, whereas `WellTyped`
    stays a threaded hypothesis because it is *not* (only positionally recoverable via
    `WellTyped_subrange`).  The slice identity is the same `drop_take`/`take_take`/`min` rewrite the
    `WellTyped_subrange` Dyck bridge uses. -/
theorem dyck_of_wellBracketed_window (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_wb : WellBracketed ((tokens.toList.take hi).drop lo)) :
    ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0 := by
  intro i h_lo_i h_i_hi
  rw [flowBracketBalance_eq_pbalance tokens lo i h_lo_i]
  have h_slice : ((tokens.toList.take hi).drop lo).take (i - lo)
      = (tokens.toList.drop lo).take (i - lo) := by
    rw [List.drop_take, List.take_take, show min (i - lo) (hi - lo) = i - lo from by omega]
  rw [← h_slice]
  exact h_wb.2 (i - lo)

/-- **Seq-side locate bundle assembler** (Phase J — the producer-dual lifted to the bundled
    deliverable).  Where `located_entry_of_recseqbody` (Reflection 245) builds only the single
    recursive `entry` field, this packages the *whole* `SeqLocated tokens lo hi` bundle the locate
    consumer joint `flowSubrangesOk_of_locators` actually demands: the `entry` field via the entry
    assembler, the `dyck` field as a *free projection* of the recursive deliverable
    (`dyck_of_wellBracketed_window` on `h_rec.toWellBracketed` — no separate Dyck hypothesis needed),
    and the remaining `pos`/`wt` fields as direct pass-throughs.  It is the last mile between the
    producer-dual and the consumer joint — before it, the entry assembler delivered one of
    `SeqLocated`'s four fields, leaving an arity gap between what the dual produces (a `RecSeqEntry`) and
    what the joint's `h_seq` hypothesis demands (the four-field bundle); after it, the seq locator
    hypothesis is reduced to producing exactly the inner-window `RecSeqBody` (the recursion's deliverable
    one nesting level down) plus the threaded `WellTyped` (the lone non-projectable invariant, recovered
    positionally via `WellTyped_subrange`).  Every field is a pass-through or a structure-projection
    except `entry`, so the bundle's residual collapses to precisely the
    recursive sub-deliverable — the producer-side mirror of `flowSubrangesOk_of_locators` reducing the
    consumer residual to the locator hypotheses.  Verified-but-unconsumed until the locate lands: it
    references no sorry site, so the frontier sorry count is unchanged.  (The map mirror
    `mapLocated_of_recmapbody` additionally threads the six pair-interior primitives `MapLocated`
    stores but `located_mapentry_of_recmapbody` does not produce — the storage asymmetry of Reflection
    246 reappearing at the bundle level.) -/
theorem seqLocated_of_recseqbody (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi_sz : hi < tokens.size)
    (h_open : tokens[lo - 1]!.val = .flowSequenceStart)
    (h_close : tokens[hi]!.val = .flowSequenceEnd)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo))
    (h_rec : RecSeqBody ((tokens.toList.take hi).drop lo)) :
    SeqLocated tokens lo hi :=
  ⟨h_lo, dyck_of_wellBracketed_window tokens lo hi h_rec.toWellBracketed, h_wt,
    located_entry_of_recseqbody tokens lo hi h_lo h_lo_hi h_hi_sz h_open h_close h_rec⟩

/-- **Map-side locate bundle assembler** (Phase J — the symmetric mirror of `seqLocated_of_recseqbody`,
    Reflection 247).  Packages the whole `MapLocated tokens lo hi` bundle the consumer joint
    `flowSubrangesOk_of_locators` demands on the map side: the recursive `entry` field via the entry
    assembler `located_mapentry_of_recmapbody`, the `dyck` field as a free projection of the recursive
    deliverable (`dyck_of_wellBracketed_window` on `h_rec.toWellBracketed`, no Dyck hypothesis), and
    `pos`/`wt` as direct pass-throughs — exactly as the seq mirror.  Where it is **not** as clean as the seq side (R246's
    storage asymmetry, now at the bundle's field count): `MapLocated` STORES six pair-interior
    primitives (`key_content` … `value_bracket_succ`, the depth-0 `.key`/`.value` alternation of
    Reflection 232) that `located_mapentry_of_recmapbody` does NOT produce — the entry assembler
    delivers only the recursive `RecMapEntry`.  So this assembler threads those six as further
    hypotheses (the seq bundle has none), and its hypothesis count exceeds the seq bundle's by exactly
    the bundled-type-stores-minus-entry-producer-delivers — the projected-not-produced primitives.
    Effect: reduces the map locator hypothesis of `flowSubrangesOk_of_locators` to producing the
    inner-window `RecMapBody` (the recursive deliverable) plus those six primitives (carried by the
    enclosing locate from its own window guards, not regenerated here).  Verified-but-unconsumed until
    the locate lands: references no sorry site, frontier sorry count unchanged. -/
theorem mapLocated_of_recmapbody (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi_sz : hi < tokens.size)
    (h_open : tokens[lo - 1]!.val = .flowMappingStart)
    (h_close : tokens[hi]!.val = .flowMappingEnd)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo))
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
       (tokens[j + 1]!.val = .flowMappingEnd ∧ j + 1 = hi)))
    (h_rec : RecMapBody ((tokens.toList.take hi).drop lo)) :
    MapLocated tokens lo hi :=
  ⟨h_lo, dyck_of_wellBracketed_window tokens lo hi h_rec.toWellBracketed, h_wt,
    located_mapentry_of_recmapbody tokens lo hi h_lo h_lo_hi h_hi_sz h_open h_close h_rec,
    h_key_content, h_key_scalar_value, h_value_content, h_value_scalar_succ,
    h_key_bracket_succ, h_value_bracket_succ⟩

/-- **Seq-side outer locate bundle assembler** (Phase J — Reflection 254, the WellTyped sibling of
    Reflection 253's Dyck collapse).  Just as the per-window `dyck` field is a *free projection* of
    the window's own `RecSeqBody` (`dyck_of_wellBracketed_window` on `h_rec.toWellBracketed`), the
    per-window `wt` field is **recoverable from the OUTER-span `WellTyped`** via `WellTyped_subrange`
    — fed by the window's free balance (`h_rec.toWellBracketed.1`) and free Dyck (the same R253
    projection).  So `wt` is *not* a per-window deliverable either: the locate threads a single outer
    `WellTyped ((take HI).drop LO)` once and recovers each window's `WellTyped` here.  This is the
    exact per-window call shape the locate makes — supply the window's `RecSeqBody` and the
    positional guards (`LO ≤ lo`, `1 ≤ lo`, `lo ≤ hi`, `hi ≤ HI`, openers/closers), and the bundle
    assembles itself.  Its per-window NEW deliverable collapses to exactly `{RecSeqBody}` (pos a
    guard, Dyck free, WellTyped recovered-from-outer).  Verified-but-unconsumed until the locate
    lands: composes only existing lemmas, references no sorry site, frontier sorry count unchanged. -/
theorem seqLocated_of_recseqbody_outer (tokens : Array (Positioned YamlToken))
    (LO HI lo hi : Nat)
    (h_LO_lo : LO ≤ lo) (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi_HI : hi ≤ HI)
    (h_HI_sz : HI ≤ tokens.size) (h_hi_sz : hi < tokens.size)
    (h_open : tokens[lo - 1]!.val = .flowSequenceStart)
    (h_close : tokens[hi]!.val = .flowSequenceEnd)
    (h_wt_outer : WellTyped ((tokens.toList.take HI).drop LO))
    (h_rec : RecSeqBody ((tokens.toList.take hi).drop lo)) :
    SeqLocated tokens lo hi := by
  have h_wb := h_rec.toWellBracketed
  have h_dyck := dyck_of_wellBracketed_window tokens lo hi h_wb
  have h_slice : (tokens.toList.take hi).drop lo = (tokens.toList.drop lo).take (hi - lo) := by
    rw [List.drop_take]
  have h_bal : flowBracketBalance tokens lo hi = 0 := by
    rw [flowBracketBalance_eq_pbalance tokens lo hi h_lo_hi, ← h_slice]; exact h_wb.1
  have h_wt := WellTyped_subrange tokens LO lo hi HI h_LO_lo h_lo_hi h_hi_HI h_HI_sz
    h_wt_outer h_bal h_dyck
  exact seqLocated_of_recseqbody tokens lo hi h_lo h_lo_hi h_hi_sz h_open h_close h_wt h_rec

/-- **Map-side outer locate bundle assembler** (Phase J — Reflection 254, the symmetric mirror of
    `seqLocated_of_recseqbody_outer`).  Recovers the per-window `wt` from the outer-span `WellTyped`
    via `WellTyped_subrange` exactly as the seq side; the six pair-interior primitives (the storage
    asymmetry of Reflection 246) stay threaded — they are positional facts about the map body the
    enclosing locate carries from its own window guards, not recoverable from the window's
    `RecMapBody` alone.  So the per-window NEW deliverable is `{RecMapBody, +6}` (pos a guard, Dyck
    free, WellTyped recovered-from-outer).  Verified-but-unconsumed: composes only existing lemmas,
    references no sorry site, frontier sorry count unchanged. -/
theorem mapLocated_of_recmapbody_outer (tokens : Array (Positioned YamlToken))
    (LO HI lo hi : Nat)
    (h_LO_lo : LO ≤ lo) (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi_HI : hi ≤ HI)
    (h_HI_sz : HI ≤ tokens.size) (h_hi_sz : hi < tokens.size)
    (h_open : tokens[lo - 1]!.val = .flowMappingStart)
    (h_close : tokens[hi]!.val = .flowMappingEnd)
    (h_wt_outer : WellTyped ((tokens.toList.take HI).drop LO))
    (h_rec : RecMapBody ((tokens.toList.take hi).drop lo))
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
    MapLocated tokens lo hi := by
  have h_wb := h_rec.toWellBracketed
  have h_dyck := dyck_of_wellBracketed_window tokens lo hi h_wb
  have h_slice : (tokens.toList.take hi).drop lo = (tokens.toList.drop lo).take (hi - lo) := by
    rw [List.drop_take]
  have h_bal : flowBracketBalance tokens lo hi = 0 := by
    rw [flowBracketBalance_eq_pbalance tokens lo hi h_lo_hi, ← h_slice]; exact h_wb.1
  have h_wt := WellTyped_subrange tokens LO lo hi HI h_LO_lo h_lo_hi h_hi_HI h_HI_sz
    h_wt_outer h_bal h_dyck
  exact mapLocated_of_recmapbody tokens lo hi h_lo h_lo_hi h_hi_sz h_open h_close h_wt
    h_key_content h_key_scalar_value h_value_content h_value_scalar_succ
    h_key_bracket_succ h_value_bracket_succ h_rec

/-- **`FlowSubrangesOk` assembler from locators** (Phase J — the locate consumer joint).  Packages
    the two per-window `*_of_located_entry` joints into the universal `FlowSubrangesOk tokens` the
    `scanFiltered_emit{Seq,Map}_nonempty_structure` sorry sites consume, keyed only on the not-yet-
    produced locate recursion's deliverables `SeqLocated`/`MapLocated` (as bare universal hypotheses).
    Each `FlowSubrangesOk` field instantiates its locator at the guarded window, then hands the bundle
    plus the field's own guards to the matching joint.  Verified-but-unconsumed until the locate lands:
    it does not reference either sorry site, so the frontier sorry count is unchanged — but it retypes
    the whole downstream-of-locate residual to the single boundary "produce `SeqLocated`/`MapLocated`
    at every guarded window." -/
theorem flowSubrangesOk_of_locators (tokens : Array (Positioned YamlToken))
    (h_seq : ∀ lo hi, lo < hi → hi < tokens.size →
      tokens[hi]!.val = .flowSequenceEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowSequenceStart →
      SeqLocated tokens lo hi)
    (h_map : ∀ lo hi, lo < hi → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      MapLocated tokens lo hi) :
    FlowSubrangesOk tokens where
  -- The empty window (`lo = hi`, a nested `[]`/`{}`) is peeled to the vacuous body leaf
  -- (`seqBodyProps_empty`/`mapBodyProps_empty`), so the locators — and the recursive `Rec…Body`
  -- producers behind them — are only ever asked for the strictly non-empty window `lo < hi`.  This
  -- is what makes those producer hypotheses *satisfiable*: `RecSeqBody`/`RecMapBody` has no empty
  -- constructor, so a `lo ≤ hi`-typed producer would demand `RecSeqBody []` at the empty window.
  seq := fun lo hi h_lo_hi h_hi_sz h_tpe h_bal h_open =>
    (Nat.eq_or_lt_of_le h_lo_hi).elim
      (fun h_eq => seqBodyProps_empty tokens lo hi h_eq)
      (fun h_lt =>
        let L := h_seq lo hi h_lt h_hi_sz h_tpe h_bal h_open
        seqBodyProps_of_located_entry tokens lo hi L.pos h_lo_hi h_hi_sz h_tpe h_bal L.dyck L.wt
          h_open L.entry)
  map := fun lo hi h_lo_hi h_hi_sz h_tpe h_bal h_open =>
    (Nat.eq_or_lt_of_le h_lo_hi).elim
      (fun h_eq => mapBodyProps_empty tokens lo hi h_eq)
      (fun h_lt =>
        let L := h_map lo hi h_lt h_hi_sz h_tpe h_bal h_open
        mapBodyProps_of_located_entry tokens lo hi L.pos h_lo_hi h_hi_sz h_tpe h_bal L.dyck L.wt
          L.entry L.key_content L.key_scalar_value L.value_content L.value_scalar_succ
          L.key_bracket_succ L.value_bracket_succ)

/-- **Seq-side boundary-anchoring locator joint** (Phase J — the locate's input boundary, the
    consumer-joint-before-producer move at the *outer span* this time).  `FlowSubrangesOk.seq`
    quantifies over **all** `lo hi` with the bracket guards and *no* positional bounds, whereas the
    outer bundle assembler `seqLocated_of_recseqbody_outer` needs `2 ≤ lo`, `hi ≤ size - 2` (to use
    `LO = 2`, `HI = size - 2` — the body-interior span the proof already has `WellTyped` for) and
    `1 ≤ lo`.  This joint **recovers those bounds from the stream's own boundary tokens**: any window
    with `tokens[lo-1] = .flowSequenceStart` cannot have `lo ≤ 1` (else `tokens[0] = .streamStart`
    would have to be `.flowSequenceStart`), so `2 ≤ lo`; any window with `tokens[hi] = .flowSequenceEnd`
    cannot have `hi = size - 1` (else `tokens[size-1] = .streamEnd` would be `.flowSequenceEnd`), so
    `hi ≤ size - 2`.  With the bounds recovered, it threads the single outer `WellTyped` (over the
    interior `[2, size-2)`) and the bounded per-window `RecSeqBody` producer (the locate recursion's
    genuine deliverable, still owed) straight into `seqLocated_of_recseqbody_outer`.  Net: the
    *unbounded* `FlowSubrangesOk.seq` locator collapses to the *bounded* per-window `RecSeqBody`
    producer — exactly the shape a value-driven recursion over the body items will deliver.
    Verified-but-unconsumed until the locate recursion lands: composes only existing lemmas, references
    no sorry site, frontier sorry count unchanged. -/
theorem seqLocator_of_window_recseqbody (tokens : Array (Positioned YamlToken))
    (h_t0 : tokens[0]!.val = .streamStart)
    (h_tlast : tokens[tokens.size - 1]!.val = .streamEnd)
    (h_wt_outer : WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2))
    (h_seq_rec : ∀ lo hi, 2 ≤ lo → lo < hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowSequenceEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowSequenceStart →
      RecSeqBody ((tokens.toList.take hi).drop lo)) :
    ∀ lo hi, lo < hi → hi < tokens.size →
      tokens[hi]!.val = .flowSequenceEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowSequenceStart →
      SeqLocated tokens lo hi := by
  intro lo hi h_lo_lt h_hi_sz h_close h_bal h_open
  -- `h_seq_rec` is now keyed on the strict `lo < hi`; the empty window (`lo = hi`, a nested `[]`)
  -- is peeled at `flowSubrangesOk_of_locators` via `seqBodyProps_empty`, so it never reaches here.
  -- Everything downstream of this point consumes the `≤` form, recovered once.
  have h_lo_hi : lo ≤ hi := Nat.le_of_lt h_lo_lt
  -- Recover `2 ≤ lo` from the stream-start boundary token.
  have h_lo2 : 2 ≤ lo := by
    rcases Nat.lt_or_ge lo 2 with hlt | hge
    · exfalso
      have h0 : lo - 1 = 0 := by omega
      rw [h0, h_t0] at h_open
      exact absurd h_open (by decide)
    · exact hge
  -- Recover `hi ≤ size - 2` from the stream-end boundary token.
  have h_hi2 : hi ≤ tokens.size - 2 := by
    rcases Nat.lt_or_ge hi (tokens.size - 1) with hlt | hge
    · omega
    · exfalso
      have heq : hi = tokens.size - 1 := by omega
      rw [heq, h_tlast] at h_close
      exact absurd h_close (by decide)
  exact seqLocated_of_recseqbody_outer tokens 2 (tokens.size - 2) lo hi
    h_lo2 (by omega) h_lo_hi h_hi2 (by omega) h_hi_sz h_open h_close h_wt_outer
    (h_seq_rec lo hi h_lo2 h_lo_lt h_hi2 h_hi_sz h_close h_bal h_open)

/-- **Map-side boundary-anchoring locator joint** (Phase J — the verbatim mirror of
    `seqLocator_of_window_recseqbody` over the `.flowMapping{Start,End}` boundary tokens, completing
    the seq-before-map rhythm at the locate's *input* boundary).  `FlowSubrangesOk.map` quantifies
    over **all** `lo hi` with the bracket guards and *no* positional bounds, whereas the outer bundle
    assembler `mapLocated_of_recmapbody_outer` needs `2 ≤ lo`, `hi ≤ size - 2`, `1 ≤ lo`.  The
    bound-recovery is identical to the seq side: any window with `tokens[lo-1] = .flowMappingStart`
    cannot have `lo ≤ 1` (else `tokens[0] = .streamStart` would be `.flowMappingStart`), so `2 ≤ lo`;
    any window with `tokens[hi] = .flowMappingEnd` cannot have `hi = size - 1` (else
    `tokens[size-1] = .streamEnd` would be `.flowMappingEnd`), so `hi ≤ size - 2`.

    The *delta* from the seq joint is the **six pair-interior primitives** (the Reflection 246 storage
    asymmetry): `mapLocated_of_recmapbody_outer` threads them, so they surface here as six additional
    *per-window universal* producer hypotheses — the bounded value-driven map recursion establishes
    them as side-products of the same descent that builds the `RecMapBody`.  With the bounds recovered
    once, the joint hands the recovered bounds to every producer hypothesis and to the outer assembler.
    Net: the *unbounded* `FlowSubrangesOk.map` locator collapses to the *bounded* per-window
    `{RecMapBody, +6 primitives}` producer the value-driven recursion will deliver.
    Verified-but-unconsumed until the locate recursion lands: composes only existing lemmas, references
    no sorry site, frontier sorry count unchanged. -/
theorem mapLocator_of_window_recmapbody (tokens : Array (Positioned YamlToken))
    (h_t0 : tokens[0]!.val = .streamStart)
    (h_tlast : tokens[tokens.size - 1]!.val = .streamEnd)
    (h_wt_outer : WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2))
    (h_map_rec : ∀ lo hi, 2 ≤ lo → lo < hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      RecMapBody ((tokens.toList.take hi).drop lo))
    (h_key_content : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .key →
        k + 1 < hi ∧ isFlowContentStart tokens[k + 1]!.val)
    (h_key_scalar_value : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .key →
        (∃ c s, tokens[k + 1]!.val = .scalar c s) →
        k + 2 < hi ∧ tokens[k + 2]!.val = .value)
    (h_value_content : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .value →
        k + 1 < hi ∧ isFlowContentStart tokens[k + 1]!.val)
    (h_value_scalar_succ : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .value →
        (∃ c s, tokens[k + 1]!.val = .scalar c s) →
        k + 2 ≤ hi ∧
        (tokens[k + 2]!.val = .flowEntry ∨
         (tokens[k + 2]!.val = .flowMappingEnd ∧ k + 2 = hi)))
    (h_key_bracket_succ : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      ∀ k j, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .key →
        k + 1 < j → j < hi →
        flowBracketDelta tokens[j]!.val = -1 →
        flowBracketBalance tokens lo (j + 1) = 0 →
        j + 1 < hi ∧ tokens[j + 1]!.val = .value)
    (h_value_bracket_succ : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      ∀ k j, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .value →
        k + 1 < j → j < hi →
        flowBracketDelta tokens[j]!.val = -1 →
        flowBracketBalance tokens lo (j + 1) = 0 →
        j + 1 ≤ hi ∧
        (tokens[j + 1]!.val = .flowEntry ∨
         (tokens[j + 1]!.val = .flowMappingEnd ∧ j + 1 = hi))) :
    ∀ lo hi, lo < hi → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      MapLocated tokens lo hi := by
  intro lo hi h_lo_lt h_hi_sz h_close h_bal h_open
  -- `h_map_rec` is now keyed on the strict `lo < hi`; the empty window (`lo = hi`, a nested `{}`)
  -- is peeled at `flowSubrangesOk_of_locators` via `mapBodyProps_empty`, so it never reaches here.
  have h_lo_hi : lo ≤ hi := Nat.le_of_lt h_lo_lt
  -- Recover `2 ≤ lo` from the stream-start boundary token.
  have h_lo2 : 2 ≤ lo := by
    rcases Nat.lt_or_ge lo 2 with hlt | hge
    · exfalso
      have h0 : lo - 1 = 0 := by omega
      rw [h0, h_t0] at h_open
      exact absurd h_open (by decide)
    · exact hge
  -- Recover `hi ≤ size - 2` from the stream-end boundary token.
  have h_hi2 : hi ≤ tokens.size - 2 := by
    rcases Nat.lt_or_ge hi (tokens.size - 1) with hlt | hge
    · omega
    · exfalso
      have heq : hi = tokens.size - 1 := by omega
      rw [heq, h_tlast] at h_close
      exact absurd h_close (by decide)
  exact mapLocated_of_recmapbody_outer tokens 2 (tokens.size - 2) lo hi
    h_lo2 (by omega) h_lo_hi h_hi2 (by omega) h_hi_sz h_open h_close h_wt_outer
    (h_map_rec lo hi h_lo2 h_lo_lt h_hi2 h_hi_sz h_close h_bal h_open)
    (h_key_content lo hi h_lo2 h_lo_hi h_hi2 h_hi_sz h_close h_bal h_open)
    (h_key_scalar_value lo hi h_lo2 h_lo_hi h_hi2 h_hi_sz h_close h_bal h_open)
    (h_value_content lo hi h_lo2 h_lo_hi h_hi2 h_hi_sz h_close h_bal h_open)
    (h_value_scalar_succ lo hi h_lo2 h_lo_hi h_hi2 h_hi_sz h_close h_bal h_open)
    (h_key_bracket_succ lo hi h_lo2 h_lo_hi h_hi2 h_hi_sz h_close h_bal h_open)
    (h_value_bracket_succ lo hi h_lo2 h_lo_hi h_hi2 h_hi_sz h_close h_bal h_open)

/-- **`FlowSubrangesOk` from the per-window `Rec…Body` producers** (Phase J — the locate's whole
    consumer chain folded into one boundary).  This packages the three landed locate-consumer joints —
    the universal assembler `flowSubrangesOk_of_locators` (R243) and the two boundary-anchoring locator
    joints `seqLocator_of_window_recseqbody`/`mapLocator_of_window_recmapbody` (R255/R256) — into a
    single lemma keyed *only* on the locate recursion's genuine, still-owed deliverables: the
    bounded per-window `RecSeqBody`/`RecMapBody` producers (and, on the map side, the six pair-interior
    primitives the R246 storage asymmetry leaves below the `Rec…Body`'s granularity), plus the two
    stream-frame boundary tokens and the single outer `WellTyped` the proof already owns at the
    structure site.

    With this, the entire residual *downstream of the producer* is gone: every consumer step
    (`FlowSubrangesOk` packaging, the unbounded↔bounded boundary reconciliation on both sides, the
    per-window `*_of_located_entry`/`*_of_recseqbody_window` joints, the Dyck-free / WellTyped-via-outer
    reductions) is composed here once.  What remains is *exactly* the value-driven locate recursion: a
    function delivering `RecSeqBody ((take hi).drop lo)` (seq) / `RecMapBody …` + the six primitives
    (map) at every guarded body-interior window.  The future recursion discharges the two
    `scanFiltered_emit{Seq,Map}_nonempty_structure` sorry sites by `exact flowSubrangesOk_of_window_producers
    tokens h_t0 h_tlast h_wt_interior <seq recursion> <map recursion> <the six primitives>`.

    Verified-but-unconsumed (R225): composes only landed lemmas, references no sorry site, frontier
    sorry count unchanged at 4 — it collapses the locate's whole consumer chain into one typed
    boundary, the producer's contract. -/
theorem flowSubrangesOk_of_window_producers (tokens : Array (Positioned YamlToken))
    (h_t0 : tokens[0]!.val = .streamStart)
    (h_tlast : tokens[tokens.size - 1]!.val = .streamEnd)
    (h_wt_outer : WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2))
    (h_seq_rec : ∀ lo hi, 2 ≤ lo → lo < hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowSequenceEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowSequenceStart →
      RecSeqBody ((tokens.toList.take hi).drop lo))
    (h_map_rec : ∀ lo hi, 2 ≤ lo → lo < hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      RecMapBody ((tokens.toList.take hi).drop lo))
    (h_key_content : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .key →
        k + 1 < hi ∧ isFlowContentStart tokens[k + 1]!.val)
    (h_key_scalar_value : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .key →
        (∃ c s, tokens[k + 1]!.val = .scalar c s) →
        k + 2 < hi ∧ tokens[k + 2]!.val = .value)
    (h_value_content : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .value →
        k + 1 < hi ∧ isFlowContentStart tokens[k + 1]!.val)
    (h_value_scalar_succ : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      ∀ k, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .value →
        (∃ c s, tokens[k + 1]!.val = .scalar c s) →
        k + 2 ≤ hi ∧
        (tokens[k + 2]!.val = .flowEntry ∨
         (tokens[k + 2]!.val = .flowMappingEnd ∧ k + 2 = hi)))
    (h_key_bracket_succ : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      ∀ k j, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .key →
        k + 1 < j → j < hi →
        flowBracketDelta tokens[j]!.val = -1 →
        flowBracketBalance tokens lo (j + 1) = 0 →
        j + 1 < hi ∧ tokens[j + 1]!.val = .value)
    (h_value_bracket_succ : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      ∀ k j, lo ≤ k → k < hi →
        flowBracketBalance tokens lo k = 0 →
        tokens[k]!.val = .value →
        k + 1 < j → j < hi →
        flowBracketDelta tokens[j]!.val = -1 →
        flowBracketBalance tokens lo (j + 1) = 0 →
        j + 1 ≤ hi ∧
        (tokens[j + 1]!.val = .flowEntry ∨
         (tokens[j + 1]!.val = .flowMappingEnd ∧ j + 1 = hi))) :
    FlowSubrangesOk tokens :=
  flowSubrangesOk_of_locators tokens
    (seqLocator_of_window_recseqbody tokens h_t0 h_tlast h_wt_outer h_seq_rec)
    (mapLocator_of_window_recmapbody tokens h_t0 h_tlast h_wt_outer h_map_rec
      h_key_content h_key_scalar_value h_value_content h_value_scalar_succ
      h_key_bracket_succ h_value_bracket_succ)

/-- **The window-width strong-recursion combinator** (Phase J — the `Nat.strongRecOn` width-metric
    DRIVER's loop-closing skeleton, abstracted to its grammar-free core).  Every reflection since R272
    has named "the `Nat.strongRecOn` width-metric driver" as the single remaining brick on
    Workstream A's critical path, and named it as ONE thing.  It is in fact TWO, entangled, and this
    brick is the separating cut: the *recursion plumbing* (well-founded descent on the window width
    `hi - lo`, threading the inductive hypothesis to strictly-narrower sub-windows) and the *per-window
    grammar step* (read the head shape off `WellTyped`, classify the first item, assemble the body).
    The plumbing is generic — it knows nothing about tokens, `RecSeqBody`, or YAML; it is pure
    strong recursion on a `Nat` metric.  The grammar step is where the genuine remaining difficulty
    lives (the content substrate `WellTyped` does not encode).  Carving the plumbing off as this
    combinator pins the per-window step's *exact* inductive-hypothesis interface
    (`hi' - lo' < hi - lo → G lo' hi' → P lo' hi'`) and removes all well-founded-recursion risk from
    that step's future authoring: the step becomes a *non-recursive* lemma that simply *consumes* an
    oracle for narrower windows.

    This is the producer-side mirror of `flow_parser_ok_of_structure`'s span-bound strong induction
    (`∀ n, ∀ lo hi, hi - lo ≤ n → …`, `induction n using Nat.strongRecOn`): the parser recurses on the
    same window-width metric to *consume* `FlowSubrangesOk`; this combinator recurses on it to *produce*
    the structure those subranges describe.  The metric and the descent are identical; only the motive
    differs — so the wrapper is written once, abstractly, over arbitrary `P` (the per-window
    deliverable) and `G` (the per-window guard).

    Because it names **no collection-specific deliverable type** — `P` and `G` are abstract — the
    seq/map mirror discriminator ([[ref-entry-boundary-input-shape-split]]) says it does NOT re-split:
    unlike the structural moves and the classify unifiers (which mirror, because they mention
    `RecSeqBody`/`RecMapBody`), this single combinator drives *both* axes.  The seq driver instantiates
    `P := fun lo hi => RecSeqBody ((tokens.toList.take hi).drop lo)`; the map driver
    `P := … RecMapBody …`; both reuse this proof verbatim.  It is [[ref-consumer-joint-before-producer]]
    at the recursion layer (build the wrapper that consumes the per-window step before the step
    exists) and [[ref-fold-consumer-chain-to-producer-contract]] applied to the driver itself (the
    residual downstream collapses to the single typed boundary `step` — the per-window producer's
    contract, with its IH interface now fixed by this signature).

    Verified-but-unconsumed (R225): references no sorry site, frontier sorry count unchanged at 4;
    axiom-clean (pure `Nat.strongRecOn`, no `Classical.choice`). -/
theorem windowWidth_strongRecOn {P : Nat → Nat → Prop} (G : Nat → Nat → Prop)
    (step : ∀ lo hi, G lo hi →
      (∀ lo' hi', hi' - lo' < hi - lo → G lo' hi' → P lo' hi') →
      P lo hi) :
    ∀ lo hi, G lo hi → P lo hi := by
  -- Span-bound strong induction (the codebase idiom, cf. `flow_parser_ok_of_structure`): generalize
  -- the window width to a bound `n` so the IH ranges over every strictly-narrower span at once.
  have key : ∀ n : Nat, ∀ lo hi : Nat, hi - lo ≤ n → G lo hi → P lo hi := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n IH =>
      intro lo hi h_span h_g
      -- Hand the per-window step its oracle: any sub-window of strictly smaller width has width `< n`
      -- (since `hi - lo ≤ n`), so the strong-recursion IH discharges it.
      exact step lo hi h_g (fun lo' hi' h_lt h_g' =>
        IH (hi' - lo') (by omega) lo' hi' (Nat.le_refl _) h_g')
  intro lo hi h_g
  exact key (hi - lo) lo hi (Nat.le_refl _) h_g

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
