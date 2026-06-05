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
    (h_seq : ∀ lo hi, lo ≤ hi → hi < tokens.size →
      tokens[hi]!.val = .flowSequenceEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowSequenceStart →
      SeqLocated tokens lo hi)
    (h_map : ∀ lo hi, lo ≤ hi → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      MapLocated tokens lo hi) :
    FlowSubrangesOk tokens where
  seq := fun lo hi h_lo_hi h_hi_sz h_tpe h_bal h_open =>
    let L := h_seq lo hi h_lo_hi h_hi_sz h_tpe h_bal h_open
    seqBodyProps_of_located_entry tokens lo hi L.pos h_lo_hi h_hi_sz h_tpe h_bal L.dyck L.wt
      h_open L.entry
  map := fun lo hi h_lo_hi h_hi_sz h_tpe h_bal h_open =>
    let L := h_map lo hi h_lo_hi h_hi_sz h_tpe h_bal h_open
    mapBodyProps_of_located_entry tokens lo hi L.pos h_lo_hi h_hi_sz h_tpe h_bal L.dyck L.wt
      L.entry L.key_content L.key_scalar_value L.value_content L.value_scalar_succ
      L.key_bracket_succ L.value_bracket_succ

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
    (h_seq_rec : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowSequenceEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowSequenceStart →
      RecSeqBody ((tokens.toList.take hi).drop lo)) :
    ∀ lo hi, lo ≤ hi → hi < tokens.size →
      tokens[hi]!.val = .flowSequenceEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowSequenceStart →
      SeqLocated tokens lo hi := by
  intro lo hi h_lo_hi h_hi_sz h_close h_bal h_open
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
    (h_seq_rec lo hi h_lo2 h_lo_hi h_hi2 h_hi_sz h_close h_bal h_open)

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
    (h_map_rec : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
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
    ∀ lo hi, lo ≤ hi → hi < tokens.size →
      tokens[hi]!.val = .flowMappingEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowMappingStart →
      MapLocated tokens lo hi := by
  intro lo hi h_lo_hi h_hi_sz h_close h_bal h_open
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
    (h_map_rec lo hi h_lo2 h_lo_hi h_hi2 h_hi_sz h_close h_bal h_open)
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
    (h_seq_rec : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
      tokens[hi]!.val = .flowSequenceEnd →
      flowBracketBalance tokens lo hi = 0 →
      tokens[lo - 1]!.val = .flowSequenceStart →
      RecSeqBody ((tokens.toList.take hi).drop lo))
    (h_map_rec : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi ≤ tokens.size - 2 → hi < tokens.size →
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
