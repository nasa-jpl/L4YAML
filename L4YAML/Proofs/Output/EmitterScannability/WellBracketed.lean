/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Proofs.Output.EmitterScannability.FilteredTracking

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

/-! ### §G.balance  Well-bracketed body algebra (`.body2.establishing`)

Pure `flowBracketBalance`-level combinatorics underpinning the outer-level
flowEntry characterizations (legacy sorries 9646 / 9552).

An emitter *body* (the content between `[`/`]` or `{`/`}`) is a list of
**entries** — one per sequence item or one `key: value` pair — separated by
single `.flowEntry` tokens (the `", "` comma separators). Each entry is
`EntrySafe`: its total bracket balance is `0` and every `.flowEntry` strictly
inside it sits at running balance `≥ 1` (so it is an *inner* flowEntry, not an
outer-level one). `SafeBody Q` bundles a body whose entries are all `EntrySafe`
and whose heads all satisfy a predicate `Q` (instantiated downstream to
"content-start" for sequences and ".key" for mappings).

The main lemma `SafeBody_flowEntry_zero_balance` shows the *only* balance-0
flowEntries in such a body are the separators, and each is immediately followed
by an entry head (hence satisfies `Q`). The array/offset wrapper
`SafeBody_array_flowEntry` restates this against `flowBracketBalance` on the
filtered token array with a base offset `lo`, the exact shape the body
characterization theorems consume.

The scanner side — producing a `SafeBody` from emit output, which needs the
per-`emit v` block to be shown bracket-balanced with positive interior — is
`.body2.discharge`. -/

/-- Cumulative flow-bracket balance of a positioned-token list. -/
def pbalance (l : List (Positioned YamlToken)) : Int :=
  l.foldl (fun acc t => acc + flowBracketDelta t.val) 0

theorem pbalance_nil : pbalance [] = 0 := rfl

theorem pbalance_append (a b : List (Positioned YamlToken)) :
    pbalance (a ++ b) = pbalance a + pbalance b := by
  unfold pbalance
  rw [List.foldl_append,
      foldl_add_shift b (fun t => flowBracketDelta t.val) (a.foldl _ 0)]

theorem pbalance_singleton (t : Positioned YamlToken) :
    pbalance [t] = flowBracketDelta t.val := by
  simp [pbalance, List.foldl]

theorem pbalance_cons (t : Positioned YamlToken) (l : List (Positioned YamlToken)) :
    pbalance (t :: l) = flowBracketDelta t.val + pbalance l := by
  have h : t :: l = [t] ++ l := rfl
  rw [h, pbalance_append, pbalance_singleton]

/-- `.flowEntry` contributes `0` to the bracket balance. -/
theorem flowBracketDelta_flowEntry : flowBracketDelta .flowEntry = 0 := rfl

/-- A flow-sequence opener `[` contributes `+1`. -/
theorem flowBracketDelta_flowSequenceStart : flowBracketDelta .flowSequenceStart = 1 := rfl

/-- A flow-sequence closer `]` contributes `-1`. -/
theorem flowBracketDelta_flowSequenceEnd : flowBracketDelta .flowSequenceEnd = -1 := rfl

/-- A flow-mapping opener `{` contributes `+1`. -/
theorem flowBracketDelta_flowMappingStart : flowBracketDelta .flowMappingStart = 1 := rfl

/-- A flow-mapping closer `}` contributes `-1`. -/
theorem flowBracketDelta_flowMappingEnd : flowBracketDelta .flowMappingEnd = -1 := rfl

/-- A scalar token contributes `0`. -/
theorem flowBracketDelta_scalar (value : String) (style : ScalarStyle) :
    flowBracketDelta (.scalar value style) = 0 := rfl

/-- A `.key` token contributes `0`. -/
theorem flowBracketDelta_key : flowBracketDelta .key = 0 := rfl

/-- The only tokens of delta `+1` are the two openers `[` / `{`. -/
theorem flowBracketDelta_eq_one_iff (v : YamlToken) :
    flowBracketDelta v = 1 ↔ v = .flowSequenceStart ∨ v = .flowMappingStart := by
  cases v <;> simp [flowBracketDelta]

/-- An emitter *entry* (one sequence item, or one mapping `key: value` pair):
    bracket-balanced overall, with every interior `.flowEntry` at balance `≥ 1`. -/
def EntrySafe (e : List (Positioned YamlToken)) : Prop :=
  pbalance e = 0 ∧
  ∀ (i : Nat) (h : i < e.length), (e[i]'h).val = .flowEntry → pbalance (e.take i) ≥ 1

/-- A flow body: nonempty `EntrySafe` entries with `Q`-satisfying heads,
    separated by single `.flowEntry` tokens. -/
inductive SafeBody (Q : YamlToken → Prop) : List (Positioned YamlToken) → Prop
  | single (e : List (Positioned YamlToken)) (h_ne : e ≠ [])
      (h_safe : EntrySafe e) (h_head : Q (e.head h_ne).val) : SafeBody Q e
  | cons (e : List (Positioned YamlToken)) (fe : Positioned YamlToken)
      (rest : List (Positioned YamlToken)) (h_ne : e ≠ [])
      (h_safe : EntrySafe e) (h_head : Q (e.head h_ne).val)
      (h_fe : fe.val = .flowEntry) (h_rest : SafeBody Q rest) :
      SafeBody Q (e ++ fe :: rest)

/-- The head of a `SafeBody` exists and satisfies `Q`. -/
theorem SafeBody.head_Q {Q : YamlToken → Prop} {l : List (Positioned YamlToken)}
    (h : SafeBody Q l) : ∃ (hl : 0 < l.length), Q (l[0]'hl).val := by
  have key : ∀ (e : List (Positioned YamlToken)) (h_ne : e ≠ []),
      ∃ (hl : 0 < e.length), (e[0]'hl) = e.head h_ne := by
    intro e h_ne
    match e, h_ne with
    | a :: as, _ => exact ⟨by simp, rfl⟩
  induction h with
  | single e h_ne h_safe h_head =>
    obtain ⟨hl, he⟩ := key e h_ne
    exact ⟨hl, he ▸ h_head⟩
  | cons e fe rest h_ne h_safe h_head h_fe h_rest _ih =>
    obtain ⟨hl0, he⟩ := key e h_ne
    have hl : 0 < (e ++ fe :: rest).length := by rw [List.length_append]; omega
    refine ⟨hl, ?_⟩
    have hidx : (e ++ fe :: rest)[0]'hl = e[0]'hl0 := List.getElem_append_left hl0
    rw [hidx, he]; exact h_head

/-- **Main balance lemma.** In a `SafeBody`, every balance-0 `.flowEntry` is a
    separator, immediately followed by an entry head (which satisfies `Q`). -/
theorem SafeBody_flowEntry_zero_balance {Q : YamlToken → Prop}
    {body : List (Positioned YamlToken)} (h : SafeBody Q body) :
    ∀ (k : Nat) (hk : k < body.length),
      (body[k]'hk).val = .flowEntry → pbalance (body.take k) = 0 →
      ∃ (hk1 : k + 1 < body.length), Q (body[k+1]'hk1).val := by
  induction h with
  | single e h_ne h_safe h_head =>
    intro k hk h_fe h_bal
    have := h_safe.2 k hk h_fe
    omega
  | cons e fe rest h_ne h_safe h_head h_fe h_rest ih =>
    intro k hk h_fek h_bal
    have h_len : (e ++ fe :: rest).length = e.length + 1 + rest.length := by
      simp [List.length_append]; omega
    rcases Nat.lt_trichotomy k e.length with hlt | heq | hgt
    · -- inside `e`: flowEntry there has balance ≥ 1, contradicting = 0
      exfalso
      have hbody_k : (e ++ fe :: rest)[k]'hk = e[k]'hlt := List.getElem_append_left hlt
      have hek_fe : (e[k]'hlt).val = .flowEntry := by rw [← hbody_k]; exact h_fek
      have htake : (e ++ fe :: rest).take k = e.take k := by
        rw [List.take_append, show k - e.length = 0 from by omega,
            List.take_zero, List.append_nil]
      rw [htake] at h_bal
      have := h_safe.2 k hlt hek_fe
      omega
    · -- the separator at `k = e.length`: next is the head of `rest`
      subst heq
      obtain ⟨hr0, hQ⟩ := h_rest.head_Q
      have hk1 : e.length + 1 < (e ++ fe :: rest).length := by rw [h_len]; omega
      refine ⟨hk1, ?_⟩
      have hidx : (e ++ fe :: rest)[e.length + 1]'hk1 = rest[0]'hr0 := by
        have h1 : (e ++ fe :: rest)[e.length + 1]? = rest[0]? := by
          rw [List.getElem?_append_right (by omega),
              show e.length + 1 - e.length = 0 + 1 from by omega, List.getElem?_cons_succ]
        rw [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hr0] at h1
        exact Option.some.inj h1
      rw [hidx]; exact hQ
    · -- after the separator: write `k = |e| + 1 + m`, the offset `m` into `rest`
      obtain ⟨m, hm⟩ : ∃ m, k = e.length + 1 + m := ⟨k - e.length - 1, by omega⟩
      subst hm
      have hk_rest : m < rest.length := by rw [h_len] at hk; omega
      -- body[|e|+1+m] = rest[m]
      have hbody_k : (e ++ fe :: rest)[e.length + 1 + m]'hk = rest[m]'hk_rest := by
        have h1 : (e ++ fe :: rest)[e.length + 1 + m]? = rest[m]? := by
          rw [List.getElem?_append_right (by omega),
              show e.length + 1 + m - e.length = m + 1 from by omega, List.getElem?_cons_succ]
        rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk_rest] at h1
        exact Option.some.inj h1
      have h_rest_fe : (rest[m]'hk_rest).val = .flowEntry := by
        rw [← hbody_k]; exact h_fek
      -- balance(take (|e|+1+m)) = pbalance e + delta fe + pbalance (rest.take m) = pbalance (rest.take m)
      have htake : (e ++ fe :: rest).take (e.length + 1 + m) = e ++ fe :: rest.take m := by
        rw [List.take_append, List.take_of_length_le (show e.length ≤ e.length + 1 + m from by omega),
            show e.length + 1 + m - e.length = m + 1 from by omega, List.take_succ_cons]
      have h_bal' : pbalance (rest.take m) = 0 := by
        rw [htake, pbalance_append, pbalance_cons, h_safe.1, h_fe,
            flowBracketDelta_flowEntry] at h_bal
        omega
      obtain ⟨hj1, hQ⟩ := ih m hk_rest h_rest_fe h_bal'
      have hk1 : e.length + 1 + m + 1 < (e ++ fe :: rest).length := by rw [h_len]; omega
      refine ⟨hk1, ?_⟩
      have hidx : (e ++ fe :: rest)[e.length + 1 + m + 1]'hk1 = rest[m + 1]'hj1 := by
        have h1 : (e ++ fe :: rest)[e.length + 1 + m + 1]? = rest[m + 1]? := by
          rw [List.getElem?_append_right (by omega),
              show e.length + 1 + m + 1 - e.length = (m + 1) + 1 from by omega,
              List.getElem?_cons_succ]
        rw [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hj1] at h1
        exact Option.some.inj h1
      rw [hidx]; exact hQ

/-- Bridge: `flowBracketBalance` on an array slice equals `pbalance` of the
    corresponding `drop`/`take` of its `toList`. -/
theorem flowBracketBalance_eq_pbalance (arr : Array (Positioned YamlToken))
    (lo k : Nat) (h : lo ≤ k) :
    flowBracketBalance arr lo k = pbalance ((arr.toList.drop lo).take (k - lo)) := by
  unfold flowBracketBalance pbalance
  split
  · rename_i hge
    have : k - lo = 0 := by omega
    rw [this, List.take_zero]; rfl
  · rfl

/-- **Array/offset wrapper.** Restates `SafeBody_flowEntry_zero_balance` against
    `flowBracketBalance` on the filtered token array with base offset `lo`,
    matching the body-characterization consumers. -/
theorem SafeBody_array_flowEntry {Q : YamlToken → Prop}
    (arr : Array (Positioned YamlToken)) (lo : Nat)
    (h : SafeBody Q (arr.toList.drop lo)) :
    ∀ (k : Nat), lo ≤ k → (hk : k < arr.size) →
      (arr[k]'hk).val = .flowEntry → flowBracketBalance arr lo k = 0 →
      ∃ (hk1 : k + 1 < arr.size), Q (arr[k+1]'hk1).val := by
  intro k h_lo hk h_fe h_bal
  have h_len : (arr.toList.drop lo).length = arr.size - lo := by
    rw [List.length_drop, Array.length_toList]
  have hj_lt : k - lo < (arr.toList.drop lo).length := by rw [h_len]; omega
  -- body[k - lo].val = arr[k].val
  have h_drop_get : ((arr.toList.drop lo)[k - lo]'hj_lt).val = (arr[k]'hk).val := by
    rw [List.getElem_drop]
    rw [Array.getElem_toList (by omega)]
    congr 2
    omega
  have h_fe' : ((arr.toList.drop lo)[k - lo]'hj_lt).val = .flowEntry := by
    rw [h_drop_get]; exact h_fe
  -- balance(take (k - lo)) = 0
  have h_bal' : pbalance ((arr.toList.drop lo).take (k - lo)) = 0 := by
    rw [← flowBracketBalance_eq_pbalance arr lo k h_lo]; exact h_bal
  obtain ⟨hj1, hQ⟩ :=
    SafeBody_flowEntry_zero_balance h (k - lo) hj_lt h_fe' h_bal'
  have hk1 : k + 1 < arr.size := by rw [h_len] at hj1; omega
  refine ⟨hk1, ?_⟩
  have h_get : ((arr.toList.drop lo)[(k - lo) + 1]'hj1).val = (arr[k+1]'hk1).val := by
    rw [List.getElem_drop]
    rw [Array.getElem_toList (by omega)]
    congr 2
    omega
  rw [← h_get]; exact hQ

/-! #### Well-bracketed blocks (`.body2.discharge.wbalgebra`)

`WellBracketed` is the Dyck-word condition on flow brackets: total balance `0`
with every prefix balance `≥ 0`. It is the recursive invariant a scanned
`emit v` block satisfies — closed under concatenation (so a body of blocks +
`.flowEntry` separators stays well-bracketed) and under wrapping a
`WellBracketed` interior in a matching `[ ]`/`{ }` pair. The wrapping lemma
additionally yields `EntrySafe` (the per-entry obligation `SafeBody` consumes):
inside a bracket pair every interior `.flowEntry` sits at balance `≥ 1`.

These are pure `pbalance` combinatorics. The scanner side — producing a
`WellBracketed` filtered delta from `emit v`, which threads delta-tracking
through `emit_scans_in_flow` and the list/pairlist producers — is
`.body2.discharge.bridge`. -/

/-- Dyck condition on flow brackets: balanced, with all prefix balances `≥ 0`. -/
def WellBracketed (l : List (Positioned YamlToken)) : Prop :=
  pbalance l = 0 ∧ ∀ (i : Nat), pbalance (l.take i) ≥ 0

theorem WellBracketed_nil : WellBracketed [] := by
  refine ⟨pbalance_nil, fun i => ?_⟩
  simp [List.take_nil, pbalance_nil]

/-- Prefix balance of a concatenation splits additively. -/
theorem pbalance_take_append (a b : List (Positioned YamlToken)) (i : Nat) :
    pbalance ((a ++ b).take i) = pbalance (a.take i) + pbalance (b.take (i - a.length)) := by
  rw [List.take_append, pbalance_append]

/-- Prefix balance of a singleton: `0` (empty prefix) or its delta. -/
theorem pbalance_take_singleton (t : Positioned YamlToken) (j : Nat) :
    pbalance ([t].take j) = if j = 0 then 0 else flowBracketDelta t.val := by
  match j with
  | 0 => simp [pbalance_nil]
  | k + 1 => simp [List.take_succ_cons, pbalance_singleton]

/-- A single token of zero delta (scalar, `:`, `.value`, …) is well-bracketed. -/
theorem WellBracketed_singleton_delta_zero (t : Positioned YamlToken)
    (h : flowBracketDelta t.val = 0) : WellBracketed [t] := by
  refine ⟨by rw [pbalance_singleton, h], fun i => ?_⟩
  rw [pbalance_take_singleton]
  split <;> omega

/-- `WellBracketed` is closed under concatenation. -/
theorem WellBracketed_append (a b : List (Positioned YamlToken))
    (ha : WellBracketed a) (hb : WellBracketed b) : WellBracketed (a ++ b) := by
  refine ⟨?_, fun i => ?_⟩
  · have := ha.1; have := hb.1; rw [pbalance_append]; omega
  · rw [pbalance_take_append]
    have h1 := ha.2 i; have h2 := hb.2 (i - a.length); omega

/-- Inserting a delta-`0` token (a `.key`/`.value`/`.scalar`/`.flowEntry`) at any
    position of a `WellBracketed` list keeps it `WellBracketed`: the total balance
    is unchanged and every prefix balance gains only the (zero) delta.  This is the
    pure lemma the **colon step** needs — `scanValuePrepare`'s retroactive
    placeholder→`.key` write inserts a single delta-`0` token *into the middle* of
    the key block (breaking the per-step append decomposition the sequence-body
    producer relied on), and `WellBracketed`-ness must survive that mid-list
    insertion regardless of *where* it lands. -/
theorem WellBracketed_insert_delta_zero (l : List (Positioned YamlToken))
    (t : Positioned YamlToken) (i : Nat)
    (h_delta : flowBracketDelta t.val = 0) (h_wb : WellBracketed l) :
    WellBracketed (l.take i ++ t :: l.drop i) := by
  obtain ⟨h_bal, h_pre⟩ := h_wb
  have h_split : pbalance (l.take i) + pbalance (l.drop i) = 0 := by
    have h := (pbalance_append (l.take i) (l.drop i)).symm
    rw [List.take_append_drop] at h
    omega
  refine ⟨?_, fun j => ?_⟩
  · -- total balance unchanged: prefix + 0 + suffix = 0
    rw [pbalance_append, pbalance_cons, h_delta]; omega
  · -- prefix balance ≥ 0 at every cut `j`
    rw [pbalance_take_append]
    rcases Nat.eq_zero_or_pos (j - (l.take i).length) with hm | hm
    · -- cut lands inside `l.take i`: a genuine prefix of `l`
      have hlen : (l.take i).length ≤ i := by rw [List.length_take]; omega
      have hji : j ≤ i := by omega
      rw [hm, List.take_zero, pbalance_nil, List.take_take]
      simp only [Nat.min_eq_left hji]
      have := h_pre j; omega
    · -- cut passes the insert: prefix(l.take i) + delta t(=0) + a prefix of the suffix
      obtain ⟨k, hk⟩ : ∃ k, j - (l.take i).length = k + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos hm).symm⟩
      rw [hk, List.take_succ_cons, pbalance_cons, h_delta]
      have hlen_le : (l.take i).length ≤ j := by omega
      rw [List.take_of_length_le hlen_le]
      have h2 : pbalance (l.take i) + pbalance ((l.drop i).take k) = pbalance (l.take (i + k)) := by
        rw [List.take_add, pbalance_append]
      have := h_pre (i + k); omega

/-- The `i = 0` specialization of `WellBracketed_insert_delta_zero`: prepending a
    delta-`0` token preserves `WellBracketed`.  The colon writes `.key` at the
    *front* of the key block (the first new filtered token is `.key`, per
    `keyshape_first_token_key`), so this cons form is the one the mapping-body
    producer applies directly. -/
theorem WellBracketed_cons_delta_zero (t : Positioned YamlToken)
    (l : List (Positioned YamlToken))
    (h_delta : flowBracketDelta t.val = 0) (h_wb : WellBracketed l) :
    WellBracketed (t :: l) := by
  simpa using WellBracketed_insert_delta_zero l t 0 h_delta h_wb

/-- **Wrapping lemma.** A `WellBracketed` interior framed by a matching opener
    (delta `+1`) and closer (delta `-1`) is both `WellBracketed` and `EntrySafe`.
    The `EntrySafe` half is the payoff: every interior `.flowEntry` is at
    balance `≥ 1` because the opener already contributes `+1`. -/
theorem wrap_block (op cl : Positioned YamlToken) (body : List (Positioned YamlToken))
    (h_op : flowBracketDelta op.val = 1) (h_cl : flowBracketDelta cl.val = -1)
    (h_body : WellBracketed body) :
    WellBracketed (op :: (body ++ [cl])) ∧ EntrySafe (op :: (body ++ [cl])) := by
  -- total balance: 1 + (0 + -1) = 0
  have h_total : pbalance (op :: (body ++ [cl])) = 0 := by
    rw [pbalance_cons, pbalance_append, pbalance_singleton, h_op, h_cl]
    have := h_body.1; omega
  -- prefix balances ≥ 0
  have h_pref : ∀ i, pbalance ((op :: (body ++ [cl])).take i) ≥ 0 := by
    intro i
    match i with
    | 0 => simp [List.take_zero, pbalance_nil]
    | m + 1 =>
      rw [List.take_succ_cons, pbalance_cons, h_op, pbalance_take_append,
          pbalance_take_singleton]
      have hbody := h_body.2 m
      split <;> omega
  refine ⟨⟨h_total, h_pref⟩, h_total, ?_⟩
  -- EntrySafe interior: a `.flowEntry` can only sit in `body`, at balance ≥ 1
  intro idx h_idx h_fe
  match idx, h_idx, h_fe with
  | 0, h_idx, h_fe =>
    exfalso
    have hv : ((op :: (body ++ [cl]))[0]'h_idx).val = op.val := rfl
    rw [hv] at h_fe
    have hd := h_op
    rw [h_fe, flowBracketDelta_flowEntry] at hd
    omega
  | m + 1, h_idx, h_fe =>
    have h_m_lt : m < (body ++ [cl]).length := by
      rw [List.length_cons] at h_idx; omega
    have hv : ((op :: (body ++ [cl]))[m + 1]'h_idx).val = ((body ++ [cl])[m]'h_m_lt).val := by
      rw [List.getElem_cons_succ]
    rw [hv] at h_fe
    rcases Nat.lt_or_ge m body.length with hlt | hge
    · -- genuine interior flowEntry: balance = 1 + (body prefix ≥ 0) ≥ 1
      rw [List.take_succ_cons, pbalance_cons, h_op, pbalance_take_append,
          show m - body.length = 0 from by omega, List.take_zero, pbalance_nil]
      have := h_body.2 m
      omega
    · -- m = body.length: the token is the closer, not a flowEntry — contradiction
      exfalso
      have h_m_eq : m = body.length := by
        rw [List.length_append] at h_m_lt
        have : ([cl]).length = 1 := rfl
        omega
      have hcl_v : ((body ++ [cl])[m]'h_m_lt).val = cl.val := by
        have e : (body ++ [cl])[m]? = some cl := by
          rw [List.getElem?_append_right (by omega), h_m_eq,
              show body.length - body.length = 0 from by omega]
          rfl
        rw [List.getElem?_eq_getElem h_m_lt] at e
        exact congrArg (·.val) (Option.some.inj e)
      rw [hcl_v] at h_fe
      have hd := h_cl
      rw [h_fe, flowBracketDelta_flowEntry] at hd
      omega

/-- A scalar entry (a single non-`.flowEntry`, delta-`0` token) is `EntrySafe`.
    The `≠ .flowEntry` premise is essential: a singleton `.flowEntry` would have
    its sole token at prefix balance `0`, violating the `≥ 1` interior condition. -/
theorem EntrySafe_singleton (t : Positioned YamlToken)
    (h_delta : flowBracketDelta t.val = 0) (h_ne : t.val ≠ .flowEntry) : EntrySafe [t] := by
  refine ⟨by rw [pbalance_singleton, h_delta], fun i h_i h_fe => ?_⟩
  -- a singleton's only index is 0, and its value is not a flowEntry
  match i, h_i, h_fe with
  | 0, _, h_fe =>
    exfalso
    have hv : (([t])[0]'(by simp)).val = t.val := rfl
    rw [hv] at h_fe
    exact h_ne h_fe
  | k + 1, h_i, _ => simp at h_i

/-- A flow-sequence block `[ body ]` with `WellBracketed` interior is both
    `WellBracketed` and `EntrySafe` — the shape a scanned `emit (.sequence …)`
    block takes. Specializes `wrap_block` with the concrete bracket deltas. -/
theorem wrap_seq_block (op cl : Positioned YamlToken)
    (body : List (Positioned YamlToken))
    (h_op : op.val = .flowSequenceStart) (h_cl : cl.val = .flowSequenceEnd)
    (h_body : WellBracketed body) :
    WellBracketed (op :: (body ++ [cl])) ∧ EntrySafe (op :: (body ++ [cl])) :=
  wrap_block op cl body (h_op ▸ flowBracketDelta_flowSequenceStart)
    (h_cl ▸ flowBracketDelta_flowSequenceEnd) h_body

/-- A flow-mapping block `{ body }` with `WellBracketed` interior is both
    `WellBracketed` and `EntrySafe` — the shape a scanned `emit (.mapping …)`
    block takes. Specializes `wrap_block` with the concrete bracket deltas. -/
theorem wrap_map_block (op cl : Positioned YamlToken)
    (body : List (Positioned YamlToken))
    (h_op : op.val = .flowMappingStart) (h_cl : cl.val = .flowMappingEnd)
    (h_body : WellBracketed body) :
    WellBracketed (op :: (body ++ [cl])) ∧ EntrySafe (op :: (body ++ [cl])) :=
  wrap_block op cl body (h_op ▸ flowBracketDelta_flowMappingStart)
    (h_cl ▸ flowBracketDelta_flowMappingEnd) h_body

/-- A scalar entry — a single `.scalar` token — is `EntrySafe`. -/
theorem EntrySafe_scalar (t : Positioned YamlToken) (value : String) (style : ScalarStyle)
    (h : t.val = .scalar value style) : EntrySafe [t] :=
  EntrySafe_singleton t (h ▸ flowBracketDelta_scalar value style) (by rw [h]; simp)

/-- Concatenation of two `EntrySafe` entries is `EntrySafe`.  Each piece is
    bracket-balanced (`pbalance = 0`), so the prefix balance at any `.flowEntry`
    in `a` is the same as inside `a` alone (`≥ 1`), and the prefix balance at a
    `.flowEntry` in `b` is `pbalance a + (b-prefix balance) = 0 + (≥ 1)`. -/
theorem EntrySafe_append (a b : List (Positioned YamlToken))
    (ha : EntrySafe a) (hb : EntrySafe b) : EntrySafe (a ++ b) := by
  refine ⟨by rw [pbalance_append, ha.1, hb.1]; omega, ?_⟩
  intro i h_i h_fe
  rcases Nat.lt_or_ge i a.length with hlt | hge
  · -- the `.flowEntry` lives inside `a`
    have h_idx : (a ++ b)[i]'h_i = a[i]'hlt := List.getElem_append_left hlt
    have h_take : (a ++ b).take i = a.take i := by
      rw [List.take_append, show i - a.length = 0 from by omega, List.take_zero, List.append_nil]
    rw [h_take]
    exact ha.2 i hlt (by rw [← h_idx]; exact h_fe)
  · -- the `.flowEntry` lives inside `b` at offset `i - a.length`
    have hb_idx : i - a.length < b.length := by rw [List.length_append] at h_i; omega
    have h_idx : (a ++ b)[i]'h_i = b[i - a.length]'hb_idx := List.getElem_append_right hge
    have h_take : (a ++ b).take i = a ++ b.take (i - a.length) := by
      rw [List.take_append, List.take_of_length_le hge]
    rw [h_take, pbalance_append, ha.1]
    have := hb.2 (i - a.length) hb_idx (by rw [← h_idx]; exact h_fe)
    omega

/-! #### Unit entries — the value-end successor (`.body2.discharge.entryunit`)

`EntrySafe` is too weak to read a *successor* off a value-end.  It admits an entry
with an *interior* balance-`0` split (e.g. `scalar scalar`, two depth-`0` tokens) that
the emitter never produces — `emit v` for one value is a lone scalar token or one
matched `[…]`/`{…}` pair.  That gap is exactly why `EntrySafe` yields the `.flowEntry`
*converse* (`SafeBody_array_flowEntry`: a depth-`0` `.flowEntry` is a separator, an
entry head next) but **not** the forward fact a value-end needs (a depth-`0`
scalar/close is an *entry end*, so a separator or the body close comes next).

`EntryUnit` closes the gap: a unit entry forbids interior depth-`0` positions (every
proper nonempty prefix is at balance `≥ 1`), so a scalar-headed unit is a singleton and
a bracket-headed one a single matched pair — the emitter's per-value shape.
`SafeBodyUnit Q` is the body of unit entries, and `SafeBodyUnit_succ` is the dual of
`SafeBody_flowEntry_zero_balance`: in such a body, a token that ends a balanced prefix
and is not itself a separator is the last token of an entry, so its successor is a
separating `.flowEntry` or the body end.  These are pure `pbalance` combinatorics — the
enablement substrate for the `scalar_succ`/`value_scalar_succ` and bracket-conjunct
`h_succ` shape facts.  See Reflection 218: the `h_succ` guard
`flowBracketDelta tokens[j]!.val = -1` is precisely the "value-end, not separator"
discriminator this lemma consumes. -/

/-- A *unit* entry: bracket-balanced (`pbalance = 0`) with every proper nonempty prefix
    at balance `≥ 1`.  Strengthens `EntrySafe` by forbidding *interior* depth-`0`
    positions — so a scalar-headed unit is a singleton and a bracket-headed one a single
    matched pair, matching `emit v`'s per-value output. -/
def EntryUnit (e : List (Positioned YamlToken)) : Prop :=
  pbalance e = 0 ∧ ∀ (i : Nat), 0 < i → i < e.length → pbalance (e.take i) ≥ 1

/-- A single delta-`0` token (a `.scalar`/`.key`/`.value`) is a unit entry — vacuously,
    it has no proper nonempty prefix. -/
theorem EntryUnit_singleton_delta_zero (t : Positioned YamlToken)
    (h_delta : flowBracketDelta t.val = 0) : EntryUnit [t] := by
  refine ⟨by rw [pbalance_singleton, h_delta], fun i h_i h_lt => ?_⟩
  exfalso
  simp only [List.length_cons, List.length_nil] at h_lt
  omega

/-- A `.scalar` token is a unit entry. -/
theorem EntryUnit_scalar (t : Positioned YamlToken) (value : String) (style : ScalarStyle)
    (h : t.val = .scalar value style) : EntryUnit [t] :=
  EntryUnit_singleton_delta_zero t (h ▸ flowBracketDelta_scalar value style)

/-- A `WellBracketed` interior framed by a matching opener (delta `+1`)/closer
    (delta `-1`) is a unit entry: the opener lifts every interior prefix to balance
    `≥ 1`, and the closer's `-1` only lands at the final position.  The unit refinement
    of `wrap_block`'s `EntrySafe` half. -/
theorem EntryUnit_wrap (op cl : Positioned YamlToken) (body : List (Positioned YamlToken))
    (h_op : flowBracketDelta op.val = 1) (h_cl : flowBracketDelta cl.val = -1)
    (h_body : WellBracketed body) : EntryUnit (op :: (body ++ [cl])) := by
  refine ⟨?_, fun i h_i h_lt => ?_⟩
  · -- total balance 1 + 0 + (-1) = 0
    rw [pbalance_cons, pbalance_append, pbalance_singleton, h_op, h_cl]
    have := h_body.1; omega
  · -- i = m+1; the prefix is `op :: body.take m` (the `[cl]` part is dropped, m ≤ |body|)
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have h_m_le : m ≤ body.length := by
      simp only [List.length_cons, List.length_append, List.length_nil] at h_lt
      omega
    rw [List.take_succ_cons, pbalance_cons, h_op, pbalance_take_append,
        show m - body.length = 0 from by omega, List.take_zero, pbalance_nil]
    have := h_body.2 m
    omega

/-- A flow body of *unit* entries — `SafeBody` with `EntryUnit` in place of `EntrySafe`:
    nonempty unit entries with `Q`-satisfying heads, separated by single `.flowEntry`s. -/
inductive SafeBodyUnit (Q : YamlToken → Prop) : List (Positioned YamlToken) → Prop
  | single (e : List (Positioned YamlToken)) (h_ne : e ≠ [])
      (h_unit : EntryUnit e) (h_head : Q (e.head h_ne).val) : SafeBodyUnit Q e
  | cons (e : List (Positioned YamlToken)) (fe : Positioned YamlToken)
      (rest : List (Positioned YamlToken)) (h_ne : e ≠ [])
      (h_unit : EntryUnit e) (h_head : Q (e.head h_ne).val)
      (h_fe : fe.val = .flowEntry) (h_rest : SafeBodyUnit Q rest) :
      SafeBodyUnit Q (e ++ fe :: rest)

/-- **Forward value-end successor** — the dual of `SafeBody_flowEntry_zero_balance`.
    In a body of unit entries, a token `k` that ends a balanced prefix
    (`pbalance (take (k+1)) = 0`) and is *not* itself a separator (`≠ .flowEntry`) is
    the last token of an entry, so either it is the body's last token (`k+1 = length`)
    or its successor is a separating `.flowEntry`.  `EntrySafe` is too weak for this —
    it permits an interior depth-`0` split that would make `body[k+1]` another token of
    the *same* entry; `EntryUnit`'s `≥ 1` interior condition forbids it. -/
theorem SafeBodyUnit_succ {Q : YamlToken → Prop}
    {body : List (Positioned YamlToken)} (h : SafeBodyUnit Q body) :
    ∀ (k : Nat) (hk : k < body.length),
      pbalance (body.take (k + 1)) = 0 → (body[k]'hk).val ≠ .flowEntry →
      k + 1 = body.length ∨
      ∃ (hk1 : k + 1 < body.length), (body[k+1]'hk1).val = .flowEntry := by
  induction h with
  | single e h_ne h_unit h_head =>
    intro k hk h_bal _h_nfe
    rcases Nat.lt_or_ge (k + 1) e.length with hlt | _hge
    · -- k+1 < |e|: an interior prefix sits at balance ≥ 1, contradicting = 0
      exfalso; have := h_unit.2 (k + 1) (by omega) hlt; omega
    · -- k < |e| and k+1 ≥ |e| force k+1 = |e|
      left; omega
  | cons e fe rest h_ne h_unit h_head h_fe h_rest ih =>
    intro k hk h_bal h_nfe
    have h_len : (e ++ fe :: rest).length = e.length + 1 + rest.length := by
      simp [List.length_append]; omega
    rcases Nat.lt_trichotomy k e.length with hlt | heq | hgt
    · -- inside `e`
      rcases Nat.lt_or_ge (k + 1) e.length with hlt1 | _hge1
      · -- k+1 < |e|: interior prefix of `e` at balance ≥ 1 contradicts = 0
        exfalso
        have htake : (e ++ fe :: rest).take (k + 1) = e.take (k + 1) := by
          rw [List.take_append, show k + 1 - e.length = 0 from by omega,
              List.take_zero, List.append_nil]
        rw [htake] at h_bal
        have := h_unit.2 (k + 1) (by omega) hlt1
        omega
      · -- k+1 = |e|: the successor is the separator `fe`
        have hk1eq : k + 1 = e.length := by omega
        right
        have hk1 : k + 1 < (e ++ fe :: rest).length := by rw [h_len]; omega
        refine ⟨hk1, ?_⟩
        have hidx : (e ++ fe :: rest)[k + 1]'hk1 = fe := by
          have h1 : (e ++ fe :: rest)[k + 1]? = some fe := by
            rw [List.getElem?_append_right (by omega), hk1eq,
                show e.length - e.length = 0 from by omega]
            rfl
          rw [List.getElem?_eq_getElem hk1] at h1
          exact Option.some.inj h1
        rw [hidx]; exact h_fe
    · -- k = |e|: `body[k] = fe = .flowEntry`, contradicting `h_nfe`
      exfalso; subst heq
      have hidx : (e ++ fe :: rest)[e.length]'hk = fe := by
        have h1 : (e ++ fe :: rest)[e.length]? = some fe := by
          rw [List.getElem?_append_right (by omega),
              show e.length - e.length = 0 from by omega]
          rfl
        rw [List.getElem?_eq_getElem hk] at h1
        exact Option.some.inj h1
      rw [hidx] at h_nfe; exact h_nfe h_fe
    · -- after the separator: `k = |e| + 1 + m`, recurse into `rest`
      obtain ⟨m, hm⟩ : ∃ m, k = e.length + 1 + m := ⟨k - e.length - 1, by omega⟩
      subst hm
      have hk_rest : m < rest.length := by rw [h_len] at hk; omega
      have hbody_k : (e ++ fe :: rest)[e.length + 1 + m]'hk = rest[m]'hk_rest := by
        have h1 : (e ++ fe :: rest)[e.length + 1 + m]? = rest[m]? := by
          rw [List.getElem?_append_right (by omega),
              show e.length + 1 + m - e.length = m + 1 from by omega, List.getElem?_cons_succ]
        rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk_rest] at h1
        exact Option.some.inj h1
      have h_nfe' : (rest[m]'hk_rest).val ≠ .flowEntry := by rw [← hbody_k]; exact h_nfe
      have htake : (e ++ fe :: rest).take (e.length + 1 + m + 1) =
          e ++ fe :: rest.take (m + 1) := by
        rw [List.take_append,
            List.take_of_length_le (show e.length ≤ e.length + 1 + m + 1 from by omega),
            show e.length + 1 + m + 1 - e.length = (m + 1) + 1 from by omega, List.take_succ_cons]
      have h_bal' : pbalance (rest.take (m + 1)) = 0 := by
        rw [htake, pbalance_append, pbalance_cons, h_unit.1, h_fe,
            flowBracketDelta_flowEntry] at h_bal
        omega
      rcases ih m hk_rest h_bal' h_nfe' with hend | ⟨hm1, hfe1⟩
      · left; rw [h_len]; omega
      · right
        have hk1 : e.length + 1 + m + 1 < (e ++ fe :: rest).length := by rw [h_len]; omega
        refine ⟨hk1, ?_⟩
        have hidx : (e ++ fe :: rest)[e.length + 1 + m + 1]'hk1 = rest[m + 1]'hm1 := by
          have h1 : (e ++ fe :: rest)[e.length + 1 + m + 1]? = rest[m + 1]? := by
            rw [List.getElem?_append_right (by omega),
                show e.length + 1 + m + 1 - e.length = (m + 1) + 1 from by omega,
                List.getElem?_cons_succ]
          rw [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hm1] at h1
          exact Option.some.inj h1
        rw [hidx]; exact hfe1

/-- **Array/offset wrapper** for `SafeBodyUnit_succ`, against `flowBracketBalance` on the
    filtered token array with base offset `lo` — the value-end successor dual of
    `SafeBody_array_flowEntry`, in the shape the body characterizations consume. -/
theorem SafeBodyUnit_array_succ {Q : YamlToken → Prop}
    (arr : Array (Positioned YamlToken)) (lo : Nat)
    (h : SafeBodyUnit Q (arr.toList.drop lo)) :
    ∀ (k : Nat), lo ≤ k → (hk : k < arr.size) →
      flowBracketBalance arr lo (k + 1) = 0 → (arr[k]'hk).val ≠ .flowEntry →
      k + 1 = arr.size ∨
      ∃ (hk1 : k + 1 < arr.size), (arr[k+1]'hk1).val = .flowEntry := by
  intro k h_lo hk h_bal h_nfe
  have h_len : (arr.toList.drop lo).length = arr.size - lo := by
    rw [List.length_drop, Array.length_toList]
  have hj_lt : k - lo < (arr.toList.drop lo).length := by rw [h_len]; omega
  have h_drop_get : ((arr.toList.drop lo)[k - lo]'hj_lt).val = (arr[k]'hk).val := by
    rw [List.getElem_drop]
    rw [Array.getElem_toList (by omega)]
    congr 2
    omega
  have h_nfe' : ((arr.toList.drop lo)[k - lo]'hj_lt).val ≠ .flowEntry := by
    rw [h_drop_get]; exact h_nfe
  have h_bal' : pbalance ((arr.toList.drop lo).take ((k - lo) + 1)) = 0 := by
    have h_eq : flowBracketBalance arr lo (k + 1) =
        pbalance ((arr.toList.drop lo).take ((k + 1) - lo)) :=
      flowBracketBalance_eq_pbalance arr lo (k + 1) (by omega)
    rw [show (k + 1) - lo = (k - lo) + 1 from by omega] at h_eq
    rw [← h_eq]; exact h_bal
  rcases SafeBodyUnit_succ h (k - lo) hj_lt h_bal' h_nfe' with hend | ⟨hj1, hfe1⟩
  · left; rw [h_len] at hend; omega
  · right
    have hk1 : k + 1 < arr.size := by rw [h_len] at hj1; omega
    refine ⟨hk1, ?_⟩
    have h_get : ((arr.toList.drop lo)[(k - lo) + 1]'hj1).val = (arr[k+1]'hk1).val := by
      rw [List.getElem_drop]
      rw [Array.getElem_toList (by omega)]
      congr 2
      omega
    rw [← h_get]; exact hfe1

/-- The balance-relevant prefix of a *windowed* body `(arr.toList.take hi).drop lo` agrees with
    the unbounded `arr.toList.drop lo` prefix whenever the cut `k` lies within the window
    (`k ≤ hi`): both name exactly the elements `[lo, k)`.  This lets the windowed SafeBody wrappers
    below reuse `flowBracketBalance_eq_pbalance` (which is stated against the unbounded drop). -/
theorem window_prefix_eq (arr : Array (Positioned YamlToken)) (lo hi k : Nat)
    (h_k_hi : k ≤ hi) (h_hi_sz : hi ≤ arr.size) :
    ((arr.toList.take hi).drop lo).take (k - lo) = (arr.toList.drop lo).take (k - lo) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, Array.length_toList]
    omega
  · intro n h1 h2
    simp only [List.getElem_take, List.getElem_drop]

/-- **Windowed array wrapper** for `SafeBody_flowEntry_zero_balance`, over the bounded body slice
    `(arr.toList.take hi).drop lo` — the nested-subrange version of `SafeBody_array_flowEntry`
    (which is `drop lo`-to-end and so only applies to the outer span).  A depth-0 `.flowEntry`
    separator at `k ∈ [lo, hi)` is followed by a `Q`-token at `k + 1 < hi`.  This is the
    `SeqBodyProps.after_fe` substrate at an arbitrary guarded subrange (Phase J). -/
theorem SafeBody_array_flowEntry_window {Q : YamlToken → Prop}
    (arr : Array (Positioned YamlToken)) (lo hi : Nat) (h_hi : hi ≤ arr.size)
    (h : SafeBody Q ((arr.toList.take hi).drop lo)) :
    ∀ (k : Nat) (_hk_lo : lo ≤ k) (hk_hi : k < hi),
      (arr[k]'(Nat.lt_of_lt_of_le hk_hi h_hi)).val = .flowEntry →
      flowBracketBalance arr lo k = 0 →
      ∃ (hk1 : k + 1 < hi), Q (arr[k+1]'(Nat.lt_of_lt_of_le hk1 h_hi)).val := by
  intro k hk_lo hk_hi h_fe h_bal
  have hk_sz : k < arr.size := Nat.lt_of_lt_of_le hk_hi h_hi
  have h_len : ((arr.toList.take hi).drop lo).length = hi - lo := by
    rw [List.length_drop, List.length_take, Array.length_toList]; omega
  have hj_lt : k - lo < ((arr.toList.take hi).drop lo).length := by rw [h_len]; omega
  have h_get : (((arr.toList.take hi).drop lo)[k - lo]'hj_lt).val = (arr[k]'hk_sz).val := by
    rw [List.getElem_drop, List.getElem_take, Array.getElem_toList]
    congr 2; omega
  have h_fe' : (((arr.toList.take hi).drop lo)[k - lo]'hj_lt).val = .flowEntry := by
    rw [h_get]; exact h_fe
  have h_bal' : pbalance (((arr.toList.take hi).drop lo).take (k - lo)) = 0 := by
    rw [window_prefix_eq arr lo hi k (Nat.le_of_lt hk_hi) h_hi,
        ← flowBracketBalance_eq_pbalance arr lo k hk_lo]
    exact h_bal
  obtain ⟨hj1, hQ⟩ := SafeBody_flowEntry_zero_balance h (k - lo) hj_lt h_fe' h_bal'
  have hk1 : k + 1 < hi := by rw [h_len] at hj1; omega
  refine ⟨hk1, ?_⟩
  have hk1_sz : k + 1 < arr.size := Nat.lt_of_lt_of_le hk1 h_hi
  have h_get1 : (((arr.toList.take hi).drop lo)[(k - lo) + 1]'hj1).val = (arr[k+1]'hk1_sz).val := by
    rw [List.getElem_drop, List.getElem_take, Array.getElem_toList]
    congr 2; omega
  rw [← h_get1]; exact hQ

/-- **Windowed array wrapper** for `SafeBodyUnit_succ`, over the bounded body slice
    `(arr.toList.take hi).drop lo` — the value-end-successor dual of
    `SafeBody_array_flowEntry_window`, and the nested-subrange version of `SafeBodyUnit_array_succ`.
    A balanced-prefix end at `k ∈ [lo, hi)` that is not a `.flowEntry` separator is an entry END:
    the body close (`k + 1 = hi`) or a `.flowEntry` next.  This is the `SeqBodyProps.scalar_succ` /
    bracket-conjunct `h_succ` substrate at an arbitrary guarded subrange (Phase J). -/
theorem SafeBodyUnit_array_succ_window {Q : YamlToken → Prop}
    (arr : Array (Positioned YamlToken)) (lo hi : Nat) (h_hi : hi ≤ arr.size)
    (h : SafeBodyUnit Q ((arr.toList.take hi).drop lo)) :
    ∀ (k : Nat) (_hk_lo : lo ≤ k) (hk_hi : k < hi),
      flowBracketBalance arr lo (k + 1) = 0 →
      (arr[k]'(Nat.lt_of_lt_of_le hk_hi h_hi)).val ≠ .flowEntry →
      k + 1 = hi ∨
      ∃ (hk1 : k + 1 < hi), (arr[k+1]'(Nat.lt_of_lt_of_le hk1 h_hi)).val = .flowEntry := by
  intro k hk_lo hk_hi h_bal h_nfe
  have hk_sz : k < arr.size := Nat.lt_of_lt_of_le hk_hi h_hi
  have h_len : ((arr.toList.take hi).drop lo).length = hi - lo := by
    rw [List.length_drop, List.length_take, Array.length_toList]; omega
  have hj_lt : k - lo < ((arr.toList.take hi).drop lo).length := by rw [h_len]; omega
  have h_get : (((arr.toList.take hi).drop lo)[k - lo]'hj_lt).val = (arr[k]'hk_sz).val := by
    rw [List.getElem_drop, List.getElem_take, Array.getElem_toList]
    congr 2; omega
  have h_nfe' : (((arr.toList.take hi).drop lo)[k - lo]'hj_lt).val ≠ .flowEntry := by
    rw [h_get]; exact h_nfe
  have h_bal' : pbalance (((arr.toList.take hi).drop lo).take ((k - lo) + 1)) = 0 := by
    rw [show (k - lo) + 1 = (k + 1) - lo from by omega,
        window_prefix_eq arr lo hi (k + 1) hk_hi h_hi,
        ← flowBracketBalance_eq_pbalance arr lo (k + 1) (Nat.le_succ_of_le hk_lo)]
    exact h_bal
  rcases SafeBodyUnit_succ h (k - lo) hj_lt h_bal' h_nfe' with hend | ⟨hj1, hfe1⟩
  · left; rw [h_len] at hend; omega
  · right
    have hk1 : k + 1 < hi := by rw [h_len] at hj1; omega
    refine ⟨hk1, ?_⟩
    have hk1_sz : k + 1 < arr.size := Nat.lt_of_lt_of_le hk1 h_hi
    have h_get1 : (((arr.toList.take hi).drop lo)[(k - lo) + 1]'hj1).val = (arr[k+1]'hk1_sz).val := by
      rw [List.getElem_drop, List.getElem_take, Array.getElem_toList]
      congr 2; omega
    rw [← h_get1]; exact hfe1

/-- **`SafeBodyUnit` never ENDS in a depth-`0` separator** — the no-trailing-comma fact at the list
    level, the END-boundary dual of `SafeBodyUnit_succ`.  In a body of unit entries the LAST token
    (whose strict prefix `take k` returns to balance `0`) is the value-end of the final unit, never a
    `.flowEntry`: a depth-`0` `.flowEntry` is a separator BETWEEN units (the `cons` constructor's
    `fe`), but after the last unit there is no separator.  `EntryUnit`'s `≥ 1` interior condition
    forbids a depth-`0` split inside the final unit (so the prefix cannot return to `0` mid-entry),
    and `Q` (content-start) forbids a lone-`.flowEntry` unit.  Discharges the `h_noTrailingSep`
    premise of `flowBodyContent_of_deep` *vacuously* — its premise (last token is a depth-`0`
    `.flowEntry`) is refuted, so the residual no-trailing-comma fact comes from the SAME
    `SafeBodyUnit` substrate the producer already delivers via `RecSeqBody.toSafeBodyUnit`. -/
theorem SafeBodyUnit_last_not_sep {Q : YamlToken → Prop}
    (hQ : ∀ v, Q v → v ≠ .flowEntry)
    {body : List (Positioned YamlToken)} (h : SafeBodyUnit Q body) :
    ∀ (k : Nat) (hk : k < body.length),
      k + 1 = body.length → pbalance (body.take k) = 0 → (body[k]'hk).val ≠ .flowEntry := by
  induction h with
  | single e h_ne h_unit h_head =>
    intro k hk hlast h_bal
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- k = 0: the head; `Q (e.head).val` excludes `.flowEntry`
      subst hk0
      rw [List.head_eq_getElem] at h_head
      exact hQ _ h_head
    · -- k > 0: `e.take k` is a proper nonempty prefix at balance ≥ 1, contradicting = 0
      exfalso
      have := h_unit.2 k hkpos (by omega)
      omega
  | cons e fe rest h_ne h_unit h_head h_fe h_rest ih =>
    intro k hk hlast h_bal
    have h_len : (e ++ fe :: rest).length = e.length + 1 + rest.length := by
      simp [List.length_append]; omega
    -- `rest` is a `SafeBodyUnit`, hence nonempty, so the LAST position lies inside it.
    have h_rest_pos : 0 < rest.length := by
      cases h_rest with
      | single e' h_ne' _ _ => exact List.length_pos_iff.mpr h_ne'
      | cons e' fe' rest' _ _ _ _ _ => rw [List.length_append, List.length_cons]; omega
    obtain ⟨m, hm⟩ : ∃ m, k = e.length + 1 + m := ⟨k - e.length - 1, by rw [h_len] at hlast; omega⟩
    subst hm
    have hk_rest : m < rest.length := by rw [h_len] at hk; omega
    have hlast_rest : m + 1 = rest.length := by rw [h_len] at hlast; omega
    -- `body[e.length + 1 + m] = rest[m]`
    have hbody_k : (e ++ fe :: rest)[e.length + 1 + m]'hk = rest[m]'hk_rest := by
      have h1 : (e ++ fe :: rest)[e.length + 1 + m]? = rest[m]? := by
        rw [List.getElem?_append_right (by omega),
            show e.length + 1 + m - e.length = m + 1 from by omega, List.getElem?_cons_succ]
      rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk_rest] at h1
      exact Option.some.inj h1
    rw [hbody_k]
    -- prefix balance descends: `pbalance(body.take k) = pbalance e + δfe + pbalance(rest.take m)`.
    have htake : (e ++ fe :: rest).take (e.length + 1 + m) = e ++ fe :: rest.take m := by
      rw [List.take_append,
          List.take_of_length_le (show e.length ≤ e.length + 1 + m from by omega),
          show e.length + 1 + m - e.length = m + 1 from by omega, List.take_succ_cons]
    have h_bal' : pbalance (rest.take m) = 0 := by
      rw [htake, pbalance_append, pbalance_cons, h_unit.1, h_fe, flowBracketDelta_flowEntry] at h_bal
      omega
    exact ih m hk_rest hlast_rest h_bal'

/-- **Windowed array wrapper** for `SafeBodyUnit_last_not_sep`, over the bounded body slice
    `(arr.toList.take hi).drop lo` — the END-boundary dual of `SafeBodyUnit_array_succ_window`.  The
    last in-window position `k` (`k + 1 = hi`) whose prefix balance returns to `0` is NOT a `.flowEntry`
    separator.  Fed `exfalso`-style, this discharges the `noTrailingSepFact` residual at any guarded
    seq subrange: the windowed `SafeBodyUnit` the body producer delivers refutes a trailing comma. -/
theorem SafeBodyUnit_array_last_not_sep_window {Q : YamlToken → Prop}
    (hQ : ∀ v, Q v → v ≠ .flowEntry)
    (arr : Array (Positioned YamlToken)) (lo hi : Nat) (h_hi : hi ≤ arr.size)
    (h : SafeBodyUnit Q ((arr.toList.take hi).drop lo)) :
    ∀ (k : Nat), lo ≤ k → k + 1 = hi →
      flowBracketBalance arr lo k = 0 →
      arr[k]!.val ≠ .flowEntry := by
  intro k h_lo hk1 h_bal
  have hk_hi : k < hi := by omega
  have hk_sz : k < arr.size := Nat.lt_of_lt_of_le hk_hi h_hi
  rw [getElem!_pos arr k hk_sz]
  have h_len : ((arr.toList.take hi).drop lo).length = hi - lo := by
    rw [List.length_drop, List.length_take, Array.length_toList]; omega
  have hj_lt : k - lo < ((arr.toList.take hi).drop lo).length := by rw [h_len]; omega
  have h_get : (((arr.toList.take hi).drop lo)[k - lo]'hj_lt).val = (arr[k]'hk_sz).val := by
    rw [List.getElem_drop, List.getElem_take, Array.getElem_toList]
    congr 2; omega
  have h_bal' : pbalance (((arr.toList.take hi).drop lo).take (k - lo)) = 0 := by
    rw [window_prefix_eq arr lo hi k (Nat.le_of_lt hk_hi) h_hi,
        ← flowBracketBalance_eq_pbalance arr lo k h_lo]
    exact h_bal
  have hlast : (k - lo) + 1 = ((arr.toList.take hi).drop lo).length := by rw [h_len]; omega
  have h_not := SafeBodyUnit_last_not_sep hQ h (k - lo) hj_lt hlast h_bal'
  rw [h_get] at h_not
  exact h_not

/-- Prepending a delta-`0`, non-`.flowEntry` token to an `EntrySafe` entry keeps
    it `EntrySafe`: the head contributes nothing to the balance, and any interior
    `.flowEntry` is the tail's, whose prefix balance is unchanged by the head. -/
theorem EntrySafe_cons_delta_zero (t : Positioned YamlToken)
    (l : List (Positioned YamlToken))
    (h_delta : flowBracketDelta t.val = 0) (h_ne : t.val ≠ .flowEntry)
    (hl : EntrySafe l) : EntrySafe (t :: l) := by
  refine ⟨by rw [pbalance_cons, h_delta, hl.1]; omega, ?_⟩
  intro i h_i h_fe
  match i with
  | 0 => exact absurd (by rw [List.getElem_cons_zero] at h_fe; exact h_fe) h_ne
  | j + 1 =>
    have h_jl : j < l.length := by rw [List.length_cons] at h_i; omega
    have h_idx : (t :: l)[j + 1]'h_i = l[j]'h_jl := List.getElem_cons_succ t l j h_i
    rw [List.take_succ_cons, pbalance_cons, h_delta]
    have := hl.2 j h_jl (by rw [← h_idx]; exact h_fe)
    omega

/-! #### Typed bracket structure (`.body2.discharge.typedbrackets`)

`pbalance`/`WellBracketed` collapse `[`/`{` (and `]`/`}`) to a single ±1 delta, so they
witness the *flat* Dyck condition but **not** bracket-*type* matching — the untyped stream
`[ { ] }` is balanced yet mis-nested.  The `flow_parser_ok_of_structure` dispatcher, however,
consumes `SeqBodyProps.bracket_seq`'s `tokens[j]!.val = .flowSequenceEnd` (the matching close
of a `[` is specifically a `]`, not a `}`), which the matching locator
`flowBracketBalance_matching_close` alone cannot supply (it yields only `flowBracketDelta = -1`).

This is the **typed twin** of the `WellBracketed` algebra: a stack-fold tracking opener *types*
(`true` = `[`, `false` = `{`), with `none` recording a type-mismatch / underflow.  Its closure
lemmas mirror the `pbalance` family one-for-one (`_append`, `_singleton_delta_zero`,
`_cons_delta_zero`, `wrap_{seq,map}_typed`), so the producer chain that already threads
`WellBracketed` can thread `WellTyped` by the same mechanical substitution (cf. Reflection 203).
The payoff — the matching close of a depth-0 `[` is a `]` — is the *locator* layered on top
(future), bridging `WellTyped` to the `SeqBodyProps`/`MapBodyProps` bracket conjuncts. -/

/-- One step of the typed bracket stack.  `true` on the stack marks an open `[`, `false` an
    open `{`.  A closer pops only a matching opener; a mismatch or empty-stack pop is `none`. -/
def btStep (t : Positioned YamlToken) (s : List Bool) : Option (List Bool) :=
  match t.val with
  | .flowSequenceStart => some (true :: s)
  | .flowMappingStart  => some (false :: s)
  | .flowSequenceEnd   => match s with | true :: s' => some s' | _ => none
  | .flowMappingEnd    => match s with | false :: s' => some s' | _ => none
  | _                  => some s

/-- Fold the typed bracket stack across a token list (`none` is absorbing via `bind`). -/
def btFold (s0 : Option (List Bool)) (l : List (Positioned YamlToken)) : Option (List Bool) :=
  l.foldl (fun acc t => acc.bind (btStep t)) s0

/-- A token list whose brackets are correctly typed *and* balanced: the stack fold from the
    empty stack returns to the empty stack with no mismatch. -/
def WellTyped (l : List (Positioned YamlToken)) : Prop :=
  btFold (some []) l = some []

/-- The empty token list is `WellTyped` (the typed twin of `WellBracketed_nil`). -/
theorem WellTyped_nil : WellTyped [] := rfl

theorem btFold_cons (s0 : Option (List Bool)) (t : Positioned YamlToken)
    (rest : List (Positioned YamlToken)) :
    btFold s0 (t :: rest) = btFold (s0.bind (btStep t)) rest := by
  simp [btFold, List.foldl_cons]

theorem btFold_cons_some (s : List Bool) (t : Positioned YamlToken)
    (rest : List (Positioned YamlToken)) :
    btFold (some s) (t :: rest) = btFold (btStep t s) rest := by
  simp [btFold, List.foldl_cons, Option.bind]

theorem btFold_append (s0 : Option (List Bool)) (a b : List (Positioned YamlToken)) :
    btFold s0 (a ++ b) = btFold (btFold s0 a) b := by
  simp [btFold, List.foldl_append]

theorem btFold_none (l : List (Positioned YamlToken)) : btFold none l = none := by
  induction l with
  | nil => rfl
  | cons t rest ih => rw [btFold_cons]; exact ih

/-- A non-bracket token (`flowBracketDelta = 0`) leaves the typed stack unchanged. -/
theorem btStep_delta_zero (t : Positioned YamlToken) (s : List Bool)
    (h : flowBracketDelta t.val = 0) : btStep t s = some s := by
  unfold btStep
  cases hv : t.val <;> simp only [hv] at h ⊢ <;>
    first | rfl | simp [flowBracketDelta] at h

/-- **Stack-frame for a single step.**  If a step is defined over stack `s`, the same step
    over an extended stack `s ++ extra` leaves `extra` untouched. -/
theorem btStep_frame (t : Positioned YamlToken) (s m extra : List Bool)
    (h : btStep t s = some m) : btStep t (s ++ extra) = some (m ++ extra) := by
  unfold btStep at h ⊢
  cases hv : t.val <;> simp only [hv] at h ⊢ <;>
    first
      | (cases s with
         | nil => simp_all
         | cons b s' => cases b <;> simp_all)
      | (cases h; rfl)
      | simp_all

/-- **Stack-frame for a fold.**  A fold defined over stack `s` (ending at `m`) runs identically
    over an extended stack `s ++ extra`, ending at `m ++ extra`.  This is the inductive engine:
    a `WellTyped` body never underflows its starting stack, so it returns to it. -/
theorem btFold_frame (l : List (Positioned YamlToken)) :
    ∀ (s m extra : List Bool), btFold (some s) l = some m →
      btFold (some (s ++ extra)) l = some (m ++ extra) := by
  induction l with
  | nil =>
    intro s m extra h
    simp only [btFold, List.foldl_nil] at h ⊢
    obtain rfl := Option.some.inj h; rfl
  | cons t rest ih =>
    intro s m extra h
    rw [btFold_cons_some] at h ⊢
    cases hb : btStep t s with
    | none => rw [hb, btFold_none] at h; exact absurd h (by simp)
    | some m' =>
      rw [hb] at h
      rw [btStep_frame t s m' extra hb]
      exact ih m' m extra h

/-- A `WellTyped` body folded over *any* prefix stack returns to that prefix. -/
theorem WellTyped_frame (l : List (Positioned YamlToken)) (pre : List Bool)
    (h : WellTyped l) : btFold (some pre) l = some pre := by
  have := btFold_frame l [] [] pre h
  simpa using this

/-- A defined fold's prefix is defined (mirrors `WellTyped_prefix_some`, without `WellTyped`):
    `none` is absorbing, so an undefined prefix would force the whole fold to `none ≠ some r`. -/
theorem btFold_some_prefix (a b : List (Positioned YamlToken)) (r : List Bool)
    (h : btFold (some []) (a ++ b) = some r) : ∃ m, btFold (some []) a = some m := by
  rw [btFold_append] at h
  cases ha : btFold (some []) a with
  | none => rw [ha, btFold_none] at h; exact absurd h (by simp)
  | some s => exact ⟨s, rfl⟩

/-- A single delta-`0` token is `WellTyped`. -/
theorem WellTyped_singleton_delta_zero (t : Positioned YamlToken)
    (h : flowBracketDelta t.val = 0) : WellTyped [t] := by
  unfold WellTyped
  rw [btFold_cons_some]
  simp only [btFold, List.foldl_nil]
  exact btStep_delta_zero t [] h

/-- `WellTyped` is closed under concatenation (stack-fold homomorphism). -/
theorem WellTyped_append (a b : List (Positioned YamlToken))
    (ha : WellTyped a) (hb : WellTyped b) : WellTyped (a ++ b) := by
  unfold WellTyped at *
  rw [btFold_append, ha]; exact hb

/-- Prepending a delta-`0` token preserves `WellTyped` — the typed twin of
    `WellBracketed_cons_delta_zero`. -/
theorem WellTyped_cons_delta_zero (t : Positioned YamlToken)
    (l : List (Positioned YamlToken))
    (h_delta : flowBracketDelta t.val = 0) (h_wt : WellTyped l) : WellTyped (t :: l) := by
  have h : t :: l = [t] ++ l := rfl
  rw [h]
  exact WellTyped_append [t] l (WellTyped_singleton_delta_zero t h_delta) h_wt

/-- **Typed wrap (sequence).**  A `WellTyped` interior framed by `[ … ]` is `WellTyped`:
    the matching `]` pops exactly the `[` this lemma pushed.  The typed twin of
    `wrap_seq_block` — its payoff is that the close is provably a `]`, not a `}`. -/
theorem wrap_seq_typed (op cl : Positioned YamlToken) (body : List (Positioned YamlToken))
    (h_op : op.val = .flowSequenceStart) (h_cl : cl.val = .flowSequenceEnd)
    (h_body : WellTyped body) : WellTyped (op :: (body ++ [cl])) := by
  unfold WellTyped
  rw [btFold_cons_some]
  have hop : btStep op [] = some [true] := by unfold btStep; rw [h_op]
  rw [hop, btFold_append, WellTyped_frame body [true] h_body, btFold_cons_some]
  simp only [btFold, List.foldl_nil]
  unfold btStep; rw [h_cl]

/-- **Typed wrap (mapping).**  A `WellTyped` interior framed by `{ … }` is `WellTyped`. -/
theorem wrap_map_typed (op cl : Positioned YamlToken) (body : List (Positioned YamlToken))
    (h_op : op.val = .flowMappingStart) (h_cl : cl.val = .flowMappingEnd)
    (h_body : WellTyped body) : WellTyped (op :: (body ++ [cl])) := by
  unfold WellTyped
  rw [btFold_cons_some]
  have hop : btStep op [] = some [false] := by unfold btStep; rw [h_op]
  rw [hop, btFold_append, WellTyped_frame body [false] h_body, btFold_cons_some]
  simp only [btFold, List.foldl_nil]
  unfold btStep; rw [h_cl]

/-! #### Typed locator, part 1 — the depth–balance bridge (`.body2.discharge.typedlocator`)

The numeric locator `flowBracketBalance_matching_close` finds the matching close `j` of a
depth-0 opener at `k` purely from the `Int` balance and position index — it yields only
`flowBracketDelta tokens[j]!.val = -1` (a closer, `]` *or* `}`).  To pin the close's
*type* (a `[` matches a `]`, never a `}`), the typed stack `btFold` must be connected to
those numeric indices.

This bridge proves the typed stack's *length* equals the running `pbalance` (= the
`flowBracketBalance` the locator and `SeqBodyProps` speak): so "balance `1` at `j`" becomes
"stack `[b]` at `j`", and the lone element `b` is exactly the bracket type the close must
match.  The two `btStep_pop_eq_*` lemmas then read off the close's token from `b`.  The
remaining bottom-preservation step — that `b` equals the *opener* type at `k` (so the close
of a `[` is a `]`) — is the second sub-brick, layered above this. -/

/-- **One step shifts the stack length by exactly the bracket delta.**  A `[`/`{` push adds
    one, a matching `]`/`}` pop removes one, everything else is unchanged — mirroring
    `flowBracketDelta`.  The `none` (mismatch/underflow) cases are excluded by the hypothesis. -/
theorem btStep_length (t : Positioned YamlToken) (s s' : List Bool)
    (h : btStep t s = some s') :
    (s'.length : Int) = (s.length : Int) + flowBracketDelta t.val := by
  unfold btStep at h
  cases hv : t.val <;> simp only [hv] at h <;> simp only [flowBracketDelta] <;>
    first
      | (cases s with
         | nil => simp at h
         | cons b s'' => cases b <;> simp_all <;> omega)
      | (obtain rfl := Option.some.inj h; simp)

/-- **A `some`-valued fold shifts length by `pbalance`.**  Whenever the typed fold from a
    starting stack `s0` stays defined (`= some s1`), the final stack length differs from the
    initial by the cumulative bracket balance of the list. -/
theorem btFold_length (l : List (Positioned YamlToken)) :
    ∀ (s0 s1 : List Bool), btFold (some s0) l = some s1 →
      (s1.length : Int) = (s0.length : Int) + pbalance l := by
  induction l with
  | nil =>
    intro s0 s1 h
    simp only [btFold, List.foldl_nil] at h
    obtain rfl := Option.some.inj h
    simp [pbalance_nil]
  | cons t rest ih =>
    intro s0 s1 h
    rw [btFold_cons_some] at h
    cases hb : btStep t s0 with
    | none => rw [hb, btFold_none] at h; exact absurd h (by simp)
    | some m =>
      rw [hb] at h
      have hstep := btStep_length t s0 m hb
      have hrest := ih m s1 h
      rw [pbalance_cons]; omega

/-- **One-step frame inverse.**  If a step over the extended stack `s ++ extra` is defined and does
    not pop into `extra` (`0 ≤ s.length + flowBracketDelta t.val`, so a pop has something in `s` to
    remove), the same step is defined over `s` alone, and the extension is preserved.  The converse
    of `btStep_frame`. -/
theorem btStep_frame_inv (t : Positioned YamlToken) (s extra M : List Bool)
    (h_nopop : 0 ≤ (s.length : Int) + flowBracketDelta t.val)
    (h : btStep t (s ++ extra) = some M) :
    ∃ n, btStep t s = some n ∧ M = n ++ extra := by
  unfold btStep at h ⊢
  cases hv : t.val <;> simp only [hv] at h ⊢ <;>
    simp only [hv, flowBracketDelta] at h_nopop <;>
    first
      | (obtain rfl := Option.some.inj h; exact ⟨_, rfl, rfl⟩)
      | (cases s with
         | nil => simp only [List.length_nil] at h_nopop; omega
         | cons b s' => cases b <;> simp_all)

/-- **Fold frame inverse** — the converse of `btFold_frame`.  If the fold over the extended stack
    `s ++ extra` is defined (`= some m'`) and never pops into `extra` (absolute floor
    `0 ≤ s.length + pbalance (l.take k)` at every prefix), then the fold over `s` alone is defined and
    the extension is preserved (`m' = m ++ extra`).  The floor alone suffices for definedness of the
    smaller fold because every pop the big fold makes targets a within-`l` push (never `extra`), so the
    smaller fold replays the identical, defined decisions. -/
theorem btFold_frame_inv (l : List (Positioned YamlToken)) :
    ∀ (s extra m' : List Bool),
      (∀ k, k ≤ l.length → 0 ≤ (s.length : Int) + pbalance (l.take k)) →
      btFold (some (s ++ extra)) l = some m' →
      ∃ m, btFold (some s) l = some m ∧ m' = m ++ extra := by
  induction l with
  | nil =>
    intro s extra m' _ h
    simp only [btFold, List.foldl_nil] at h ⊢
    exact ⟨s, rfl, (Option.some.inj h).symm⟩
  | cons t rest ih =>
    intro s extra m' hfloor h
    rw [btFold_cons_some] at h
    have h_nopop : 0 ≤ (s.length : Int) + flowBracketDelta t.val := by
      have h1 := hfloor 1 (by simp)
      have htk : ((t :: rest).take 1) = [t] := by simp
      rw [htk, pbalance_singleton] at h1; exact h1
    cases hb : btStep t (s ++ extra) with
    | none => rw [hb, btFold_none] at h; exact absurd h (by simp)
    | some M =>
      rw [hb] at h
      obtain ⟨n, hn, hMn⟩ := btStep_frame_inv t s extra M h_nopop hb
      rw [btFold_cons_some, hn]
      have hstep_len : (n.length : Int) = (s.length : Int) + flowBracketDelta t.val :=
        btStep_length t s n hn
      have hfloor' : ∀ k, k ≤ rest.length → 0 ≤ (n.length : Int) + pbalance (rest.take k) := by
        intro k hk
        have hh := hfloor (k + 1) (by simp only [List.length_cons]; omega)
        have htk : ((t :: rest).take (k + 1)) = t :: rest.take k := by simp
        rw [htk, pbalance_cons] at hh
        rw [hstep_len]; omega
      exact ih n extra m' hfloor' (by rw [hMn] at h; exact h)

/-- **A prefix of a `WellTyped` list never underflows** — it folds to `some` (because `none`
    is absorbing, an underflowing prefix would force the whole fold to `none ≠ some []`). -/
theorem WellTyped_prefix_some (a b : List (Positioned YamlToken))
    (h : WellTyped (a ++ b)) : ∃ s, btFold (some []) a = some s := by
  unfold WellTyped at h
  rw [btFold_append] at h
  cases ha : btFold (some []) a with
  | none => rw [ha, btFold_none] at h; exact absurd h (by simp)
  | some s => exact ⟨s, rfl⟩

/-- **Depth–balance bridge.**  In a `WellTyped` list, the stack after any prefix `l.take m`
    is `some s` with `s.length` equal to that prefix's `pbalance`.  This is the glue between
    the typed-stack world (`WellTyped`) and the numeric `flowBracketBalance`/`pbalance` world
    where the matching locator and `SeqBodyProps` live. -/
theorem WellTyped_take_stack (l : List (Positioned YamlToken)) (m : Nat)
    (h : WellTyped l) :
    ∃ s, btFold (some []) (l.take m) = some s ∧ (s.length : Int) = pbalance (l.take m) := by
  have hsplit : l = l.take m ++ l.drop m := (List.take_append_drop m l).symm
  rw [hsplit] at h
  obtain ⟨s, hs⟩ := WellTyped_prefix_some _ _ h
  refine ⟨s, hs, ?_⟩
  have := btFold_length _ _ _ hs; simpa using this

/-- **Bridge: a non-empty typed stack at a prefix forces positive numeric balance** — the
    gate→locator hypothesis bridge for `(i'-b-locator-glue-gate-bridge)`.  Whenever the typed-stack
    head exists after the prefix `[0,a)` (`btFold`-top `= some hd`, for EITHER `hd = true` (seq) or
    `hd = false` (map) — so this serves both axes verbatim), the numeric `flowBracketBalance tokens 0 a`
    is `≥ 1`, exactly the hypothesis of `flowBracketBalance_backward_open_locate`.

    No new metric: the typed stack length and the numeric balance are the SAME integer
    (`btFold_length`: `s.length = pbalance (take a)`; `flowBracketBalance_eq_pbalance`:
    `flowBracketBalance tokens 0 a = pbalance (take a)`).  Both `[` and `{` push one stack element AND
    contribute `+1` via `flowBracketDelta`, so the count is uniform across seq/map — a non-empty stack
    (`btFold`-top `= some _`) ⇒ length `≥ 1` ⇒ balance `≥ 1` directly, with no per-step induction. -/
theorem flowBracketBalance_pos_of_btFold_head
    (tokens : Array (Positioned YamlToken)) (a : Nat) (hd : Bool)
    (h_mark : (btFold (some []) (tokens.toList.take a)).bind (·.head?) = some hd) :
    flowBracketBalance tokens 0 a ≥ 1 := by
  cases hbf : btFold (some []) (tokens.toList.take a) with
  | none => rw [hbf] at h_mark; simp at h_mark
  | some s =>
    rw [hbf] at h_mark
    have hs_ne : s ≠ [] := by
      intro h; subst h; simp at h_mark
    have hlen := btFold_length (tokens.toList.take a) [] s hbf
    simp only [List.length_nil] at hlen
    have hpb : flowBracketBalance tokens 0 a = pbalance (tokens.toList.take a) := by
      rw [flowBracketBalance_eq_pbalance tokens 0 a (Nat.zero_le a)]; simp
    have h1 : 1 ≤ s.length := by
      cases s with
      | nil => exact absurd rfl hs_ne
      | cons _ _ => simp
    rw [hpb]; omega

/-- **Reading the close type (sequence).**  The only `btStep` that pops `[true]` to `[]` is a
    `.flowSequenceEnd` — once the bridge fixes the stack at the close to `[true]`, this pins
    the close token to a `]`. -/
theorem btStep_pop_eq_seqEnd (t : Positioned YamlToken)
    (h : btStep t [true] = some []) : t.val = .flowSequenceEnd := by
  unfold btStep at h
  cases hv : t.val <;> simp only [hv] at h <;> simp_all

/-- **Reading the close type (mapping).**  The only `btStep` that pops `[false]` to `[]` is a
    `.flowMappingEnd`. -/
theorem btStep_pop_eq_mapEnd (t : Positioned YamlToken)
    (h : btStep t [false] = some []) : t.val = .flowMappingEnd := by
  unfold btStep at h
  cases hv : t.val <;> simp only [hv] at h <;> simp_all

/-! #### Typed locator, part 2 — bottom-preservation (`.body2.discharge.typedlocator.bottom`)

Part 1 (the depth–balance bridge) turns "balance `1` at the close `j`" into "the stack at `j`
is a singleton `[b]`", and `btStep_pop_eq_*` read the close token off `b`.  What is still open
is that `b` is the *opener* type: the close of a depth-0 `[` is a `]`, not a `}`.

This is the genuinely inductive step (cf. Reflection 204): the *bottom* of the stack — the
opener still waiting to be closed — is never popped while the depth stays `≥ 1`.  A `btStep`
only ever touches the *head* of the stack (push prepends, pop removes the head); so as long as
the stack stays non-empty across a span, its last element (`getLast?`, the bottom) is invariant.
Feeding `s0 = [true]` (just after a depth-0 `[`) and the interior span up to the matching close
then forces the close's singleton to be `[true]` as well — pinning the close type via part 1. -/

/-- `getLast?` ignores a `cons` onto a non-empty tail: the bottom (last) element is unchanged. -/
theorem getLast?_cons_ne (a : Bool) (s : List Bool) (hs : s ≠ []) :
    (a :: s).getLast? = s.getLast? := by
  cases s with
  | nil => exact absurd rfl hs
  | cons x xs => simp [List.getLast?_cons_cons]

/-- **One step preserves the stack bottom** (when neither stack is empty).  A push prepends to
    the head, a matching pop removes the head — both leave the last element untouched. -/
theorem btStep_getLast?_preserved (t : Positioned YamlToken) (s s' : List Bool)
    (hs : s ≠ []) (hs' : s' ≠ []) (h : btStep t s = some s') :
    s'.getLast? = s.getLast? := by
  unfold btStep at h
  cases hv : t.val <;> simp only [hv] at h <;>
    first
      | (obtain rfl := Option.some.inj h; rfl)
      | (obtain rfl := Option.some.inj h; exact getLast?_cons_ne _ _ hs)
      | (cases s with
         | nil => simp at h
         | cons b s'' =>
             cases b <;> simp at h <;>
               (subst h; exact (getLast?_cons_ne _ _ hs').symm))

/-- **Bottom-preservation across a positive-depth span.**  If the typed fold from a non-empty
    stack `s0` stays defined and the running depth (`s0.length + pbalance` of every prefix) never
    drops below `1`, the final stack has the *same bottom element* as `s0`.  The bottom opener is
    never popped while depth stays positive — this is the structural fact the type-collapsing
    numeric balance cannot see. -/
theorem btFold_getLast?_preserved (l : List (Positioned YamlToken)) :
    ∀ (s0 sf : List Bool), s0 ≠ [] →
      (∀ m, m ≤ l.length → 1 ≤ (s0.length : Int) + pbalance (l.take m)) →
      btFold (some s0) l = some sf →
      sf.getLast? = s0.getLast? := by
  induction l with
  | nil =>
    intro s0 sf _ _ h
    simp only [btFold, List.foldl_nil] at h
    obtain rfl := Option.some.inj h
    rfl
  | cons t rest ih =>
    intro s0 sf hs0 hpos h
    rw [btFold_cons_some] at h
    cases hb : btStep t s0 with
    | none => rw [hb, btFold_none] at h; exact absurd h (by simp)
    | some m =>
      rw [hb] at h
      have hlen : (m.length : Int) = (s0.length : Int) + flowBracketDelta t.val :=
        btStep_length t s0 m hb
      -- depth ≥ 1 after the first token keeps `m` non-empty
      have h1 := hpos 1 (by simp)
      have htake1 : ((t :: rest).take 1) = [t] := by simp
      rw [htake1, pbalance_singleton] at h1
      have hm_ne : m ≠ [] := by
        intro hmm
        rw [hmm, List.length_nil] at hlen
        omega
      have hstep := btStep_getLast?_preserved t s0 m hs0 hm_ne hb
      have hpos' : ∀ n, n ≤ rest.length → 1 ≤ (m.length : Int) + pbalance (rest.take n) := by
        intro n hn
        have hh := hpos (n + 1) (by simp only [List.length_cons]; omega)
        have htk : ((t :: rest).take (n + 1)) = t :: rest.take n := by simp
        rw [htk, pbalance_cons] at hh
        omega
      have hrec := ih m sf hm_ne hpos' h
      rw [hrec]; exact hstep

/-! #### Typed locator, part 3 — the typed matching close (`.body2.discharge.typedlocator.instantiate`)

Parts 1 (depth–balance bridge) and 2 (bottom-preservation) assemble here.  The numeric
`flowBracketBalance_matching_close` locates the matching close `j` of a depth-0 opener at `k`
and now (brick (c-iii-a)) also exposes the interior depth-positivity it maintained as a loop
invariant.  Feeding that positivity into `btFold_getLast?_preserved` with `s0 = [opener-bit]`
forces the stack just before the close to be the *same* singleton the opener pushed — so the
close `btStep`-pops it, and `btStep_pop_eq_{seqEnd,mapEnd}` read off the close's *type*.  The
payoff: `flowBracketBalance_matching_close_{seq,map}` — given a `WellTyped` interior, the
matching close of a `[` is a `]` (of a `{` is a `}`), exactly the `tokens[j]!.val` the
`SeqBodyProps`/`MapBodyProps` bracket conjuncts demand and the numeric balance cannot supply. -/

theorem btStep_val_congr (t t' : Positioned YamlToken) (s : List Bool)
    (h : t.val = t'.val) : btStep t s = btStep t' s := by
  unfold btStep; rw [h]

theorem btStep_emptypush_delta (t : Positioned YamlToken) (b : Bool)
    (h : btStep t [] = some [b]) : flowBracketDelta t.val = 1 := by
  unfold btStep at h
  cases hv : t.val <;> simp only [hv] at h <;>
    simp only [flowBracketDelta] <;>
    first | rfl | (exact absurd h (by simp))

/-- **Typed matching-close — generic core.**  Over a `WellTyped` body `B` bridged to the
    token array's `flowBracketBalance` (`hbal`) and values (`hval`), the matching close `j`
    of a depth-0 opener at `k` (numeric facts from `flowBracketBalance_matching_close`) pops
    the exact singleton `[b]` the opener pushed.  `B` is abstract so this avoids re-deriving
    the `take`/`drop` offset bridge inside `WellTyped`. -/
theorem matching_close_typed_generic
    (B : List (Positioned YamlToken)) (tokens : Array (Positioned YamlToken))
    (lo k j hi : Nat) (b : Bool)
    (hlenB : B.length = hi - lo)
    (hbal : ∀ t, lo ≤ t → t ≤ hi → pbalance (B.take (t - lo)) = flowBracketBalance tokens lo t)
    (hval : ∀ t, lo ≤ t → t < hi → ∀ (hb : t - lo < B.length),
      (B[t - lo]'hb).val = tokens[t]!.val)
    (h_wt : WellTyped B)
    (h_lo_k : lo ≤ k) (h_kj : k < j) (h_j_hi : j < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_k_depth : flowBracketBalance tokens lo k = 0)
    (h_k_push : btStep tokens[k]! [] = some [b])
    (h_inner : flowBracketBalance tokens (k+1) j = 0)
    (h_j_close : flowBracketDelta tokens[j]!.val = -1)
    (h_pos : ∀ i, k < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) :
    btStep tokens[j]! [b] = some [] := by
  have hstep : ∀ t, lo ≤ t → t < tokens.size →
      flowBracketBalance tokens lo (t+1) =
        flowBracketBalance tokens lo t + flowBracketDelta tokens[t]!.val := by
    intro t ht1 ht2
    have hszL : tokens.toList.length = tokens.size := rfl
    rw [flowBracketBalance_compose tokens lo t (t+1) ht1 (by omega),
        flowBracketBalance_single tokens t (by rw [hszL]; exact ht2),
        Array.getElem_toList ht2, ← getElem!_pos tokens t ht2]
  have h_kdelta : flowBracketDelta tokens[k]!.val = 1 := btStep_emptypush_delta _ _ h_k_push
  have h_lo_k1 : flowBracketBalance tokens lo (k+1) = 1 := by
    have e := hstep k h_lo_k (by omega); omega
  have h_lo_j : flowBracketBalance tokens lo j = 1 := by
    have e := flowBracketBalance_compose tokens lo (k+1) j (by omega) (by omega); omega
  have h_lo_j1 : flowBracketBalance tokens lo (j+1) = 0 := by
    have e := hstep j (by omega) (by omega); omega
  have hKlt : k - lo < B.length := by rw [hlenB]; omega
  have hJlt : j - lo < B.length := by rw [hlenB]; omega
  -- Stack after opener prefix is `[b]`.
  have hopen : btFold (some []) (B.take (k - lo + 1)) = some [b] := by
    rw [List.take_succ_eq_append_getElem hKlt, btFold_append]
    obtain ⟨s, hs, hslen⟩ := WellTyped_take_stack B (k - lo) h_wt
    have hsK0 : pbalance (B.take (k - lo)) = 0 := by rw [hbal k h_lo_k (by omega), h_k_depth]
    rw [hsK0] at hslen
    have hsnil : s = [] := List.eq_nil_of_length_eq_zero (by exact_mod_cast hslen)
    rw [hs, hsnil]
    have hsingle : btFold (some ([] : List Bool)) [B[k - lo]'hKlt]
        = btStep (B[k - lo]'hKlt) [] := by simp [btFold, List.foldl]
    rw [hsingle, btStep_val_congr (B[k - lo]'hKlt) tokens[k]! [] (hval k h_lo_k (by omega) hKlt)]
    exact h_k_push
  -- Stack just before the close is `[b]`.
  have hbefore : btFold (some []) (B.take (j - lo)) = some [b] := by
    have hsplit : B.take (j - lo)
        = B.take (k - lo + 1) ++ (B.drop (k - lo + 1)).take ((j - lo) - (k - lo + 1)) := by
      rw [← List.take_add]; congr 1; omega
    obtain ⟨sf, hsf, hsflen⟩ := WellTyped_take_stack B (j - lo) h_wt
    rw [hsplit, btFold_append, hopen] at hsf
    have hsflen' : (sf.length : Int) = 1 := by
      rw [hsflen, hbal j (by omega) (by omega), h_lo_j]
    have hpos_seg : ∀ m, m ≤ ((B.drop (k - lo + 1)).take ((j - lo) - (k - lo + 1))).length →
        1 ≤ (([b] : List Bool).length : Int)
            + pbalance (((B.drop (k - lo + 1)).take ((j - lo) - (k - lo + 1))).take m) := by
      intro m hm
      rw [List.length_take] at hm
      have hmtake : ((B.drop (k - lo + 1)).take ((j - lo) - (k - lo + 1))).take m
          = (B.drop (k - lo + 1)).take m := by
        rw [List.take_take]; congr 1; omega
      rw [hmtake]
      have hcat : B.take (k - lo + 1) ++ (B.drop (k - lo + 1)).take m = B.take (k - lo + 1 + m) := by
        rw [← List.take_add]
      have hk1 : pbalance (B.take (k - lo + 1)) = 1 := by
        rw [show k - lo + 1 = (k + 1) - lo from by omega, hbal (k + 1) (by omega) (by omega), h_lo_k1]
      have key : pbalance (B.take (k - lo + 1)) + pbalance ((B.drop (k - lo + 1)).take m)
          = flowBracketBalance tokens lo (k + 1 + m) := by
        rw [← pbalance_append, hcat, show k - lo + 1 + m = (k + 1 + m) - lo from by omega,
            hbal (k + 1 + m) (by omega) (by omega)]
      have hge := h_pos (k + 1 + m) (by omega) (by omega)
      have hlen1 : (([b] : List Bool).length : Int) = 1 := by simp
      rw [hlen1]; omega
    have hbot := btFold_getLast?_preserved _ [b] sf (by simp) hpos_seg hsf
    have hsf_eq : sf = [b] := by
      rcases sf with _ | ⟨x, xs⟩
      · simp at hsflen'
      · rcases xs with _ | ⟨y, ys⟩
        · have hxb : x = b := by simpa using hbot
          rw [hxb]
        · simp only [List.length_cons] at hsflen'; omega
    rw [hsf_eq] at hsf
    rw [hsplit, btFold_append, hopen]
    exact hsf
  -- The close pops `[b]`.
  have hclose : btFold (some []) (B.take (j - lo + 1)) = btStep (B[j - lo]'hJlt) [b] := by
    rw [List.take_succ_eq_append_getElem hJlt, btFold_append, hbefore]
    simp [btFold, List.foldl]
  obtain ⟨s', hs', hs'len⟩ := WellTyped_take_stack B (j - lo + 1) h_wt
  rw [hclose] at hs'
  have hpb' : pbalance (B.take (j - lo + 1)) = flowBracketBalance tokens lo (j + 1) := by
    rw [show j - lo + 1 = (j + 1) - lo from by omega, hbal (j + 1) (by omega) (by omega)]
  rw [hpb', h_lo_j1] at hs'len
  have hs'nil : s' = [] := List.eq_nil_of_length_eq_zero (by exact_mod_cast hs'len)
  rw [hs'nil] at hs'
  rw [btStep_val_congr (B[j - lo]'hJlt) tokens[j]! [b] (hval j (by omega) h_j_hi hJlt)] at hs'
  exact hs'

/-- **Typed matching-close — array core.**  Specializes `matching_close_typed_generic` to the
    interior slice `[lo, hi)` of the token array, proving the `length`/`balance`/`value`
    bridges for that concrete `B`. -/
theorem matching_close_typed_core
    (tokens : Array (Positioned YamlToken)) (lo k j hi : Nat) (b : Bool)
    (h_lo_k : lo ≤ k) (h_kj : k < j) (h_j_hi : j < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_k_depth : flowBracketBalance tokens lo k = 0)
    (h_k_push : btStep tokens[k]! [] = some [b])
    (h_inner : flowBracketBalance tokens (k+1) j = 0)
    (h_j_close : flowBracketDelta tokens[j]!.val = -1)
    (h_pos : ∀ i, k < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo)) :
    btStep tokens[j]! [b] = some [] := by
  rw [List.drop_take] at h_wt
  have hszL : tokens.toList.length = tokens.size := rfl
  have hlenB : ((tokens.toList.drop lo).take (hi - lo)).length = hi - lo := by
    rw [List.length_take, List.length_drop, hszL]; omega
  have hbal : ∀ t, lo ≤ t → t ≤ hi →
      pbalance (((tokens.toList.drop lo).take (hi - lo)).take (t - lo))
        = flowBracketBalance tokens lo t := by
    intro t ht1 ht2
    rw [List.take_take, show min (t - lo) (hi - lo) = t - lo from by omega,
        ← flowBracketBalance_eq_pbalance tokens lo t ht1]
  have hval : ∀ t, lo ≤ t → t < hi → ∀ (hb : t - lo < ((tokens.toList.drop lo).take (hi - lo)).length),
      (((tokens.toList.drop lo).take (hi - lo))[t - lo]'hb).val = tokens[t]!.val := by
    intro t ht1 ht2 hb
    have h1 : ((tokens.toList.drop lo).take (hi - lo))[t - lo]'hb = tokens[t]! := by
      rw [List.getElem_take, List.getElem_drop,
          Array.getElem_toList (show lo + (t - lo) < tokens.size from by omega),
          ← getElem!_pos tokens (lo + (t - lo)) (by omega)]
      congr 1; omega
    rw [h1]
  exact matching_close_typed_generic ((tokens.toList.drop lo).take (hi - lo)) tokens lo k j hi b
    hlenB hbal hval h_wt h_lo_k h_kj h_j_hi h_hi_sz h_k_depth h_k_push h_inner h_j_close h_pos

theorem flowBracketBalance_matching_close_seq
    (tokens : Array (Positioned YamlToken)) (lo k hi : Nat)
    (h_lo_k : lo ≤ k) (h_k_hi : k < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_k_depth : flowBracketBalance tokens lo k = 0)
    (h_k_open : tokens[k]!.val = .flowSequenceStart)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo)) :
    ∃ j, k < j ∧ j < hi ∧ tokens[j]!.val = .flowSequenceEnd ∧
      flowBracketBalance tokens (k+1) j = 0 := by
  have h_k_open_delta : flowBracketDelta tokens[k]!.val = 1 := by rw [h_k_open]; rfl
  obtain ⟨j, hkj, hjhi, hjdelta, hinner, hpos⟩ :=
    flowBracketBalance_matching_close tokens lo k hi h_lo_k h_k_hi h_hi_sz
      h_k_depth h_k_open_delta h_total h_dyck
  have h_k_push : btStep tokens[k]! [] = some [true] := by unfold btStep; rw [h_k_open]
  have hpop := matching_close_typed_core tokens lo k j hi true h_lo_k hkj hjhi h_hi_sz
    h_k_depth h_k_push hinner hjdelta hpos h_wt
  exact ⟨j, hkj, hjhi, btStep_pop_eq_seqEnd _ hpop, hinner⟩

theorem flowBracketBalance_matching_close_map
    (tokens : Array (Positioned YamlToken)) (lo k hi : Nat)
    (h_lo_k : lo ≤ k) (h_k_hi : k < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_k_depth : flowBracketBalance tokens lo k = 0)
    (h_k_open : tokens[k]!.val = .flowMappingStart)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo)) :
    ∃ j, k < j ∧ j < hi ∧ tokens[j]!.val = .flowMappingEnd ∧
      flowBracketBalance tokens (k+1) j = 0 := by
  have h_k_open_delta : flowBracketDelta tokens[k]!.val = 1 := by rw [h_k_open]; rfl
  obtain ⟨j, hkj, hjhi, hjdelta, hinner, hpos⟩ :=
    flowBracketBalance_matching_close tokens lo k hi h_lo_k h_k_hi h_hi_sz
      h_k_depth h_k_open_delta h_total h_dyck
  have h_k_push : btStep tokens[k]! [] = some [false] := by unfold btStep; rw [h_k_open]
  have hpop := matching_close_typed_core tokens lo k j hi false h_lo_k hkj hjhi h_hi_sz
    h_k_depth h_k_push hinner hjdelta hpos h_wt
  exact ⟨j, hkj, hjhi, btStep_pop_eq_mapEnd _ hpop, hinner⟩

/-! #### Typed locator, part 4 — balanced-factor extraction for nested subranges
    (`.body2.discharge.typedlocator.infix`)

The two `flowBracketBalance_matching_close_{seq,map}` lemmas demand `WellTyped` of the
*subrange* interior `((tokens.toList.take hi).drop lo)`.  When assembling `FlowSubrangesOk`,
that subrange is **nested**: only the *global* interior is known `WellTyped`, and the
universal `FlowSubrangesOk.seq`/`.map` hand the proof no per-subrange `WellTyped` hypothesis.

This part supplies the descent engine.  `btFold_unframe` is the down-direction dual of the
existing `btFold_frame`: a fold over an extended stack `s ++ extra` that never pops into
`extra` (a Dyck guard) runs identically over `s` alone.  `WellTyped_infix_balanced` then reads
off the payoff — a balanced, Dyck infix of a `WellTyped` list is itself `WellTyped`, at *any*
nesting depth — because feasibility of the infix from the empty stack is recovered by
un-framing the (feasible-because-prefix) `pre ++ m`, and balance-`0` forces the stack back to
`[]`.  No Dyck-tracking re-proof of type-matching is needed: the matches come for free from the
ambient `WellTyped`. -/

/-- **Step-level un-frame.**  If a step over an *extended* stack `s ++ extra` is defined, and a
    pop never reaches into `extra` (guard: a closer requires `s` non-empty), then the same step
    over `s` alone is defined and the result is the un-extended stack `s' ++ extra`.  The
    converse of `btStep_frame`. -/
theorem btStep_unframe (t : Positioned YamlToken) (s extra r : List Bool)
    (h : btStep t (s ++ extra) = some r)
    (hguard : flowBracketDelta t.val = -1 → s ≠ []) :
    ∃ s', btStep t s = some s' ∧ r = s' ++ extra := by
  unfold btStep at h ⊢
  cases hv : t.val <;> simp only [hv] at h ⊢ <;>
    first
      | exact ⟨_, rfl, by obtain rfl := Option.some.inj h; rfl⟩
      | (have hs : s ≠ [] := hguard (by rw [hv]; rfl)
         cases s with
         | nil => exact absurd rfl hs
         | cons b s0 =>
             cases b <;>
               first
                 | exact ⟨s0, rfl, by obtain rfl := Option.some.inj h; rfl⟩
                 | simp_all)

/-- **Fold-level un-frame.**  A fold over an extended stack `s ++ extra` that never pops into
    `extra` (Dyck guard: every prefix keeps `s.length + pbalance ≥ 0`) runs identically over `s`
    alone, ending one un-extended stack lower.  This is the down-direction dual of `btFold_frame`;
    the guard is what `btFold_frame` gets for free in the up-direction. -/
theorem btFold_unframe (m : List (Positioned YamlToken)) :
    ∀ (s extra mfull : List Bool),
      btFold (some (s ++ extra)) m = some mfull →
      (∀ i, i ≤ m.length → (s.length : Int) + pbalance (m.take i) ≥ 0) →
      ∃ m', btFold (some s) m = some m' ∧ mfull = m' ++ extra := by
  induction m with
  | nil =>
    intro s extra mfull h _
    simp only [btFold, List.foldl_nil] at h
    obtain rfl := Option.some.inj h
    exact ⟨s, rfl, rfl⟩
  | cons t rest ih =>
    intro s extra mfull h hguard
    rw [btFold_cons_some] at h
    cases hb : btStep t (s ++ extra) with
    | none => rw [hb, btFold_none] at h; exact absurd h (by simp)
    | some r =>
      rw [hb] at h
      have hstepguard : flowBracketDelta t.val = -1 → s ≠ [] := by
        intro hd
        have hg1 := hguard 1 (by simp)
        have htake : ((t :: rest).take 1) = [t] := rfl
        rw [htake, pbalance_singleton, hd] at hg1
        rintro rfl
        simp at hg1
      obtain ⟨s', hss', hr⟩ := btStep_unframe t s extra r hb hstepguard
      have hlen := btStep_length t s s' hss'
      rw [btFold_cons_some, hss']
      subst hr
      have hguard' : ∀ i, i ≤ rest.length → (s'.length : Int) + pbalance (rest.take i) ≥ 0 := by
        intro i hi
        have hg := hguard (i + 1) (by simp; omega)
        have htake : ((t :: rest).take (i + 1)) = t :: rest.take i := rfl
        rw [htake, pbalance_cons] at hg
        omega
      exact ih s' extra mfull h hguard'

/-- **Typed balanced-factor extraction.**  An infix `m` of a `WellTyped` list that is itself
    balanced (`pbalance m = 0`) and Dyck (every prefix `pbalance ≥ 0`) is `WellTyped` — *at any
    nesting depth*, because feasibility of `m` from the empty stack is recovered by un-framing the
    (feasible) prefix `pre ++ m`, and balance-`0` forces the resulting stack back to `[]`.  This
    discharges the `WellTyped` hypothesis that `flowBracketBalance_matching_close_{seq,map}` demand
    for *nested* subranges, where the global `WellTyped` is all that is on hand. -/
theorem WellTyped_infix_balanced (pre m suf : List (Positioned YamlToken))
    (h : WellTyped (pre ++ m ++ suf))
    (hbal : pbalance m = 0)
    (hdyck : ∀ i, i ≤ m.length → pbalance (m.take i) ≥ 0) :
    WellTyped m := by
  -- feasibility of the prefix `pre` and of `pre ++ m`
  have hA : pre ++ m ++ suf = pre ++ (m ++ suf) := by rw [List.append_assoc]
  obtain ⟨sp, hsp⟩ := WellTyped_prefix_some pre (m ++ suf) (hA ▸ h)
  obtain ⟨sp', hsp'⟩ := WellTyped_prefix_some (pre ++ m) suf h
  unfold WellTyped at h ⊢
  rw [btFold_append, hsp] at hsp'
  -- un-frame `m` from the empty stack with frame `sp`
  obtain ⟨m', hm', _⟩ :=
    btFold_unframe m [] sp sp' (by simpa using hsp')
      (by intro i hi; simpa using hdyck i hi)
  -- balance-0 forces `m' = []`
  have hlen := btFold_length m [] m' hm'
  rw [hbal] at hlen
  have hz : m'.length = 0 := by
    have : (m'.length : Int) = 0 := by simpa using hlen
    exact_mod_cast this
  rw [hm', List.eq_nil_of_length_eq_zero hz]

/-! #### Typed locator, part 5 — subrange `WellTyped` in `flowBracketBalance` language
    (`.body2.discharge.typedlocator.subrange`)

`WellTyped_infix_balanced` speaks list infixes (`pre ++ m ++ suf`, `pbalance`); the consumers
— `FlowSubrangesOk.seq`/`.map` and `flowBracketBalance_matching_close_{seq,map}` — speak array
indices and `flowBracketBalance`.  This part bridges the two: a nested subrange `[lo, hi)` of a
`WellTyped` enclosing slice `[LO, HI)`, given its balance (`flowBracketBalance lo hi = 0`) and
its *local* Dyck (`flowBracketBalance lo p ≥ 0` for every `lo ≤ p ≤ hi`), is `WellTyped`.  The
enclosing slice splits as `pre ++ m ++ suf` with `m` the subrange; the `flowBracketBalance_eq_pbalance`
bridge converts both balance facts into the `pbalance` form the engine takes.  The local Dyck is
*not* free from `FlowSubrangesOk`'s hypotheses — deriving it from the global Dyck is the remaining
`(d-dyck)` brick; here it is a clean input so the assembly can feed it once established. -/

/-- **Subrange `WellTyped` in `flowBracketBalance` language.**  A nested subrange `[lo, hi)`
    of a `WellTyped` enclosing slice `[LO, HI)` that is itself balanced and locally Dyck
    (every prefix balance from `lo` stays `≥ 0`) is `WellTyped`.  Packages
    `WellTyped_infix_balanced` behind the `flowBracketBalance`/array-index interface that
    `FlowSubrangesOk` and `flowBracketBalance_matching_close_{seq,map}` consume. -/
theorem WellTyped_subrange (tokens : Array (Positioned YamlToken)) (LO lo hi HI : Nat)
    (hLO : LO ≤ lo) (h_lo_hi : lo ≤ hi) (hHI : hi ≤ HI)
    (h_HI_sz : HI ≤ tokens.size)
    (hW : WellTyped ((tokens.toList.take HI).drop LO))
    (h_bal : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ p, lo ≤ p → p ≤ hi → flowBracketBalance tokens lo p ≥ 0) :
    WellTyped ((tokens.toList.take hi).drop lo) := by
  rw [List.drop_take] at hW
  -- Split the enclosing slice into pre ++ (m ++ suf), with m the subrange.
  have hsplit : (tokens.toList.drop LO).take (HI - LO)
      = (tokens.toList.drop LO).take (lo - LO)
        ++ ((tokens.toList.drop lo).take (hi - lo)
            ++ (tokens.toList.drop hi).take (HI - hi)) := by
    rw [show HI - LO = (lo - LO) + (HI - lo) from by omega, List.take_add,
        List.drop_drop, show LO + (lo - LO) = lo from by omega,
        show HI - lo = (hi - lo) + (HI - hi) from by omega, List.take_add,
        List.drop_drop, show lo + (hi - lo) = hi from by omega]
  rw [hsplit, ← List.append_assoc] at hW
  -- Balance bridge: pbalance of the subrange slice = flowBracketBalance lo hi = 0.
  have hbal : pbalance ((tokens.toList.drop lo).take (hi - lo)) = 0 := by
    rw [← flowBracketBalance_eq_pbalance tokens lo hi h_lo_hi]; exact h_bal
  have hlenm : ((tokens.toList.drop lo).take (hi - lo)).length = hi - lo := by
    rw [List.length_take, List.length_drop]
    have hsz : tokens.toList.length = tokens.size := rfl
    omega
  -- Local Dyck bridge: every prefix balance of the slice = flowBracketBalance lo (lo+i) ≥ 0.
  have hdyck' : ∀ i, i ≤ ((tokens.toList.drop lo).take (hi - lo)).length →
      pbalance (((tokens.toList.drop lo).take (hi - lo)).take i) ≥ 0 := by
    intro i hi_le
    rw [hlenm] at hi_le
    rw [List.take_take, show min i (hi - lo) = i from by omega]
    have hb : pbalance ((tokens.toList.drop lo).take i)
        = flowBracketBalance tokens lo (lo + i) := by
      rw [flowBracketBalance_eq_pbalance tokens lo (lo + i) (by omega),
          show lo + i - lo = i from by omega]
    rw [hb]
    exact h_dyck (lo + i) (by omega) (by omega)
  have hres := WellTyped_infix_balanced
      ((tokens.toList.drop LO).take (lo - LO))
      ((tokens.toList.drop lo).take (hi - lo))
      ((tokens.toList.drop hi).take (HI - hi))
      hW hbal hdyck'
  rw [List.drop_take]
  exact hres

/-! #### Typed locator, part 6 — bracket-conjunct assembly (`.body2.discharge.typedlocator.assemble`)

Parts 1–5 deliver the two halves of a nested-bracket conjunct: the typed locator
`flowBracketBalance_matching_close_{seq,map}` gives the matching close's *position and type*
(`tokens[j]!.val = .flowSequenceEnd`/`.flowMappingEnd` with balanced interior), and the landed
successor reduction `seq_bracket_succ_reduce` (in `ParserGrammable`, via the matched pair's
depth-transparency `flowBracketBalance_after_bracket_pair_zero`) attaches the *successor* from
the single shared emitter fact.

This part bolts them together into the exact `SeqBodyProps.bracket_seq`/`bracket_map` conjunct
shapes `flow_parser_ok_of_structure` consumes.  The lone remaining input is `h_succ` — the
"next depth-0 token after a complete value is `.flowEntry` or the body close" emitter fact.  It is
**guarded by the locator's own output** `flowBracketDelta tokens[j]!.val = -1` (a value-*close* at
`j`): without that guard the bare `balance lo (j+1) = 0` premise also holds at every *separator*
`j` (where `tokens[j+1]` is the next entry's content-start, not `.flowEntry`/close), so the
unguarded universal is *undischargeable* — the guard restricts the quantifier to the value-end
positions the fact is actually about.  It is *the same* fact `scalar_succ` needs (after the
depth-transparency reduction collapses the bracketed value to its close), so `(d-shape)` reduces to
one emitter obligation per body kind.  A seq body always closes with `.flowSequenceEnd`, so **both**
conjuncts carry the seq successor (`FE ∨ (seqEnd ∧ j+1=hi)`), even a bracketed-*map* item (`{…}`) —
only the close-type and which locator differ. -/

/-- **`SeqBodyProps.bracket_seq` assembled.**  A depth-0 `[` opener at `k` in a well-bracketed,
    `WellTyped` seq body `[lo, hi)` yields the full `bracket_seq` conjunct: matching `]` at `j`
    with balanced interior (typed locator), plus the `FE ∨ (seqEnd ∧ j+1=hi)` successor
    (`seq_bracket_succ_reduce` from `h_succ`). -/
theorem seq_bracket_seq_conjunct (tokens : Array (Positioned YamlToken))
    (lo hi k : Nat) (h_lo_k : lo ≤ k) (h_k_hi : k < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_k_depth : flowBracketBalance tokens lo k = 0)
    (h_k_open : tokens[k]!.val = .flowSequenceStart)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo))
    (h_succ : ∀ j, k < j → j < hi → flowBracketDelta tokens[j]!.val = -1 →
      flowBracketBalance tokens lo (j+1) = 0 →
      j + 1 ≤ hi ∧
      (tokens[j+1]!.val = .flowEntry ∨
       (tokens[j+1]!.val = .flowSequenceEnd ∧ j + 1 = hi))) :
    ∃ j, k < j ∧ j < hi ∧
      tokens[j]!.val = .flowSequenceEnd ∧
      flowBracketBalance tokens (k+1) j = 0 ∧
      j + 1 ≤ hi ∧
      (tokens[j+1]!.val = .flowEntry ∨
       (tokens[j+1]!.val = .flowSequenceEnd ∧ j + 1 = hi)) := by
  obtain ⟨j, hkj, hjhi, hjval, hinner⟩ :=
    flowBracketBalance_matching_close_seq tokens lo k hi h_lo_k h_k_hi h_hi_sz
      h_k_depth h_k_open h_total h_dyck h_wt
  have h_j_sz : j < tokens.size := Nat.lt_of_lt_of_le hjhi h_hi_sz
  have h_open_delta : flowBracketDelta tokens[k]!.val = 1 := by rw [h_k_open]; rfl
  have h_close_delta : flowBracketDelta tokens[j]!.val = -1 := by rw [hjval]; rfl
  have hsucc := seq_bracket_succ_reduce tokens lo hi k j h_lo_k hkj h_j_sz
    h_k_depth h_open_delta h_close_delta hinner (fun hd => h_succ j hkj hjhi h_close_delta hd)
  exact ⟨j, hkj, hjhi, hjval, hinner, hsucc.1, hsucc.2⟩

/-- **`SeqBodyProps.bracket_map` assembled.**  A depth-0 `{` opener at `k` in a seq body yields
    the `bracket_map` conjunct: matching `}` at `j` (typed locator `..._map`) with balanced
    interior, plus the SAME seq-body successor — a seq body closes with `.flowSequenceEnd`, so a
    bracketed-map item still routes through `seq_bracket_succ_reduce`. -/
theorem seq_bracket_map_conjunct (tokens : Array (Positioned YamlToken))
    (lo hi k : Nat) (h_lo_k : lo ≤ k) (h_k_hi : k < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_k_depth : flowBracketBalance tokens lo k = 0)
    (h_k_open : tokens[k]!.val = .flowMappingStart)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo))
    (h_succ : ∀ j, k < j → j < hi → flowBracketDelta tokens[j]!.val = -1 →
      flowBracketBalance tokens lo (j+1) = 0 →
      j + 1 ≤ hi ∧
      (tokens[j+1]!.val = .flowEntry ∨
       (tokens[j+1]!.val = .flowSequenceEnd ∧ j + 1 = hi))) :
    ∃ j, k < j ∧ j < hi ∧
      tokens[j]!.val = .flowMappingEnd ∧
      flowBracketBalance tokens (k+1) j = 0 ∧
      j + 1 ≤ hi ∧
      (tokens[j+1]!.val = .flowEntry ∨
       (tokens[j+1]!.val = .flowSequenceEnd ∧ j + 1 = hi)) := by
  obtain ⟨j, hkj, hjhi, hjval, hinner⟩ :=
    flowBracketBalance_matching_close_map tokens lo k hi h_lo_k h_k_hi h_hi_sz
      h_k_depth h_k_open h_total h_dyck h_wt
  have h_j_sz : j < tokens.size := Nat.lt_of_lt_of_le hjhi h_hi_sz
  have h_open_delta : flowBracketDelta tokens[k]!.val = 1 := by rw [h_k_open]; rfl
  have h_close_delta : flowBracketDelta tokens[j]!.val = -1 := by rw [hjval]; rfl
  have hsucc := seq_bracket_succ_reduce tokens lo hi k j h_lo_k hkj h_j_sz
    h_k_depth h_open_delta h_close_delta hinner (fun hd => h_succ j hkj hjhi h_close_delta hd)
  exact ⟨j, hkj, hjhi, hjval, hinner, hsucc.1, hsucc.2⟩

/-! **Typed locator, part 7 — bracket-conjunct assembly (map side).**

The map analogues of the seq conjuncts.  Two differences from the seq side: the opener sits at
`k+1` (one past the `.key`/`.value` at depth-0 `k`, whose depth-0 the caller supplies as
`h_k1_depth`), and the opener *kind* is genuinely a 2-way disjunction in the conjunct hypothesis —
so the kind split (`.flowSequenceStart` vs `.flowMappingStart`) lives *inside* these lemmas, each
branch calling its matching typed locator and re-asserting the kind in the output disjunction.
The successor is governed by what the body is doing: after a `.key` it is `.value`
(`map_key_bracket_value_reduce`, M5); after a `.value` it is the map body close
(`map_value_bracket_succ_reduce`, `FE ∨ (mapEnd ∧ j+1=hi)`, M8).  As on the seq side, the `h_succ`
emitter premise is **guarded by the value-close fact** `flowBracketDelta tokens[j]!.val = -1` so the
quantifier ranges only over value-end positions (separators, which also reach depth-0 at `j+1`,
carry delta `0` and are excluded).  M9/M10 (`bracket_seq`/`bracket_map`) need no wrapper — they are
*exactly* the typed-locator outputs, so the assembly site invokes
`flowBracketBalance_matching_close_{seq,map}` directly. -/

/-- **`MapBodyProps.key_bracket_value` assembled (M5).**  After a `.key` at depth-0 `k`, a bracket
    opener at `k+1` (depth-0, kind `[` or `{`) in a well-bracketed, `WellTyped` map body `[lo, hi)`
    yields the full M5 conjunct: the 2-way kind split routes through the matching typed locator for
    the close position+type with balanced interior, plus the `.value` successor
    (`map_key_bracket_value_reduce` from the shared "what follows a complete key" fact `h_succ`). -/
theorem map_key_bracket_conjunct (tokens : Array (Positioned YamlToken))
    (lo hi k : Nat) (h_lo_k1 : lo ≤ k + 1) (h_k1_hi : k + 1 < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_k1_depth : flowBracketBalance tokens lo (k+1) = 0)
    (h_open : tokens[k+1]!.val = .flowSequenceStart ∨ tokens[k+1]!.val = .flowMappingStart)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo))
    (h_succ : ∀ j, k + 1 < j → j < hi → flowBracketDelta tokens[j]!.val = -1 →
      flowBracketBalance tokens lo (j+1) = 0 →
      j + 1 < hi ∧ tokens[j+1]!.val = .value) :
    ∃ j, k + 1 < j ∧ j < hi ∧
      ((tokens[k+1]!.val = .flowSequenceStart ∧ tokens[j]!.val = .flowSequenceEnd) ∨
       (tokens[k+1]!.val = .flowMappingStart ∧ tokens[j]!.val = .flowMappingEnd)) ∧
      flowBracketBalance tokens (k+2) j = 0 ∧
      j + 1 < hi ∧ tokens[j+1]!.val = .value := by
  rcases h_open with h_seq | h_map
  · obtain ⟨j, hkj, hjhi, hjval, hinner⟩ :=
      flowBracketBalance_matching_close_seq tokens lo (k+1) hi h_lo_k1 h_k1_hi h_hi_sz
        h_k1_depth h_seq h_total h_dyck h_wt
    have h_j_sz : j < tokens.size := Nat.lt_of_lt_of_le hjhi h_hi_sz
    have h_open_delta : flowBracketDelta tokens[k+1]!.val = 1 := by rw [h_seq]; rfl
    have h_close_delta : flowBracketDelta tokens[j]!.val = -1 := by rw [hjval]; rfl
    have hsucc := map_key_bracket_value_reduce tokens lo hi (k+1) j h_lo_k1 hkj h_j_sz
      h_k1_depth h_open_delta h_close_delta hinner (fun hd => h_succ j hkj hjhi h_close_delta hd)
    exact ⟨j, hkj, hjhi, Or.inl ⟨h_seq, hjval⟩, hinner, hsucc.1, hsucc.2⟩
  · obtain ⟨j, hkj, hjhi, hjval, hinner⟩ :=
      flowBracketBalance_matching_close_map tokens lo (k+1) hi h_lo_k1 h_k1_hi h_hi_sz
        h_k1_depth h_map h_total h_dyck h_wt
    have h_j_sz : j < tokens.size := Nat.lt_of_lt_of_le hjhi h_hi_sz
    have h_open_delta : flowBracketDelta tokens[k+1]!.val = 1 := by rw [h_map]; rfl
    have h_close_delta : flowBracketDelta tokens[j]!.val = -1 := by rw [hjval]; rfl
    have hsucc := map_key_bracket_value_reduce tokens lo hi (k+1) j h_lo_k1 hkj h_j_sz
      h_k1_depth h_open_delta h_close_delta hinner (fun hd => h_succ j hkj hjhi h_close_delta hd)
    exact ⟨j, hkj, hjhi, Or.inr ⟨h_map, hjval⟩, hinner, hsucc.1, hsucc.2⟩

/-- **`MapBodyProps.value_bracket_succ` assembled (M8).**  After a `.value` at depth-0 `k`, a
    bracket opener at `k+1` (depth-0, kind `[` or `{`) in a map body yields the M8 conjunct: the
    2-way kind split routes through the matching typed locator for the close position+type with
    balanced interior, plus the `FE ∨ (mapEnd ∧ j+1=hi)` successor (`map_value_bracket_succ_reduce`
    from `h_succ`).  A map body closes with `.flowMappingEnd`, so both kinds carry the map
    successor. -/
theorem map_value_bracket_conjunct (tokens : Array (Positioned YamlToken))
    (lo hi k : Nat) (h_lo_k1 : lo ≤ k + 1) (h_k1_hi : k + 1 < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_k1_depth : flowBracketBalance tokens lo (k+1) = 0)
    (h_open : tokens[k+1]!.val = .flowSequenceStart ∨ tokens[k+1]!.val = .flowMappingStart)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_wt : WellTyped ((tokens.toList.take hi).drop lo))
    (h_succ : ∀ j, k + 1 < j → j < hi → flowBracketDelta tokens[j]!.val = -1 →
      flowBracketBalance tokens lo (j+1) = 0 →
      j + 1 ≤ hi ∧
      (tokens[j+1]!.val = .flowEntry ∨
       (tokens[j+1]!.val = .flowMappingEnd ∧ j + 1 = hi))) :
    ∃ j, k + 1 < j ∧ j < hi ∧
      ((tokens[k+1]!.val = .flowSequenceStart ∧ tokens[j]!.val = .flowSequenceEnd) ∨
       (tokens[k+1]!.val = .flowMappingStart ∧ tokens[j]!.val = .flowMappingEnd)) ∧
      flowBracketBalance tokens (k+2) j = 0 ∧
      j + 1 ≤ hi ∧
      (tokens[j+1]!.val = .flowEntry ∨
       (tokens[j+1]!.val = .flowMappingEnd ∧ j + 1 = hi)) := by
  rcases h_open with h_seq | h_map
  · obtain ⟨j, hkj, hjhi, hjval, hinner⟩ :=
      flowBracketBalance_matching_close_seq tokens lo (k+1) hi h_lo_k1 h_k1_hi h_hi_sz
        h_k1_depth h_seq h_total h_dyck h_wt
    have h_j_sz : j < tokens.size := Nat.lt_of_lt_of_le hjhi h_hi_sz
    have h_open_delta : flowBracketDelta tokens[k+1]!.val = 1 := by rw [h_seq]; rfl
    have h_close_delta : flowBracketDelta tokens[j]!.val = -1 := by rw [hjval]; rfl
    have hsucc := map_value_bracket_succ_reduce tokens lo hi (k+1) j h_lo_k1 hkj h_j_sz
      h_k1_depth h_open_delta h_close_delta hinner (fun hd => h_succ j hkj hjhi h_close_delta hd)
    exact ⟨j, hkj, hjhi, Or.inl ⟨h_seq, hjval⟩, hinner, hsucc.1, hsucc.2⟩
  · obtain ⟨j, hkj, hjhi, hjval, hinner⟩ :=
      flowBracketBalance_matching_close_map tokens lo (k+1) hi h_lo_k1 h_k1_hi h_hi_sz
        h_k1_depth h_map h_total h_dyck h_wt
    have h_j_sz : j < tokens.size := Nat.lt_of_lt_of_le hjhi h_hi_sz
    have h_open_delta : flowBracketDelta tokens[k+1]!.val = 1 := by rw [h_map]; rfl
    have h_close_delta : flowBracketDelta tokens[j]!.val = -1 := by rw [hjval]; rfl
    have hsucc := map_value_bracket_succ_reduce tokens lo hi (k+1) j h_lo_k1 hkj h_j_sz
      h_k1_depth h_open_delta h_close_delta hinner (fun hd => h_succ j hkj hjhi h_close_delta hd)
    exact ⟨j, hkj, hjhi, Or.inr ⟨h_map, hjval⟩, hinner, hsucc.1, hsucc.2⟩


-- ═══ Filtered token lemmas for scanner handlers ═══

/-- `scanFlowSequenceStart` filtered token equation: adds exactly one `.flowSequenceStart`. -/
theorem scanFlowSequenceStart_filtered (s : ScannerState) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    (scanFlowSequenceStart s).tokens.filter p =
    (s.tokens.filter p).push { pos := s.currentPos, val := .flowSequenceStart } := by
  unfold scanFlowSequenceStart
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens]
  rw [emit_tokens_push]
  rw [Array.filter_push]; rfl

/-- `scanFlowMappingStart` filtered token equation: adds exactly one `.flowMappingStart`. -/
theorem scanFlowMappingStart_filtered (s : ScannerState) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    (scanFlowMappingStart s).tokens.filter p =
    (s.tokens.filter p).push { pos := s.currentPos, val := .flowMappingStart } := by
  unfold scanFlowMappingStart
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens]
  rw [emit_tokens_push]
  rw [Array.filter_push]; rfl

/-- `scanFlowEntry` filtered token equation (when it succeeds):
    adds exactly one `.flowEntry`. -/
theorem scanFlowEntry_filtered (s s' : ScannerState)
    (h : scanFlowEntry s = .ok s') :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    s'.tokens.filter p = (s.tokens.filter p).push { pos := s.currentPos, val := .flowEntry } := by
  unfold scanFlowEntry at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  -- Split on the validation check
  split at h
  · split at h
    · cases h
    · simp only [Except.ok.injEq] at h
      rw [← h]
      dsimp only []
      rw [ScannerCorrectness.advance_preserves_tokens]
      rw [emit_tokens_push]
      rw [Array.filter_push]; rfl
  · simp only [Except.ok.injEq] at h
    rw [← h]
    dsimp only []
    rw [ScannerCorrectness.advance_preserves_tokens]
    rw [emit_tokens_push]
    rw [Array.filter_push]; rfl

/-- `scanFlowSequenceEnd` filtered token equation: adds exactly one `.flowSequenceEnd`. -/
theorem scanFlowSequenceEnd_filtered (s : ScannerState) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    (scanFlowSequenceEnd s).tokens.filter p =
    (s.tokens.filter p).push { pos := s.currentPos, val := .flowSequenceEnd } := by
  unfold scanFlowSequenceEnd
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens]
  rw [emit_tokens_push]
  rw [Array.filter_push]; rfl

/-- `scanFlowMappingEnd` filtered token equation: adds exactly one `.flowMappingEnd`. -/
theorem scanFlowMappingEnd_filtered (s : ScannerState) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    (scanFlowMappingEnd s).tokens.filter p =
    (s.tokens.filter p).push { pos := s.currentPos, val := .flowMappingEnd } := by
  unfold scanFlowMappingEnd
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens]
  rw [emit_tokens_push]
  rw [Array.filter_push]; rfl

/-! ### §G.balance.bridge.dispatch — dispatch→handler filtered-LIST connection

    The `.leafdelta` lemmas (above) state the filtered-token effect of the
    low-level *handlers* (`scanFlowSequenceStart`, …).  `emit_scans_in_flow`'s
    `Grammable` recursion, however, calls `scanNextToken` (the *dispatch*), which
    is one hop above the handler.  These five lemmas bridge the gap: given the
    `scanNextToken s = .ok (some s')` fact already produced by the dispatch leaf
    theorems (`scanNextToken_flow_open_nested`, …), each re-derives the dispatch
    composition to pin `s'` to the handler applied to the post-`saveSimpleKey`
    state `s_ad`, then combines the handler `.leafdelta` lemma with
    `saveSimpleKey_filter_placeholder` (the two reserved placeholders filter away)
    to expose the full filtered-LIST delta `s'.tokens.filter p =
    (s.tokens.filter p).push tok`.  These are the per-leaf inputs the
    `EmitScansInFlowBlock` `Grammable` induction (`.blockwb.predicate`, next)
    consumes.  No consumers yet — pure enablement, mirroring `.leafdelta`. -/

/-- `[` dispatch: the new filtered token is exactly one `.flowSequenceStart`. -/
theorem scanNextToken_flow_open_seq_filtered_push (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'[' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    ∃ tok : Positioned YamlToken, tok.val = .flowSequenceStart ∧
      s'.tokens.filter (fun t => t.val != .placeholder)
        = (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '[')) :=
    scanNextToken_preprocess_flow s '[' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '[' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by simp only [s_ad]; split <;> exact h_sk_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '[' (h_ad_flow ▸ h_flow)
  have h_flow_disp := dispatchFlowIndicators_bracket s_ad
  have h_snt_eq : scanNextToken s = .ok (some (scanFlowSequenceStart s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = scanFlowSequenceStart s_ad :=
    Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
  have h_ad_filter : s_ad.tokens.filter (fun t => t.val != .placeholder)
      = s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]; split <;> exact saveSimpleKey_filter_placeholder s
  refine ⟨⟨s_ad.currentPos, .flowSequenceStart, s_ad.currentPos⟩, rfl, ?_⟩
  have hf := scanFlowSequenceStart_filtered s_ad
  rw [h_s', hf, h_ad_filter]

/-- `{` dispatch: the new filtered token is exactly one `.flowMappingStart`. -/
theorem scanNextToken_flow_open_map_filtered_push (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'{' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    ∃ tok : Positioned YamlToken, tok.val = .flowMappingStart ∧
      s'.tokens.filter (fun t => t.val != .placeholder)
        = (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '{')) :=
    scanNextToken_preprocess_flow s '{' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '{' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by simp only [s_ad]; split <;> exact h_sk_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '{' (h_ad_flow ▸ h_flow)
  have h_flow_disp := dispatchFlowIndicators_brace s_ad
  have h_snt_eq : scanNextToken s = .ok (some (scanFlowMappingStart s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = scanFlowMappingStart s_ad :=
    Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
  have h_ad_filter : s_ad.tokens.filter (fun t => t.val != .placeholder)
      = s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]; split <;> exact saveSimpleKey_filter_placeholder s
  refine ⟨⟨s_ad.currentPos, .flowMappingStart, s_ad.currentPos⟩, rfl, ?_⟩
  have hf := scanFlowMappingStart_filtered s_ad
  rw [h_s', hf, h_ad_filter]

/-- `]` dispatch (nested, `flowLevel ≥ 2`): the new filtered token is exactly
    one `.flowSequenceEnd`. -/
theorem scanNextToken_flow_close_seq_filtered_push (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨']' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_fl_ge2 : s.flowLevel ≥ 2)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    ∃ tok : Positioned YamlToken, tok.val = .flowSequenceEnd ∧
      s'.tokens.filter (fun t => t.val != .placeholder)
        = (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ']')) :=
    scanNextToken_preprocess_flow s ']' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ']' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_check := checkBlockFlowIndent_ok_close_bracket s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_fl_ge2 : s_ad.flowLevel ≥ 2 := by rw [h_ad_fl]; exact h_fl_ge2
  have h_flow_disp := dispatchFlowIndicators_close_bracket_nested s_ad h_ad_fl_ge2
  have h_snt_eq : scanNextToken s = .ok (some (scanFlowSequenceEnd s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = scanFlowSequenceEnd s_ad :=
    Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
  have h_ad_filter : s_ad.tokens.filter (fun t => t.val != .placeholder)
      = s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]; split <;> exact saveSimpleKey_filter_placeholder s
  refine ⟨⟨s_ad.currentPos, .flowSequenceEnd, s_ad.currentPos⟩, rfl, ?_⟩
  have hf := scanFlowSequenceEnd_filtered s_ad
  rw [h_s', hf, h_ad_filter]

/-- `}` dispatch (nested, `flowLevel ≥ 2`): the new filtered token is exactly
    one `.flowMappingEnd`. -/
theorem scanNextToken_flow_close_map_filtered_push (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'}' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_fl_ge2 : s.flowLevel ≥ 2)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    ∃ tok : Positioned YamlToken, tok.val = .flowMappingEnd ∧
      s'.tokens.filter (fun t => t.val != .placeholder)
        = (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '}')) :=
    scanNextToken_preprocess_flow s '}' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '}' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_check := checkBlockFlowIndent_ok_close_brace s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_fl_ge2 : s_ad.flowLevel ≥ 2 := by rw [h_ad_fl]; exact h_fl_ge2
  have h_flow_disp := dispatchFlowIndicators_close_brace_nested s_ad h_ad_fl_ge2
  have h_snt_eq : scanNextToken s = .ok (some (scanFlowMappingEnd s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = scanFlowMappingEnd s_ad :=
    Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
  have h_ad_filter : s_ad.tokens.filter (fun t => t.val != .placeholder)
      = s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]; split <;> exact saveSimpleKey_filter_placeholder s
  refine ⟨⟨s_ad.currentPos, .flowMappingEnd, s_ad.currentPos⟩, rfl, ?_⟩
  have hf := scanFlowMappingEnd_filtered s_ad
  rw [h_s', hf, h_ad_filter]

/-- `"` dispatch: the new filtered token is exactly one `.scalar _ .doubleQuoted`. -/
theorem scanNextToken_flow_scalar_filtered_push (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'"' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    ∃ (tok : Positioned YamlToken) (str : String) (st : ScalarStyle),
      tok.val = .scalar str st ∧
      s'.tokens.filter (fun t => t.val != .placeholder)
        = (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '"')) :=
    scanNextToken_preprocess_flow s '"' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '"' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by simp only [s_ad]; split <;> exact h_sk_flow
  have h_ad_flow_true : s_ad.inFlow = true := h_ad_flow ▸ h_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '"' h_ad_flow_true
  have h_flow_none : scanNextToken_dispatchFlowIndicators s_ad '"' = .ok none :=
    dispatchFlowIndicators_none _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have h_block_none : scanNextToken_dispatchBlockIndicators s_ad '"' = .ok none :=
    dispatchBlockIndicators_none_quote _
  have h_dc : scanNextToken_dispatchContent s_ad '"' = Except.ok s' := by
    cases h_dc_eq : scanNextToken_dispatchContent s_ad '"' with
    | error e =>
      exfalso
      have h_snt_err := scanNextToken_via_content_dispatch_error
        _ _ _ _ _ h_pp h_struct rfl h_check h_flow_none h_block_none h_dc_eq
      rw [h_snt_err] at h_snt; exact absurd h_snt (by simp)
    | ok s_dc =>
      have h_snt_eq : scanNextToken s = Except.ok (some s_dc) :=
        scanNextToken_via_content_dispatch _ _ _ _ _ h_pp h_struct rfl h_check
          h_flow_none h_block_none h_dc_eq
      have h_eq2 : s' = s_dc := Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
      subst h_eq2; rfl
  have h_tokens_push : ∃ c, s'.tokens
      = s_ad.tokens.push ⟨s_ad.currentPos, .scalar c .doubleQuoted, s_ad.currentPos⟩ := by
    cases h_dq_eq : scanDoubleQuoted s_ad with
    | error e =>
      exfalso
      have h_dc_err : scanNextToken_dispatchContent s_ad '"' = Except.error e := by
        unfold scanNextToken_dispatchContent
        simp [bind, Except.bind, pure, Except.pure, h_dq_eq]
      rw [h_dc_err] at h_dc; exact absurd h_dc (by simp)
    | ok s_dq =>
      obtain ⟨c, h_tok⟩ := scanDoubleQuoted_tokens_push h_dq_eq
      refine ⟨c, ?_⟩
      have h_s'_tokens : s'.tokens = s_dq.tokens := by
        unfold scanNextToken_dispatchContent at h_dc
        simp [bind, Except.bind, pure, Except.pure, h_dq_eq] at h_dc
        split at h_dc
        · rw [← h_dc]
        · rw [← h_dc]
      rw [h_s'_tokens, h_tok]
  obtain ⟨c, h_s'_tokens⟩ := h_tokens_push
  have h_ad_filter : s_ad.tokens.filter (fun t => t.val != .placeholder)
      = s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]; split <;> exact saveSimpleKey_filter_placeholder s
  refine ⟨⟨s_ad.currentPos, .scalar c .doubleQuoted, s_ad.currentPos⟩, c, .doubleQuoted, rfl, ?_⟩
  rw [h_s'_tokens, Array.filter_push]
  simp only [show ((⟨s_ad.currentPos, .scalar c .doubleQuoted, s_ad.currentPos⟩ : Positioned YamlToken).val
                   != YamlToken.placeholder) = true from rfl, ite_true]
  rw [h_ad_filter]

/-- `,` dispatch (flow separator): the new filtered token is exactly one `.flowEntry`.
    Companion to the five `.blockwb.dispatch` push lemmas above — the separator
    leaf the *body* of `EmitListScansInFlowBlock` / `EmitPairListScansInFlowBlock`
    threads between item blocks.  Requires the `lastRealToken ≠ flow*` premise that
    `scanFlowEntry` needs (every preceding `emit v` block supplies it). -/
theorem scanNextToken_flow_comma_filtered_push (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨',' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_last : ∀ t, lastRealTokenVal? s.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    ∃ tok : Positioned YamlToken, tok.val = .flowEntry ∧
      s'.tokens.filter (fun t => t.val != .placeholder)
        = (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ',')) :=
    scanNextToken_preprocess_flow s ',' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ',' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_check := checkBlockFlowIndent_ok_comma s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_fl_pos : s_ad.flowLevel > 0 := by
    rw [h_ad_fl]; unfold ScannerState.inFlow at h_flow; exact of_decide_eq_true h_flow
  have h_ad_last : ∀ t, lastRealTokenVal? s_ad.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry := by
    intro t ht
    have h_ad_toks : s_ad.tokens = (saveSimpleKey s).tokens := by
      simp only [s_ad]; split <;> rfl
    rw [h_ad_toks] at ht
    exact saveSimpleKey_preserves_lastRealTokenVal_ne_flow s h_last t ht
  have h_flow_disp := dispatchFlowIndicators_comma s_ad h_fl_pos h_ad_last
  have h_snt_eq : scanNextToken s =
      .ok (some { (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = { (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true } :=
    Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
  have h_ad_filter : s_ad.tokens.filter (fun t => t.val != .placeholder)
      = s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]; split <;> exact saveSimpleKey_filter_placeholder s
  have h_sfe : scanFlowEntry s_ad = .ok s' := by rw [h_s']; exact scanFlowEntry_ok s_ad h_ad_last
  refine ⟨⟨s_ad.currentPos, .flowEntry, s_ad.currentPos⟩, rfl, ?_⟩
  have hf := scanFlowEntry_filtered s_ad s' h_sfe
  rw [hf, h_ad_filter]

/-- **Comma simple-key add-on** (companion to `scanNextToken_flow_comma`): the flow
    `,` separator leaves `simpleKeyAllowed = true` (literally set by `scanFlowEntry`)
    and threads the simple key through unchanged from `saveSimpleKey s`.  Combined with
    `saveSimpleKey_id_of_flow_ska_false_ek_none` (when the pre-comma `simpleKeyAllowed`
    is `false`, as it is right after a value scan), the caller recovers
    `s'.simpleKey = s.simpleKey` — hence `simpleKey.possible` preservation.  The
    mapping-body producer needs both to re-establish the per-pair preconditions
    (`simpleKeyAllowed = true`, `simpleKey.possible = false`) before the recursive
    `EmitPairListScansInFlowBlock` call. -/
theorem scanNextToken_flow_comma_simpleKey (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨',' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_last : ∀ t, lastRealTokenVal? s.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    s'.simpleKeyAllowed = true ∧ s'.simpleKey = (saveSimpleKey s).simpleKey := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ',')) :=
    scanNextToken_preprocess_flow s ',' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ',' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_check := checkBlockFlowIndent_ok_comma s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_fl_pos : s_ad.flowLevel > 0 := by
    rw [h_ad_fl]; unfold ScannerState.inFlow at h_flow; exact of_decide_eq_true h_flow
  have h_ad_last : ∀ t, lastRealTokenVal? s_ad.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry := by
    intro t ht
    have h_ad_toks : s_ad.tokens = (saveSimpleKey s).tokens := by
      simp only [s_ad]; split <;> rfl
    rw [h_ad_toks] at ht
    exact saveSimpleKey_preserves_lastRealTokenVal_ne_flow s h_last t ht
  have h_flow_disp := dispatchFlowIndicators_comma s_ad h_fl_pos h_ad_last
  have h_snt_eq : scanNextToken s =
      .ok (some { (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = { (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true } :=
    Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
  rw [h_s']
  refine ⟨rfl, ?_⟩
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_simpleKey, ScannerCorrectness.emit_preserves_simpleKey]
  simp only [s_ad]; split <;> rfl

/-- `ScanChain_deterministic`: two chains with the same start state and step count
    reach the same final state (since `scanNextToken` is a function). -/
theorem ScanChain_deterministic {s s₁ s₂ : ScannerState} {n : Nat}
    (h₁ : ScanChain s n s₁) (h₂ : ScanChain s n s₂) : s₁ = s₂ := by
  induction h₁ generalizing s₂ with
  | zero => cases h₂; rfl
  | @step s s_mid₁ s₁ k h_snt₁ _ ih =>
    match h₂ with
    | .step h_snt₂ h_rest₂ =>
      have : s_mid₁ = _ := Option.some.inj (Except.ok.inj (h_snt₁.symm.trans h_snt₂))
      subst this
      exact ih h_rest₂

/-- `ScanChain.split`: decompose a chain into two consecutive sub-chains. -/
theorem ScanChain.split {s s₁ s₂ : ScannerState} {n₁ n₂ : Nat}
    (h₁ : ScanChain s n₁ s₁) (h_total : ScanChain s (n₁ + n₂) s₂) :
    ScanChain s₁ n₂ s₂ := by
  induction h₁ generalizing s₂ with
  | zero => simpa using h_total
  | @step s s_mid s₁ k h_snt₁ _ ih =>
    have h_rw : k + 1 + n₂ = (k + n₂) + 1 := by omega
    rw [h_rw] at h_total
    match h_total with
    | .step h_snt₂ h_rest₂ =>
      have : s_mid = _ := Option.some.inj (Except.ok.inj (h_snt₁.symm.trans h_snt₂))
      subst this
      exact ih h_rest₂


end L4YAML.Proofs.EmitterScannability
