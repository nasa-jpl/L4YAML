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
