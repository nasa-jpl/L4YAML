/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.EmitterScannability.NonemptyStructure

/-!
# The deep-family positional navigator (Phase J — the R447 residual's substrate)

The R447 residual `seqBody_recseqbody_provider` owes, for every close-gated body window of the
scanned emission, the window's `RecSeqBody` — PATH-FREE (map-nested seq windows included).  The
severance-free DEEP family (`RecSeqBodyDeep`/`RecEntryDeep`/`RecMapPairDeep`/`RecMapBodyDeep`,
`NonemptyStructure.lean`) was built precisely so a navigator can `cases` its way down without the
flat `.map`/`.mapRec` token-indistinguishability; its emission producers
(`emitList_scans_recseqbodyDeep` / `emitPairList_scans_recmapbodyDeep`) are landed.  What was never
built is the NAVIGATOR itself: the positional descent from the stored root body to an arbitrary
gated window.

This module supplies it in three layers:

1. **Positional decomposition mirrors** — the deep-family analogs of the landed flat positional
   bridges (`recseqbody_window_of_located_entry`, `recmappair_window_descent`): re-express a deep
   body/entry/pair stored on the SLICE `(tokens.toList.take hi0).drop lo0` as positional facts
   (entry spans, separator positions, interior windows) plus stored deep sub-terms on sub-slices.

2. **Bracket-floor utilities** — the window-vs-structure interaction lemmas: a gated window that
   starts at a body's entry boundary ends at the body's end; a gated window that starts strictly
   inside a bracket entry stays inside that entry's interior.

3. **The joint navigator** — one strong induction on the body span delivering, at every gated
   sub-window, the close-keyed joint `(] → RecSeqBody) ∧ (} → RecMapBody)` — the deliverable both
   `seqBody_recseqbody_provider` (seq half) and the future `h_map_rec` producer (map half) project.
-/

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

/-! ## §1 Slice algebra: shared take/drop re-expression moves

The deep body/pair constructors index CONCATENATIONS (`e ++ fe :: rest`); the navigator holds the
whole body as a SLICE `(tokens.toList.take hi0).drop lo0`.  These lemmas convert between the two:
given the concatenation shape of the slice, they name the split position and re-slice each part.
They are collection-agnostic (pure list algebra), shared by both axes. -/

/-- A concatenation decomposition of a slice re-slices its FRONT part: if
    `(take hi0).drop lo0 = e ++ suffix` then `e = (take (lo0 + e.length)).drop lo0`. -/
lemma slice_front_of_append (tokens : Array (Positioned YamlToken)) (lo0 hi0 : Nat)
    (e suffix : List (Positioned YamlToken))
    (h_lo0_hi0 : lo0 ≤ hi0) (h_hi0 : hi0 ≤ tokens.size)
    (h_shape : (tokens.toList.take hi0).drop lo0 = e ++ suffix) :
    e = (tokens.toList.take (lo0 + e.length)).drop lo0 := by
  have h_tl_len : tokens.toList.length = tokens.size := Array.length_toList
  -- length bookkeeping: the slice length is `hi0 - lo0`, so `lo0 + |e| ≤ hi0`.
  have h_slice_len : ((tokens.toList.take hi0).drop lo0).length = hi0 - lo0 := by
    rw [List.length_drop, List.length_take, h_tl_len, Nat.min_eq_left h_hi0]
  have h_len_le : lo0 + e.length ≤ hi0 := by
    have hc := congrArg List.length h_shape
    rw [h_slice_len, List.length_append] at hc
    omega
  -- `(take (lo0+|e|)).drop lo0 = ((take hi0).drop lo0).take |e|` and the latter is `e`.
  have e1 : (tokens.toList.take (lo0 + e.length)).drop lo0
      = (tokens.toList.drop lo0).take e.length := by
    rw [List.drop_take]; congr 1; omega
  have e2 : ((tokens.toList.take hi0).drop lo0).take e.length
      = (tokens.toList.drop lo0).take e.length := by
    rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega : e.length ≤ hi0 - lo0)]
  have e3 : ((tokens.toList.take hi0).drop lo0).take e.length = e := by
    rw [h_shape, List.take_left]
  rw [e1, ← e2, e3]

/-- A concatenation decomposition of a slice re-slices its BACK part past a single separator:
    if `(take hi0).drop lo0 = e ++ fe :: rest` with `m := lo0 + e.length`, then `tokens[m]! = fe`
    and `rest = (take hi0).drop (m+1)`. -/
lemma slice_sep_rest_of_append (tokens : Array (Positioned YamlToken)) (lo0 hi0 : Nat)
    (e : List (Positioned YamlToken)) (fe : Positioned YamlToken)
    (rest : List (Positioned YamlToken))
    (h_hi0 : hi0 ≤ tokens.size)
    (h_shape : (tokens.toList.take hi0).drop lo0 = e ++ fe :: rest) :
    tokens[lo0 + e.length]! = fe
    ∧ rest = (tokens.toList.take hi0).drop (lo0 + e.length + 1)
    ∧ lo0 + e.length < hi0 := by
  have h_tl_len : tokens.toList.length = tokens.size := Array.length_toList
  have h_slice_len : ((tokens.toList.take hi0).drop lo0).length = hi0 - lo0 := by
    rw [List.length_drop, List.length_take, h_tl_len, Nat.min_eq_left h_hi0]
  have h_len : hi0 - lo0 = e.length + (1 + rest.length) := by
    have hc := congrArg List.length h_shape
    rw [h_slice_len] at hc
    simp only [List.length_append, List.length_cons] at hc
    omega
  have h_m_hi0 : lo0 + e.length < hi0 := by omega
  -- Drop `e` off the decomposition: `(take hi0).drop m = fe :: rest` where `m = lo0 + e.length`.
  have h_drop_m : (tokens.toList.take hi0).drop (lo0 + e.length) = fe :: rest := by
    have h1 : (tokens.toList.take hi0).drop (lo0 + e.length)
        = ((tokens.toList.take hi0).drop lo0).drop e.length := by
      rw [List.drop_drop] <;> first | rfl | (congr 1; omega)
    rw [h1, h_shape, List.drop_left]
  -- Peel the head: `tokens[m]! = fe`.
  have h_m_sz : lo0 + e.length < tokens.size := by omega
  have h_m_len_take : lo0 + e.length < (tokens.toList.take hi0).length := by
    rw [List.length_take, h_tl_len, Nat.min_eq_left h_hi0]; omega
  have h_peel : (tokens.toList.take hi0).drop (lo0 + e.length)
      = (tokens.toList.take hi0)[lo0 + e.length]'h_m_len_take
        :: (tokens.toList.take hi0).drop (lo0 + e.length + 1) := by
    exact (List.getElem_cons_drop h_m_len_take).symm
  rw [h_peel] at h_drop_m
  obtain ⟨h_head_eq, h_tail_eq⟩ := List.cons.inj h_drop_m
  refine ⟨?_, h_tail_eq.symm, h_m_hi0⟩
  have h_get : (tokens.toList.take hi0)[lo0 + e.length]'h_m_len_take
      = tokens.toList[lo0 + e.length]'(by rw [h_tl_len]; omega) := by
    exact List.getElem_take
  rw [getElem!_pos tokens (lo0 + e.length) h_m_sz, ← Array.getElem_toList, ← h_get, h_head_eq]

/-- Head peel of a non-empty slice: `(take hi0).drop lo0 = tokens.toList[lo0] :: (take hi0).drop (lo0+1)`. -/
lemma slice_cons_head (tokens : Array (Positioned YamlToken)) (lo0 hi0 : Nat)
    (h_lo : lo0 < hi0) (h_hi : hi0 ≤ tokens.size) :
    (tokens.toList.take hi0).drop lo0
      = tokens.toList[lo0]'(by rw [Array.length_toList]; omega)
        :: (tokens.toList.take hi0).drop (lo0 + 1) := by
  have hlen : lo0 < (tokens.toList.take hi0).length := by
    rw [List.length_take, Array.length_toList, Nat.min_eq_left h_hi]; omega
  have h := (List.getElem_cons_drop hlen).symm
  rw [List.getElem_take] at h
  exact h

/-- The `getElem!`/`toList` bridge for in-bounds positions. -/
lemma tok_bang_eq_toList (tokens : Array (Positioned YamlToken)) (i : Nat)
    (h : i < tokens.size) :
    tokens[i]! = tokens.toList[i]'(by rw [Array.length_toList]; exact h) := by
  rw [getElem!_pos tokens i h, Array.getElem_toList]

/-! ## §2 Deep positional decomposition mirrors

The deep-family analogs of the landed flat positional bridges: re-express a deep body / entry /
pair stored on a slice as positional facts plus stored deep sub-terms on sub-slices.  All are
`cases` on the (severance-free) deep constructors + the §1 slice algebra. -/

/-- **Deep seq-body positional split.**  A `RecSeqBodyDeep` on the slice `[lo0, hi0)` is either a
    single entry spanning the whole window, or a first entry `[lo0, m)`, a depth-`0` `.flowEntry`
    separator at `m`, and a deep tail body on `[m+1, hi0)`. -/
lemma recseqbodydeep_window_split (tokens : Array (Positioned YamlToken)) (lo0 hi0 : Nat)
    (h_lo0_hi0 : lo0 ≤ hi0) (h_hi0 : hi0 ≤ tokens.size)
    (h_body : RecSeqBodyDeep ((tokens.toList.take hi0).drop lo0)) :
    (RecEntryDeep ((tokens.toList.take hi0).drop lo0))
    ∨ (∃ m, lo0 < m ∧ m < hi0 ∧ tokens[m]!.val = .flowEntry
        ∧ RecEntryDeep ((tokens.toList.take m).drop lo0)
        ∧ RecSeqBodyDeep ((tokens.toList.take hi0).drop (m + 1))) := by
  generalize h_shape : (tokens.toList.take hi0).drop lo0 = l at h_body
  cases h_body with
  | single e h_ne h_e h_head => exact Or.inl (h_shape ▸ h_e)
  | cons e fe rest h_ne h_e h_head h_fe h_rest =>
    -- `h_shape : (take hi0).drop lo0 = e ++ fe :: rest`; name the split.
    obtain ⟨h_fe_pos, h_rest_slice, h_m_hi0⟩ :=
      slice_sep_rest_of_append tokens lo0 hi0 e fe rest h_hi0 h_shape
    have h_e_slice := slice_front_of_append tokens lo0 hi0 e (fe :: rest) h_lo0_hi0 h_hi0
      h_shape
    have h_e_pos : 0 < e.length := List.length_pos_iff.mpr h_ne
    refine Or.inr ⟨lo0 + e.length, by omega, h_m_hi0, ?_, ?_, ?_⟩
    · rw [h_fe_pos]; exact h_fe
    · rw [← h_e_slice]; exact h_e
    · rw [← h_rest_slice]; exact h_rest

/-- **Deep map-body positional split** — the pair mirror of `recseqbodydeep_window_split`. -/
lemma recmapbodydeep_window_split (tokens : Array (Positioned YamlToken)) (lo0 hi0 : Nat)
    (h_lo0_hi0 : lo0 ≤ hi0) (h_hi0 : hi0 ≤ tokens.size)
    (h_body : RecMapBodyDeep ((tokens.toList.take hi0).drop lo0)) :
    (RecMapPairDeep ((tokens.toList.take hi0).drop lo0))
    ∨ (∃ m, lo0 < m ∧ m < hi0 ∧ tokens[m]!.val = .flowEntry
        ∧ RecMapPairDeep ((tokens.toList.take m).drop lo0)
        ∧ RecMapBodyDeep ((tokens.toList.take hi0).drop (m + 1))) := by
  generalize h_shape : (tokens.toList.take hi0).drop lo0 = l at h_body
  cases h_body with
  | single p h_ne h_p h_head => exact Or.inl (h_shape ▸ h_p)
  | cons p fe rest h_ne h_p h_head h_fe h_rest =>
    obtain ⟨h_fe_pos, h_rest_slice, h_m_hi0⟩ :=
      slice_sep_rest_of_append tokens lo0 hi0 p fe rest h_hi0 h_shape
    have h_p_slice := slice_front_of_append tokens lo0 hi0 p (fe :: rest) h_lo0_hi0 h_hi0
      h_shape
    have h_p_pos : 0 < p.length := List.length_pos_iff.mpr h_ne
    refine Or.inr ⟨lo0 + p.length, by omega, h_m_hi0, ?_, ?_, ?_⟩
    · rw [h_fe_pos]; exact h_fe
    · rw [← h_p_slice]; exact h_p
    · rw [← h_rest_slice]; exact h_rest

/-- **Deep entry positional shape dispatch.**  A `RecEntryDeep` on the slice `[lo0, m)` is one of
    the five shapes, each positionalized: a single scalar token; an empty `[ ]` / `{ }`; or a
    bracketed collection whose opener/closer sit at `lo0` / `m-1` and whose interior `[lo0+1, m-1)`
    carries the stored deep body.  This is the severance-free dispatch the flat family cannot
    provide (`.map` vs `.mapRec` are token-indistinguishable there). -/
lemma recentrydeep_window_cases (tokens : Array (Positioned YamlToken)) (lo0 m : Nat)
    (h_lo0_m : lo0 ≤ m) (h_m : m ≤ tokens.size)
    (h_e : RecEntryDeep ((tokens.toList.take m).drop lo0)) :
    (m = lo0 + 1 ∧ ∃ c s, tokens[lo0]!.val = .scalar c s)
    ∨ (m = lo0 + 2 ∧ tokens[lo0]!.val = .flowSequenceStart
        ∧ tokens[lo0 + 1]!.val = .flowSequenceEnd)
    ∨ (m = lo0 + 2 ∧ tokens[lo0]!.val = .flowMappingStart
        ∧ tokens[lo0 + 1]!.val = .flowMappingEnd)
    ∨ (lo0 + 2 < m ∧ tokens[lo0]!.val = .flowSequenceStart
        ∧ tokens[m - 1]!.val = .flowSequenceEnd
        ∧ RecSeqBodyDeep ((tokens.toList.take (m - 1)).drop (lo0 + 1)))
    ∨ (lo0 + 2 < m ∧ tokens[lo0]!.val = .flowMappingStart
        ∧ tokens[m - 1]!.val = .flowMappingEnd
        ∧ RecMapBodyDeep ((tokens.toList.take (m - 1)).drop (lo0 + 1))) := by
  -- Slice length: `|slice| = m - lo0`.
  have h_tl_len : tokens.toList.length = tokens.size := Array.length_toList
  have h_slice_len : ((tokens.toList.take m).drop lo0).length = m - lo0 := by
    rw [List.length_drop, List.length_take, h_tl_len, Nat.min_eq_left h_m]
  generalize h_shape : (tokens.toList.take m).drop lo0 = l at h_e
  cases h_e with
  | scalar t c s ht =>
    -- `slice = [t]`: length pins `m = lo0 + 1`; head peel pins `tokens[lo0] = t`.
    have h_len : m - lo0 = 1 := by
      have hc := congrArg List.length h_shape
      rw [h_slice_len] at hc; simpa using hc
    have h_m_eq : m = lo0 + 1 := by omega
    have h_lo0_sz : lo0 < tokens.size := by omega
    have h_peel := slice_cons_head tokens lo0 m (by omega) h_m
    rw [h_peel] at h_shape
    have h_t := (List.cons.inj h_shape.symm).1
    refine Or.inl ⟨h_m_eq, c, s, ?_⟩
    rw [tok_bang_eq_toList tokens lo0 h_lo0_sz, ← h_t]
    exact ht
  | seqEmpty op cl h_op h_cl =>
    have h_len : m - lo0 = 2 := by
      have hc := congrArg List.length h_shape
      rw [h_slice_len] at hc; simpa using hc
    have h_m_eq : m = lo0 + 2 := by omega
    have h_lo0_sz : lo0 < tokens.size := by omega
    have h_lo1_sz : lo0 + 1 < tokens.size := by omega
    have h_peel := slice_cons_head tokens lo0 m (by omega) h_m
    rw [h_peel] at h_shape
    have h_op_eq := (List.cons.inj h_shape.symm).1
    have h_tail := (List.cons.inj h_shape.symm).2
    have h_peel1 := slice_cons_head tokens (lo0 + 1) m (by omega) h_m
    rw [h_peel1] at h_tail
    have h_cl_eq := (List.cons.inj h_tail).1
    refine Or.inr (Or.inl ⟨h_m_eq, ?_, ?_⟩)
    · rw [tok_bang_eq_toList tokens lo0 h_lo0_sz, ← h_op_eq]; exact h_op
    · rw [tok_bang_eq_toList tokens (lo0 + 1) h_lo1_sz, ← h_cl_eq]; exact h_cl
  | mapEmpty op cl h_op h_cl =>
    have h_len : m - lo0 = 2 := by
      have hc := congrArg List.length h_shape
      rw [h_slice_len] at hc; simpa using hc
    have h_m_eq : m = lo0 + 2 := by omega
    have h_lo0_sz : lo0 < tokens.size := by omega
    have h_lo1_sz : lo0 + 1 < tokens.size := by omega
    have h_peel := slice_cons_head tokens lo0 m (by omega) h_m
    rw [h_peel] at h_shape
    have h_op_eq := (List.cons.inj h_shape.symm).1
    have h_tail := (List.cons.inj h_shape.symm).2
    have h_peel1 := slice_cons_head tokens (lo0 + 1) m (by omega) h_m
    rw [h_peel1] at h_tail
    have h_cl_eq := (List.cons.inj h_tail).1
    refine Or.inr (Or.inr (Or.inl ⟨h_m_eq, ?_, ?_⟩))
    · rw [tok_bang_eq_toList tokens lo0 h_lo0_sz, ← h_op_eq]; exact h_op
    · rw [tok_bang_eq_toList tokens (lo0 + 1) h_lo1_sz, ← h_cl_eq]; exact h_cl
  | seq op cl interior h_op h_cl h_rec =>
    -- `slice = op :: (interior ++ [cl])`, interior a (non-empty) deep body.
    have h_int_ne : interior ≠ [] := by
      cases h_rec with
      | single e h_ne _ _ => exact h_ne
      | cons e fe rest h_ne _ _ _ _ =>
        intro h
        exact absurd (List.append_eq_nil_iff.mp h).2 (by simp)
    have h_int_pos : 0 < interior.length := List.length_pos_iff.mpr h_int_ne
    have h_len : m - lo0 = interior.length + 2 := by
      have hc := congrArg List.length h_shape
      rw [h_slice_len] at hc
      simp only [List.length_cons, List.length_append] at hc
      omega
    have h_m_gt : lo0 + 2 < m := by omega
    have h_lo0_sz : lo0 < tokens.size := by omega
    have h_peel := slice_cons_head tokens lo0 m (by omega) h_m
    rw [h_peel] at h_shape
    have h_op_eq := (List.cons.inj h_shape.symm).1
    have h_tail : (tokens.toList.take m).drop (lo0 + 1) = interior ++ cl :: [] := by
      have := (List.cons.inj h_shape.symm).2
      simpa using this.symm
    obtain ⟨h_cl_pos, _, _⟩ :=
      slice_sep_rest_of_append tokens (lo0 + 1) m interior cl [] h_m h_tail
    have h_int_slice := slice_front_of_append tokens (lo0 + 1) m interior (cl :: [])
      (by omega) h_m h_tail
    have h_kv : lo0 + 1 + interior.length = m - 1 := by omega
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨h_m_gt, ?_, ?_, ?_⟩)))
    · rw [tok_bang_eq_toList tokens lo0 h_lo0_sz, ← h_op_eq]; exact h_op
    · rw [← h_kv, h_cl_pos]; exact h_cl
    · rw [← h_kv, ← h_int_slice]; exact h_rec
  | mapRec op cl interior h_op h_cl h_rec =>
    have h_int_ne : interior ≠ [] := by
      cases h_rec with
      | single p h_ne _ _ => exact h_ne
      | cons p fe rest h_ne _ _ _ _ =>
        intro h
        exact absurd (List.append_eq_nil_iff.mp h).2 (by simp)
    have h_int_pos : 0 < interior.length := List.length_pos_iff.mpr h_int_ne
    have h_len : m - lo0 = interior.length + 2 := by
      have hc := congrArg List.length h_shape
      rw [h_slice_len] at hc
      simp only [List.length_cons, List.length_append] at hc
      omega
    have h_m_gt : lo0 + 2 < m := by omega
    have h_lo0_sz : lo0 < tokens.size := by omega
    have h_peel := slice_cons_head tokens lo0 m (by omega) h_m
    rw [h_peel] at h_shape
    have h_op_eq := (List.cons.inj h_shape.symm).1
    have h_tail : (tokens.toList.take m).drop (lo0 + 1) = interior ++ cl :: [] := by
      have := (List.cons.inj h_shape.symm).2
      simpa using this.symm
    obtain ⟨h_cl_pos, _, _⟩ :=
      slice_sep_rest_of_append tokens (lo0 + 1) m interior cl [] h_m h_tail
    have h_int_slice := slice_front_of_append tokens (lo0 + 1) m interior (cl :: [])
      (by omega) h_m h_tail
    have h_kv : lo0 + 1 + interior.length = m - 1 := by omega
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨h_m_gt, ?_, ?_, ?_⟩)))
    · rw [tok_bang_eq_toList tokens lo0 h_lo0_sz, ← h_op_eq]; exact h_op
    · rw [← h_kv, h_cl_pos]; exact h_cl
    · rw [← h_kv, ← h_int_slice]; exact h_rec

/-- **Deep map-pair positional descent** — the deep mirror of the landed flat
    `recmappair_window_descent`: recover the pair's value-separator position `kv` and both
    key/value sub-blocks as `RecEntryDeep`s on their slices. -/
lemma recmappairdeep_window_descent (tokens : Array (Positioned YamlToken)) (lo m : Nat)
    (h_lo_m : lo < m) (h_m_sz : m ≤ tokens.size)
    (h_pair : RecMapPairDeep ((tokens.toList.take m).drop lo)) :
    ∃ kv, lo < kv ∧ kv < m ∧
      tokens[lo]!.val = .key ∧
      tokens[kv]!.val = .value ∧
      RecEntryDeep ((tokens.toList.take kv).drop (lo + 1)) ∧
      RecEntryDeep ((tokens.toList.take m).drop (kv + 1)) := by
  generalize h_shape : (tokens.toList.take m).drop lo = l at h_pair
  cases h_pair with
  | mk kt block_k vt block_v h_kt h_ke h_vt h_ve =>
    have h_lo_sz : lo < tokens.size := by omega
    -- head peel: `tokens[lo] = kt`.
    have h_peel := slice_cons_head tokens lo m h_lo_m h_m_sz
    rw [h_peel] at h_shape
    have h_kt_eq := (List.cons.inj h_shape.symm).1
    have h_tail : (tokens.toList.take m).drop (lo + 1) = block_k ++ vt :: block_v :=
      ((List.cons.inj h_shape.symm).2).symm
    -- `kv := lo + 1 + |block_k|`: the separator peel names it and re-slices `block_v`.
    obtain ⟨h_vt_pos, h_bv_slice, h_kv_m⟩ :=
      slice_sep_rest_of_append tokens (lo + 1) m block_k vt block_v h_m_sz h_tail
    have h_bk_slice := slice_front_of_append tokens (lo + 1) m block_k (vt :: block_v)
      (by omega) h_m_sz h_tail
    refine ⟨lo + 1 + block_k.length, by omega, h_kv_m, ?_, ?_, ?_, ?_⟩
    · rw [tok_bang_eq_toList tokens lo h_lo_sz, ← h_kt_eq]; exact h_kt
    · rw [h_vt_pos]; exact h_vt
    · rw [← h_bk_slice]; exact h_ke
    · rw [← h_bv_slice]; exact h_ve

/-! ## §3a Window-vs-structure floor utilities

The four bracket-arithmetic moves the navigator's case analysis runs on: positionalized
`WellBracketed` floors; the closer-head dip; the depth-`0` closer forcing the window to the body
end; and the interior escape bound. -/

/-- Positional floors of a `WellBracketed` slice: total balance `0` and every prefix `≥ 0`. -/
lemma wellBracketed_slice_positional (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h_ab : a ≤ b) (_h_b : b ≤ tokens.size)
    (h_wb : WellBracketed ((tokens.toList.take b).drop a)) :
    flowBracketBalance tokens a b = 0
    ∧ (∀ i, a ≤ i → i ≤ b → flowBracketBalance tokens a i ≥ 0) := by
  have h_tl_len : tokens.toList.length = tokens.size := Array.length_toList
  -- re-express the slice in the `drop`-then-`take` form the bridge uses
  have h_slice : (tokens.toList.take b).drop a = (tokens.toList.drop a).take (b - a) := by
    rw [List.drop_take]
  rw [h_slice] at h_wb
  obtain ⟨h_total, h_floor⟩ := h_wb
  constructor
  · rw [flowBracketBalance_eq_pbalance tokens a b h_ab]; exact h_total
  · intro i hi1 hi2
    have h_take : ((tokens.toList.drop a).take (b - a)).take (i - a)
        = (tokens.toList.drop a).take (i - a) := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    have := h_floor (i - a)
    rw [h_take, ← flowBracketBalance_eq_pbalance tokens a i hi1] at this
    exact this

/-- A gated window never starts at a closer: the first step dips the window balance to `-1`,
    violating the window's own Dyck floor. -/
lemma window_no_closer_head (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_lo_hi : lo < hi) (h_lo_sz : lo < tokens.size)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_closer : flowBracketDelta tokens[lo]!.val = -1) : False := by
  have h_lo_len : lo < tokens.toList.length := by rw [Array.length_toList]; omega
  have h_single : flowBracketBalance tokens lo (lo + 1) = -1 := by
    rw [flowBracketBalance_single tokens lo h_lo_len,
      ← tok_bang_eq_toList tokens lo (by rw [← Array.length_toList]; exact h_lo_len)]
    exact h_closer
  have := h_dyck (lo + 1) (by omega) (by omega)
  omega

/-- **Depth-`0` closer forcing**: a balanced closer-ended window starting at a depth-`0` position
    of a floored body span ends exactly at the span end.  (At `lo = lo0` this is the whole-window
    forcing; at map-pair block heads it drives the closer-type mismatch refutations.) -/
lemma window_depth0_closer_ends_at_end (tokens : Array (Positioned YamlToken))
    (lo0 hi0 lo hi : Nat)
    (h_hi0_sz : hi0 ≤ tokens.size)
    (h_floor : ∀ i, lo0 ≤ i → i ≤ hi0 → flowBracketBalance tokens lo0 i ≥ 0)
    (h_lo0_lo : lo0 ≤ lo) (h_lo_hi : lo < hi) (h_hi_hi0 : hi ≤ hi0)
    (h_lo_depth0 : flowBracketBalance tokens lo0 lo = 0)
    (h_bal : flowBracketBalance tokens lo hi = 0)
    (h_hi_closer : flowBracketDelta tokens[hi]!.val = -1) : hi = hi0 := by
  rcases Nat.lt_or_ge hi hi0 with h_lt | h_ge
  · -- `hi < hi0`: the closer at `hi` drives `balance lo0 (hi+1)` to `-1`, violating the floor.
    exfalso
    have h_hi_len : hi < tokens.toList.length := by rw [Array.length_toList]; omega
    have h_single : flowBracketBalance tokens hi (hi + 1) = -1 := by
      rw [flowBracketBalance_single tokens hi h_hi_len,
        ← tok_bang_eq_toList tokens hi (by omega)]
      exact h_hi_closer
    have h_c1 := flowBracketBalance_compose tokens lo0 lo hi h_lo0_lo (by omega)
    have h_c2 := flowBracketBalance_compose tokens lo0 hi (hi + 1) (by omega) (by omega)
    have := h_floor (hi + 1) (by omega) (by omega)
    omega
  · omega

/-- **Interior escape bound**: a gated window starting strictly inside a floored balanced interior
    `[a, c)` whose successor token at `c` is a closer stays inside the interior (`hi ≤ c`). -/
lemma window_in_interior_stays (tokens : Array (Positioned YamlToken)) (a c lo hi : Nat)
    (h_c_sz : c < tokens.size)
    (h_int_bal : flowBracketBalance tokens a c = 0)
    (h_int_floor : ∀ i, a ≤ i → i ≤ c → flowBracketBalance tokens a i ≥ 0)
    (h_c_closer : flowBracketDelta tokens[c]!.val = -1)
    (h_a_lo : a ≤ lo) (h_lo_c : lo < c) (_h_lo_hi : lo < hi)
    (_h_bal : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) : hi ≤ c := by
  rcases Nat.lt_or_ge c hi with h_lt | h_ge
  · -- suppose the window escapes: its Dyck floor at `c` forces `balance a lo = 0`, and then the
    -- closer at `c` dips the window balance to `-1` at `c+1 ≤ hi` — contradiction.
    exfalso
    have h_c_len : c < tokens.toList.length := by rw [Array.length_toList]; omega
    have h_single : flowBracketBalance tokens c (c + 1) = -1 := by
      rw [flowBracketBalance_single tokens c h_c_len, ← tok_bang_eq_toList tokens c h_c_sz]
      exact h_c_closer
    have h_c1 := flowBracketBalance_compose tokens a lo c h_a_lo (by omega)
    -- `balance lo c = -(balance a lo) ≤ 0`; window dyck at `c` gives `≥ 0`; so both are `0`.
    have h_d := h_int_floor lo h_a_lo (by omega)
    have h_win_c := h_dyck c (by omega) (by omega)
    have h_lo_c_bal : flowBracketBalance tokens lo c = 0 := by omega
    have h_c2 := flowBracketBalance_compose tokens lo c (c + 1) (by omega) (by omega)
    have h_win_c1 := h_dyck (c + 1) (by omega) (by omega)
    omega
  · exact h_ge

/-! ## §3b The navigator's gate/deliverable and the two descent helpers -/

/-- The navigator's per-window deliverable: the close-keyed joint DEEP body pair (consumers
    project the flat bodies via `.toFlat`; the deep form additionally feeds the per-window
    `MapBodyProps` walk). -/
@[reducible] def DeepNavOut (tokens : Array (Positioned YamlToken)) (lo hi : Nat) : Prop :=
  (tokens[hi]!.val = .flowSequenceEnd → RecSeqBodyDeep ((tokens.toList.take hi).drop lo))
  ∧ (tokens[hi]!.val = .flowMappingEnd → RecMapBodyDeep ((tokens.toList.take hi).drop lo))

/-- The navigator's window gate under a span `[lo0, hi0)`: bounds, balance, Dyck floor, and the
    close-token/head-token conjunctive disjunction (a `]`-closed window has a content-start head or
    sits immediately inside a `[`; a `}`-closed window has a `.key` head or sits immediately inside
    a `{`). -/
@[reducible] def DeepNavGate (tokens : Array (Positioned YamlToken)) (lo0 hi0 lo hi : Nat) : Prop :=
  lo0 ≤ lo ∧ lo < hi ∧ hi ≤ hi0
  ∧ flowBracketBalance tokens lo hi = 0
  ∧ (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
  ∧ ((tokens[hi]!.val = .flowSequenceEnd
      ∧ (isFlowContentStart tokens[lo]!.val ∨ tokens[lo - 1]!.val = .flowSequenceStart))
    ∨ (tokens[hi]!.val = .flowMappingEnd
      ∧ (tokens[lo]!.val = .key ∨ tokens[lo - 1]!.val = .flowMappingStart)))

/-- **Entry descent**: a gated window starting STRICTLY inside a deep entry `[lo0, m)` is refuted
    (scalar/empty entries have no legitimate interior starts; closer positions dip the window's own
    Dyck floor) or descends into the entry's stored interior body, served by the supplied
    narrower-span navigators.  The window needs NO prior `hi`-bound: the interior escape bound
    derives `hi ≤ m - 1` from the interior's own floors. -/
lemma recentrydeep_window_navigate (tokens : Array (Positioned YamlToken)) (lo0 m : Nat)
    (h_m_sz : m ≤ tokens.size) (h_lo0_m : lo0 ≤ m)
    (h_entry : RecEntryDeep ((tokens.toList.take m).drop lo0))
    (nav_seq : ∀ a b, b - a < m - lo0 → b < tokens.size →
        RecSeqBodyDeep ((tokens.toList.take b).drop a) →
        tokens[b]!.val = .flowSequenceEnd →
        ∀ lo hi, DeepNavGate tokens a b lo hi → DeepNavOut tokens lo hi)
    (nav_map : ∀ a b, b - a < m - lo0 → b < tokens.size →
        RecMapBodyDeep ((tokens.toList.take b).drop a) →
        tokens[b]!.val = .flowMappingEnd →
        ∀ lo hi, DeepNavGate tokens a b lo hi → DeepNavOut tokens lo hi)
    (lo hi : Nat) (h_lo0_lo : lo0 < lo) (h_lo_m : lo < m) (h_lo_hi : lo < hi)
    (h_bal : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_ch : (tokens[hi]!.val = .flowSequenceEnd
        ∧ (isFlowContentStart tokens[lo]!.val ∨ tokens[lo - 1]!.val = .flowSequenceStart))
      ∨ (tokens[hi]!.val = .flowMappingEnd
        ∧ (tokens[lo]!.val = .key ∨ tokens[lo - 1]!.val = .flowMappingStart))) :
    DeepNavOut tokens lo hi := by
  rcases recentrydeep_window_cases tokens lo0 m h_lo0_m h_m_sz h_entry with
    ⟨h_m_eq, c, s, h_sc⟩ | ⟨h_m_eq, h_op, h_cl⟩ | ⟨h_m_eq, h_op, h_cl⟩
    | ⟨h_m_gt, h_op, h_cl, h_int⟩ | ⟨h_m_gt, h_op, h_cl, h_int⟩
  · -- scalar: no strictly-inside position (`lo0 < lo < lo0 + 1`).
    omega
  · -- empty `[ ]`: `lo = lo0 + 1` points at the `]`, dipping the window floor.
    exact (window_no_closer_head tokens lo hi h_lo_hi (by omega) h_dyck
      (by rw [show lo = lo0 + 1 by omega, h_cl]; rfl)).elim
  · -- empty `{ }`: mirror.
    exact (window_no_closer_head tokens lo hi h_lo_hi (by omega) h_dyck
      (by rw [show lo = lo0 + 1 by omega, h_cl]; rfl)).elim
  · -- `[ interior ]`: at the closer, refute; inside, escape-bound then recurse (seq half).
    rcases Nat.lt_or_ge lo (m - 1) with h_lo_int | h_lo_cl
    · have h_int_wb : WellBracketed ((tokens.toList.take (m - 1)).drop (lo0 + 1)) :=
        (RecSeqBodyDeep.toFlat h_int).toWellBracketed
      obtain ⟨h_int_bal, h_int_floor⟩ := wellBracketed_slice_positional tokens (lo0 + 1) (m - 1)
        (by omega) (by omega) h_int_wb
      have h_hi_le : hi ≤ m - 1 := window_in_interior_stays tokens (lo0 + 1) (m - 1) lo hi
        (by omega) h_int_bal h_int_floor (by rw [h_cl]; rfl) (by omega) h_lo_int h_lo_hi
        h_bal h_dyck
      exact nav_seq (lo0 + 1) (m - 1) (by omega) (by omega) h_int h_cl lo hi
        ⟨by omega, h_lo_hi, h_hi_le, h_bal, h_dyck, h_ch⟩
    · exact (window_no_closer_head tokens lo hi h_lo_hi (by omega) h_dyck
        (by rw [show lo = m - 1 by omega, h_cl]; rfl)).elim
  · -- `{ interior }`: mirror through the map navigator.
    rcases Nat.lt_or_ge lo (m - 1) with h_lo_int | h_lo_cl
    · have h_int_wb : WellBracketed ((tokens.toList.take (m - 1)).drop (lo0 + 1)) :=
        (RecMapBodyDeep.toFlat h_int).toWellBracketed
      obtain ⟨h_int_bal, h_int_floor⟩ := wellBracketed_slice_positional tokens (lo0 + 1) (m - 1)
        (by omega) (by omega) h_int_wb
      have h_hi_le : hi ≤ m - 1 := window_in_interior_stays tokens (lo0 + 1) (m - 1) lo hi
        (by omega) h_int_bal h_int_floor (by rw [h_cl]; rfl) (by omega) h_lo_int h_lo_hi
        h_bal h_dyck
      exact nav_map (lo0 + 1) (m - 1) (by omega) (by omega) h_int h_cl lo hi
        ⟨by omega, h_lo_hi, h_hi_le, h_bal, h_dyck, h_ch⟩
    · exact (window_no_closer_head tokens lo hi h_lo_hi (by omega) h_dyck
        (by rw [show lo = m - 1 by omega, h_cl]; rfl)).elim

/-- A deep entry's LAST token is never an opener (it is a scalar or a closer) — the fact that
    refutes windows starting just past an entry/block with the `tokens[lo-1]`-opener fallback. -/
lemma recentrydeep_last_not_opener (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h_ab : a ≤ b) (h_b_sz : b ≤ tokens.size)
    (h_e : RecEntryDeep ((tokens.toList.take b).drop a)) :
    ¬ (tokens[b - 1]!.val = .flowSequenceStart ∨ tokens[b - 1]!.val = .flowMappingStart) := by
  rcases recentrydeep_window_cases tokens a b h_ab h_b_sz h_e with
    ⟨h_b_eq, c, s, h_sc⟩ | ⟨h_b_eq, h_op, h_cl⟩ | ⟨h_b_eq, h_op, h_cl⟩
    | ⟨h_b_gt, h_op, h_cl, _⟩ | ⟨h_b_gt, h_op, h_cl, _⟩
  · rw [show b - 1 = a by omega, h_sc]; rintro (h | h) <;> cases h
  · rw [show b - 1 = a + 1 by omega, h_cl]; rintro (h | h) <;> cases h
  · rw [show b - 1 = a + 1 by omega, h_cl]; rintro (h | h) <;> cases h
  · rw [h_cl]; rintro (h | h) <;> cases h
  · rw [h_cl]; rintro (h | h) <;> cases h

/-- A deep entry's HEAD token is a content-start (scalar or opener) — the fact that refutes the
    `.key`-head gate at map-pair block heads. -/
lemma recentrydeep_head_shapes (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h_ab : a ≤ b) (h_b_sz : b ≤ tokens.size)
    (h_e : RecEntryDeep ((tokens.toList.take b).drop a)) :
    (∃ c s, tokens[a]!.val = .scalar c s)
    ∨ tokens[a]!.val = .flowSequenceStart ∨ tokens[a]!.val = .flowMappingStart := by
  rcases recentrydeep_window_cases tokens a b h_ab h_b_sz h_e with
    ⟨_, c, s, h_sc⟩ | ⟨_, h_op, _⟩ | ⟨_, h_op, _⟩ | ⟨_, h_op, _, _⟩ | ⟨_, h_op, _, _⟩
  · exact Or.inl ⟨c, s, h_sc⟩
  · exact Or.inr (Or.inl h_op)
  · exact Or.inr (Or.inr h_op)
  · exact Or.inr (Or.inl h_op)
  · exact Or.inr (Or.inr h_op)

/-- **Pair descent**: a gated window starting STRICTLY inside a deep map pair `[lo0, m')` of a map
    body floored on `[lo0, hi0)` (close `}` at `hi0`) is refuted (block-head and `.value`-position
    starts fail the head gates after the depth-`0` forcing) or descends into a key/value block's
    stored interior, served by the supplied narrower-span navigators. -/
lemma recmappairdeep_window_navigate (tokens : Array (Positioned YamlToken))
    (lo0 m' hi0 : Nat)
    (h_lo0_m' : lo0 < m') (h_m'_hi0 : m' ≤ hi0) (h_hi0_sz : hi0 < tokens.size)
    (h_pair : RecMapPairDeep ((tokens.toList.take m').drop lo0))
    (h_body_floor : ∀ i, lo0 ≤ i → i ≤ hi0 → flowBracketBalance tokens lo0 i ≥ 0)
    (h_close0 : tokens[hi0]!.val = .flowMappingEnd)
    (nav_seq : ∀ a b, b - a < m' - lo0 → b < tokens.size →
        RecSeqBodyDeep ((tokens.toList.take b).drop a) →
        tokens[b]!.val = .flowSequenceEnd →
        ∀ lo hi, DeepNavGate tokens a b lo hi → DeepNavOut tokens lo hi)
    (nav_map : ∀ a b, b - a < m' - lo0 → b < tokens.size →
        RecMapBodyDeep ((tokens.toList.take b).drop a) →
        tokens[b]!.val = .flowMappingEnd →
        ∀ lo hi, DeepNavGate tokens a b lo hi → DeepNavOut tokens lo hi)
    (lo hi : Nat) (h_lo0_lo : lo0 < lo) (h_lo_m' : lo < m') (h_lo_hi : lo < hi)
    (h_hi_hi0 : hi ≤ hi0)
    (h_bal : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0)
    (h_ch : (tokens[hi]!.val = .flowSequenceEnd
        ∧ (isFlowContentStart tokens[lo]!.val ∨ tokens[lo - 1]!.val = .flowSequenceStart))
      ∨ (tokens[hi]!.val = .flowMappingEnd
        ∧ (tokens[lo]!.val = .key ∨ tokens[lo - 1]!.val = .flowMappingStart))) :
    DeepNavOut tokens lo hi := by
  obtain ⟨kv, h_lo0_kv, h_kv_m', h_kt, h_vt, h_bk, h_bv⟩ :=
    recmappairdeep_window_descent tokens lo0 m' h_lo0_m' (by omega) h_pair
  have h_hi_closer : flowBracketDelta tokens[hi]!.val = -1 := by
    rcases h_ch with ⟨h_cl, _⟩ | ⟨h_cl, _⟩ <;> rw [h_cl] <;> rfl
  -- Shared block-head refutation: at a depth-`0` in-pair start, the window is forced to the body
  -- end (`tokens[hi] = }`), and then every head gate fails.
  have block_head_refuted : ∀ (a b : Nat), lo = a →
      flowBracketBalance tokens lo0 lo = 0 →
      a ≤ b → b ≤ tokens.size →
      RecEntryDeep ((tokens.toList.take b).drop a) →
      tokens[lo - 1]!.val ≠ .flowMappingStart →
      DeepNavOut tokens lo hi := by
    intro a b h_lo_a h_d0 h_a_b h_b_sz h_blk h_prev
    have h_hi_eq : hi = hi0 := window_depth0_closer_ends_at_end tokens lo0 hi0 lo hi
      (Nat.le_of_lt h_hi0_sz) h_body_floor (by omega) h_lo_hi h_hi_hi0 h_d0 h_bal h_hi_closer
    exfalso
    rcases h_ch with ⟨h_cl, _⟩ | ⟨_, h_head | h_head⟩
    · rw [h_hi_eq, h_close0] at h_cl
      exact absurd h_cl (by decide)
    · -- `.key` head: the block head is a scalar or an opener, never `.key`.
      rcases recentrydeep_head_shapes tokens a b h_a_b h_b_sz h_blk with
        ⟨c, s, h_sc⟩ | h_op | h_op
      · rw [h_lo_a, h_sc] at h_head; cases h_head
      · rw [h_lo_a, h_op] at h_head; cases h_head
      · rw [h_lo_a, h_op] at h_head; cases h_head
    · exact h_prev h_head
  rcases Nat.lt_trichotomy lo kv with h_lo_bk | h_lo_kv | h_kv_lo
  · -- block_k zone `[lo0+1, kv)`
    rcases Nat.eq_or_lt_of_le (show lo0 + 1 ≤ lo from by omega) with h_head_eq | h_inside
    · -- `lo = lo0 + 1`: the key block's head
      refine block_head_refuted (lo0 + 1) kv h_head_eq.symm ?_ (by omega) (by omega) h_bk ?_
      · -- `balance lo0 (lo0+1) = 0`: the `.key` token has delta `0`.
        rw [← h_head_eq]
        rw [flowBracketBalance_single tokens lo0 (by rw [Array.length_toList]; omega),
          ← tok_bang_eq_toList tokens lo0 (by omega), h_kt]
        rfl
      · -- `tokens[lo-1] = tokens[lo0] = .key ≠ {`
        rw [show lo - 1 = lo0 by omega, h_kt]
        intro h; cases h
    · -- strictly inside block_k: entry descent
      exact recentrydeep_window_navigate tokens (lo0 + 1) kv (by omega) (by omega) h_bk
        (fun a b h_lt h_b_sz h_bd h_cl lo' hi' h_g =>
          nav_seq a b (by omega) h_b_sz h_bd h_cl lo' hi' h_g)
        (fun a b h_lt h_b_sz h_bd h_cl lo' hi' h_g =>
          nav_map a b (by omega) h_b_sz h_bd h_cl lo' hi' h_g)
        lo hi h_inside h_lo_bk h_lo_hi h_bal h_dyck h_ch
  · -- `lo = kv`: at the `.value` separator — every head gate fails.
    exfalso
    rcases h_ch with ⟨_, h_head | h_head⟩ | ⟨_, h_head | h_head⟩
    · rw [h_lo_kv, h_vt] at h_head
      simp [isFlowContentStart] at h_head
    · rw [show lo - 1 = kv - 1 by omega] at h_head
      exact recentrydeep_last_not_opener tokens (lo0 + 1) kv (by omega) (by omega) h_bk
        (Or.inl h_head)
    · rw [h_lo_kv, h_vt] at h_head; cases h_head
    · rw [show lo - 1 = kv - 1 by omega] at h_head
      exact recentrydeep_last_not_opener tokens (lo0 + 1) kv (by omega) (by omega) h_bk
        (Or.inr h_head)
  · -- block_v zone `[kv+1, m')`
    rcases Nat.eq_or_lt_of_le (show kv + 1 ≤ lo from by omega) with h_head_eq | h_inside
    · -- `lo = kv + 1`: the value block's head
      refine block_head_refuted (kv + 1) m' h_head_eq.symm ?_ (by omega) (by omega) h_bv ?_
      · -- `balance lo0 (kv+1) = 0`: `.key` + balanced key block + `.value` compose to `0`.
        have h_b1 : flowBracketBalance tokens lo0 (lo0 + 1) = 0 := by
          rw [flowBracketBalance_single tokens lo0 (by rw [Array.length_toList]; omega),
            ← tok_bang_eq_toList tokens lo0 (by omega), h_kt]
          rfl
        have h_bk_wb : WellBracketed ((tokens.toList.take kv).drop (lo0 + 1)) :=
          (RecEntryDeep.toFlat h_bk).toWellBracketed
        obtain ⟨h_b2, _⟩ := wellBracketed_slice_positional tokens (lo0 + 1) kv
          (by omega) (by omega) h_bk_wb
        have h_b3 : flowBracketBalance tokens kv (kv + 1) = 0 := by
          rw [flowBracketBalance_single tokens kv (by rw [Array.length_toList]; omega),
            ← tok_bang_eq_toList tokens kv (by omega), h_vt]
          rfl
        have h_c1 := flowBracketBalance_compose tokens lo0 (lo0 + 1) kv (by omega) (by omega)
        have h_c2 := flowBracketBalance_compose tokens lo0 kv (kv + 1) (by omega) (by omega)
        rw [← h_head_eq]
        omega
      · -- `tokens[lo-1] = tokens[kv] = .value ≠ {`
        rw [show lo - 1 = kv by omega, h_vt]
        intro h; cases h
    · -- strictly inside block_v: entry descent
      exact recentrydeep_window_navigate tokens (kv + 1) m' (by omega) (by omega) h_bv
        (fun a b h_lt h_b_sz h_bd h_cl lo' hi' h_g =>
          nav_seq a b (by omega) h_b_sz h_bd h_cl lo' hi' h_g)
        (fun a b h_lt h_b_sz h_bd h_cl lo' hi' h_g =>
          nav_map a b (by omega) h_b_sz h_bd h_cl lo' hi' h_g)
        lo hi h_inside h_lo_m' h_lo_hi h_bal h_dyck h_ch

/-! ## §3d The joint navigator

One span-bound strong induction delivering, at every gated sub-window of a stored deep body, the
close-keyed joint deliverable.  The two halves (seq body / map body) mirror each other: force the
whole-window delivery at `lo = lo0`, dispatch the split at `lo > lo0` (first entry/pair descent,
separator refutation, suffix recursion). -/

lemma deep_navigate_core (tokens : Array (Positioned YamlToken)) :
    ∀ (span lo0 hi0 : Nat), hi0 - lo0 ≤ span → hi0 < tokens.size →
      (RecSeqBodyDeep ((tokens.toList.take hi0).drop lo0) →
        tokens[hi0]!.val = .flowSequenceEnd →
        ∀ lo hi, DeepNavGate tokens lo0 hi0 lo hi → DeepNavOut tokens lo hi)
      ∧ (RecMapBodyDeep ((tokens.toList.take hi0).drop lo0) →
        tokens[hi0]!.val = .flowMappingEnd →
        ∀ lo hi, DeepNavGate tokens lo0 hi0 lo hi → DeepNavOut tokens lo hi) := by
  intro span
  induction span using Nat.strongRecOn with
  | ind span IH =>
    intro lo0 hi0 h_span h_hi0_sz
    -- The IH re-packaged as the two narrower-span navigator oracles the descent helpers consume.
    have nav_seq : ∀ a b, b - a < hi0 - lo0 → b < tokens.size →
        RecSeqBodyDeep ((tokens.toList.take b).drop a) →
        tokens[b]!.val = .flowSequenceEnd →
        ∀ lo hi, DeepNavGate tokens a b lo hi → DeepNavOut tokens lo hi := by
      intro a b h_lt h_b_sz h_bd h_cl lo hi h_g
      exact (IH (b - a) (by omega) a b (Nat.le_refl _) h_b_sz).1 h_bd h_cl lo hi h_g
    have nav_map : ∀ a b, b - a < hi0 - lo0 → b < tokens.size →
        RecMapBodyDeep ((tokens.toList.take b).drop a) →
        tokens[b]!.val = .flowMappingEnd →
        ∀ lo hi, DeepNavGate tokens a b lo hi → DeepNavOut tokens lo hi := by
      intro a b h_lt h_b_sz h_bd h_cl lo hi h_g
      exact (IH (b - a) (by omega) a b (Nat.le_refl _) h_b_sz).2 h_bd h_cl lo hi h_g
    constructor
    · -- ── SEQ body half ──
      intro h_body h_close0 lo hi h_gate
      obtain ⟨h_lo0_lo, h_lo_hi, h_hi_hi0, h_bal, h_dyck, h_ch⟩ := h_gate
      have h_hi_closer : flowBracketDelta tokens[hi]!.val = -1 := by
        rcases h_ch with ⟨h_cl, _⟩ | ⟨h_cl, _⟩ <;> rw [h_cl] <;> rfl
      have h_lo0_hi0 : lo0 ≤ hi0 := by omega
      have h_wb : WellBracketed ((tokens.toList.take hi0).drop lo0) :=
        (RecSeqBodyDeep.toFlat h_body).toWellBracketed
      obtain ⟨h_body_bal, h_body_floor⟩ :=
        wellBracketed_slice_positional tokens lo0 hi0 h_lo0_hi0 (Nat.le_of_lt h_hi0_sz) h_wb
      rcases Nat.eq_or_lt_of_le h_lo0_lo with h_eq | h_lo0_lt
      · -- `lo = lo0`: the depth-`0` closer forcing pins `hi = hi0`; deliver the whole body.
        have h_lo_d0 : flowBracketBalance tokens lo0 lo = 0 := by
          rw [← h_eq]
          unfold flowBracketBalance
          rw [if_pos (Nat.le_refl lo0)]
        have h_hi_eq : hi = hi0 := window_depth0_closer_ends_at_end tokens lo0 hi0 lo hi
          (Nat.le_of_lt h_hi0_sz) h_body_floor h_lo0_lo h_lo_hi h_hi_hi0 h_lo_d0 h_bal
          h_hi_closer
        refine ⟨fun _ => ?_, fun h_fme => ?_⟩
        · rw [h_hi_eq, ← h_eq]
          exact h_body
        · rw [h_hi_eq, h_close0] at h_fme
          exact absurd h_fme (by decide)
      · -- `lo0 < lo`: split the body and dispatch.
        rcases recseqbodydeep_window_split tokens lo0 hi0 h_lo0_hi0 (Nat.le_of_lt h_hi0_sz)
          h_body with h_entry | ⟨m, h_lo0_m, h_m_hi0, h_m_fe, h_entry, h_rest⟩
        · -- single entry spanning the whole window: descend into it.
          exact recentrydeep_window_navigate tokens lo0 hi0 (Nat.le_of_lt h_hi0_sz) h_lo0_hi0
            h_entry nav_seq nav_map lo hi h_lo0_lt (by omega) h_lo_hi h_bal h_dyck h_ch
        · rcases Nat.lt_trichotomy lo m with h_lo_lt_m | h_lo_eq_m | h_m_lt_lo
          · -- strictly inside the first entry `[lo0, m)`.
            exact recentrydeep_window_navigate tokens lo0 m (by omega) (by omega) h_entry
              (fun a b h_lt h_b_sz h_bd h_cl lo' hi' h_g =>
                nav_seq a b (by omega) h_b_sz h_bd h_cl lo' hi' h_g)
              (fun a b h_lt h_b_sz h_bd h_cl lo' hi' h_g =>
                nav_map a b (by omega) h_b_sz h_bd h_cl lo' hi' h_g)
              lo hi h_lo0_lt h_lo_lt_m h_lo_hi h_bal h_dyck h_ch
          · -- `lo = m`: the depth-`0` separator — every head gate fails.
            exfalso
            rcases h_ch with ⟨_, h_head | h_head⟩ | ⟨_, h_head | h_head⟩
            · rw [h_lo_eq_m, h_m_fe] at h_head
              simp [isFlowContentStart] at h_head
            · rw [show lo - 1 = m - 1 by omega] at h_head
              exact recentrydeep_last_not_opener tokens lo0 m (by omega) (by omega) h_entry
                (Or.inl h_head)
            · rw [h_lo_eq_m, h_m_fe] at h_head; cases h_head
            · rw [show lo - 1 = m - 1 by omega] at h_head
              exact recentrydeep_last_not_opener tokens lo0 m (by omega) (by omega) h_entry
                (Or.inr h_head)
          · -- `m < lo`: the window sits in the suffix `[m+1, hi0)` — recurse.
            exact nav_seq (m + 1) hi0 (by omega) h_hi0_sz h_rest h_close0 lo hi
              ⟨by omega, h_lo_hi, h_hi_hi0, h_bal, h_dyck, h_ch⟩
    · -- ── MAP body half ──
      intro h_body h_close0 lo hi h_gate
      obtain ⟨h_lo0_lo, h_lo_hi, h_hi_hi0, h_bal, h_dyck, h_ch⟩ := h_gate
      have h_hi_closer : flowBracketDelta tokens[hi]!.val = -1 := by
        rcases h_ch with ⟨h_cl, _⟩ | ⟨h_cl, _⟩ <;> rw [h_cl] <;> rfl
      have h_lo0_hi0 : lo0 ≤ hi0 := by omega
      have h_wb : WellBracketed ((tokens.toList.take hi0).drop lo0) :=
        (RecMapBodyDeep.toFlat h_body).toWellBracketed
      obtain ⟨h_body_bal, h_body_floor⟩ :=
        wellBracketed_slice_positional tokens lo0 hi0 h_lo0_hi0 (Nat.le_of_lt h_hi0_sz) h_wb
      rcases Nat.eq_or_lt_of_le h_lo0_lo with h_eq | h_lo0_lt
      · have h_lo_d0 : flowBracketBalance tokens lo0 lo = 0 := by
          rw [← h_eq]
          unfold flowBracketBalance
          rw [if_pos (Nat.le_refl lo0)]
        have h_hi_eq : hi = hi0 := window_depth0_closer_ends_at_end tokens lo0 hi0 lo hi
          (Nat.le_of_lt h_hi0_sz) h_body_floor h_lo0_lo h_lo_hi h_hi_hi0 h_lo_d0 h_bal
          h_hi_closer
        refine ⟨fun h_fse => ?_, fun _ => ?_⟩
        · rw [h_hi_eq, h_close0] at h_fse
          exact absurd h_fse (by decide)
        · rw [h_hi_eq, ← h_eq]
          exact h_body
      · rcases recmapbodydeep_window_split tokens lo0 hi0 h_lo0_hi0 (Nat.le_of_lt h_hi0_sz)
          h_body with h_pair | ⟨m, h_lo0_m, h_m_hi0, h_m_fe, h_pair, h_rest⟩
        · -- single pair spanning the whole window: descend into it.
          exact recmappairdeep_window_navigate tokens lo0 hi0 hi0 (by omega) (Nat.le_refl hi0)
            h_hi0_sz h_pair h_body_floor h_close0 nav_seq nav_map lo hi h_lo0_lt (by omega)
            h_lo_hi h_hi_hi0 h_bal h_dyck h_ch
        · rcases Nat.lt_trichotomy lo m with h_lo_lt_m | h_lo_eq_m | h_m_lt_lo
          · -- strictly inside the first pair `[lo0, m)`.
            exact recmappairdeep_window_navigate tokens lo0 m hi0 h_lo0_m (by omega) h_hi0_sz
              h_pair h_body_floor h_close0
              (fun a b h_lt h_b_sz h_bd h_cl lo' hi' h_g =>
                nav_seq a b (by omega) h_b_sz h_bd h_cl lo' hi' h_g)
              (fun a b h_lt h_b_sz h_bd h_cl lo' hi' h_g =>
                nav_map a b (by omega) h_b_sz h_bd h_cl lo' hi' h_g)
              lo hi h_lo0_lt h_lo_lt_m h_lo_hi h_hi_hi0 h_bal h_dyck h_ch
          · -- `lo = m`: the depth-`0` pair separator — every head gate fails (the pair's last
            -- token is the value block's last token, never an opener).
            exfalso
            obtain ⟨kv, h_lo0_kv, h_kv_m, h_kt, h_vt, h_bk, h_bv⟩ :=
              recmappairdeep_window_descent tokens lo0 m h_lo0_m (by omega) h_pair
            rcases h_ch with ⟨_, h_head | h_head⟩ | ⟨_, h_head | h_head⟩
            · rw [h_lo_eq_m, h_m_fe] at h_head
              simp [isFlowContentStart] at h_head
            · rw [show lo - 1 = m - 1 by omega] at h_head
              exact recentrydeep_last_not_opener tokens (kv + 1) m (by omega) (by omega) h_bv
                (Or.inl h_head)
            · rw [h_lo_eq_m, h_m_fe] at h_head; cases h_head
            · rw [show lo - 1 = m - 1 by omega] at h_head
              exact recentrydeep_last_not_opener tokens (kv + 1) m (by omega) (by omega) h_bv
                (Or.inr h_head)
          · -- `m < lo`: suffix recursion.
            exact nav_map (m + 1) hi0 (by omega) h_hi0_sz h_rest h_close0 lo hi
              ⟨by omega, h_lo_hi, h_hi_hi0, h_bal, h_dyck, h_ch⟩

/-! ## §4 The deep root seed

The `RecSeqBodyDeep` mirror of `seqRoot_recseqbody`: replay the open-bracket → body →
close-bracket scan chain, feeding the body through the DEEP chain producer
`emitList_scans_recseqbodyDeep`, then re-slice through the same token-decomposition identity.
The adapter below is `emitList_body_recseqbody` with the producer (and deliverable) swapped —
byte-identical scan-state steps ([[ref-recursive-producer-mirrors-flat-over-shared-induction]]). -/

lemma emitList_body_recseqbodyDeep
    (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, EmitScansInFlowRecEntryDeep v)
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
    ∧ RecSeqBodyDeep ((s'.tokens.filter p).toList.drop old_sz) := by
  obtain ⟨n, s', block, h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, h_block_eq, h_wb, h_wt,
          h_rec, _h_oa, _h_sa⟩ :=
    emitList_scans_recseqbodyDeep items h_ne h_all s rest h_corr h_flow h_fl h_indent h_col
      h_ek h_atol h_endline h_sync
  have h_drop : (s'.tokens.filter (fun t => t.val != .placeholder)).toList.drop
      (s.tokens.filter (fun t => t.val != .placeholder)).size = block := by
    rw [h_block_eq,
      show (s.tokens.filter (fun t => t.val != .placeholder)).size
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList.length
        from Array.length_toList.symm,
      List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
  refine ⟨n, s', h_chain.toScanChain, h_corr', h_fl', h_dp', h_ids', h_ek',
          h_col', h_inflow', h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, ?_⟩
  show RecSeqBodyDeep ((s'.tokens.filter (fun t => t.val != .placeholder)).toList.drop
      (s.tokens.filter (fun t => t.val != .placeholder)).size)
  rw [h_drop]; exact h_rec

/-- **Deep seq root seed** — `RecSeqBodyDeep` of the root body window `[2, size-2)` off emission;
    the severance-free mirror of `seqRoot_recseqbody`, keyed on the DEEP per-item hypothesis. -/
lemma seqRoot_recseqbodyDeep
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntryDeep v) :
    RecSeqBodyDeep ((tokens.toList.take (tokens.size - 2)).drop 2) := by
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
  -- Body scanning → s₂ via the DEEP producer (delivers `RecSeqBodyDeep` of the body block)
  obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_inflow₂,
          h_indent₂, h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂, h_rec₂⟩ :=
    emitList_body_recseqbodyDeep items.toList h_ne h_all s₁ [']']
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
  -- The body block's `RecSeqBodyDeep`, re-sliced to the outer window `[2, size-2)`.
  rw [h_filt₁_sz] at h_rec₂
  rw [h_take_eq]
  exact h_rec₂

/-! ## §5 Per-window `MapBodyProps` directly from the deep body

`FlowSubrangesOk.map` owes `MapBodyProps` at every map window.  The landed producers
(`mapBodyProps_of_recmapbody_window[_guarded]`) still lift bracket-`succ` primitives whose
∀-`j` shape is UNSATISFIABLE on emissions with two bracket-valued pairs (the R548 decoy: a later
pair's closer also returns the window balance to `0`).  With the DEEP body now available at every
window (the navigator's map half), the ten fields are instead read DIRECTLY off the pair
structure: a depth-`0` position is a pair head, a `.value` separator, a depth-`0` `.flowEntry`,
or a block head — and each field's successor payload is the block's own stored shape, with the
own-close pinned by the block's interior floors (never a generic closer). -/

/-- A deep entry (block) is at least one token wide. -/
lemma recentrydeep_width_pos (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h_ab : a ≤ b) (h_b_sz : b ≤ tokens.size)
    (h_e : RecEntryDeep ((tokens.toList.take b).drop a)) : a < b := by
  rcases recentrydeep_window_cases tokens a b h_ab h_b_sz h_e with
    ⟨h_eq, _⟩ | ⟨h_eq, _⟩ | ⟨h_eq, _⟩ | ⟨h_gt, _⟩ | ⟨h_gt, _⟩ <;> omega

/-- Strictly-inside positions of a deep entry (block) spanning `[a, b)` sit at depth `≥ 1`
    relative to the block start: `flowBracketBalance tokens a k ≥ 1` for `a < k < b`. -/
lemma recentrydeep_interior_pos (tokens : Array (Positioned YamlToken)) (a b k : Nat)
    (h_ab : a ≤ b) (h_b_sz : b ≤ tokens.size)
    (h_e : RecEntryDeep ((tokens.toList.take b).drop a))
    (h_a_k : a < k) (h_k_b : k < b) :
    flowBracketBalance tokens a k ≥ 1 := by
  rcases recentrydeep_window_cases tokens a b h_ab h_b_sz h_e with
    ⟨h_eq, c, s, h_sc⟩ | ⟨h_eq, h_op, h_cl⟩ | ⟨h_eq, h_op, h_cl⟩
    | ⟨h_gt, h_op, h_cl, h_int⟩ | ⟨h_gt, h_op, h_cl, h_int⟩
  · omega
  · -- empty `[ ]`: the only strictly-inside position is the closer at `a+1`, at depth `1`.
    have h_k_eq : k = a + 1 := by omega
    subst h_k_eq
    have h_a_len : a < tokens.toList.length := by rw [Array.length_toList]; omega
    rw [flowBracketBalance_single tokens a h_a_len, ← tok_bang_eq_toList tokens a (by omega),
      h_op]
    decide
  · have h_k_eq : k = a + 1 := by omega
    subst h_k_eq
    have h_a_len : a < tokens.toList.length := by rw [Array.length_toList]; omega
    rw [flowBracketBalance_single tokens a h_a_len, ← tok_bang_eq_toList tokens a (by omega),
      h_op]
    decide
  · -- `[ interior ]`: opener `+1` then the interior's Dyck floor keeps the depth `≥ 1` up to the
    -- close (the position `b-1` itself included: interior total `0` + the opener).
    have h_int_wb : WellBracketed ((tokens.toList.take (b - 1)).drop (a + 1)) :=
      (RecSeqBodyDeep.toFlat h_int).toWellBracketed
    obtain ⟨h_int_bal, h_int_floor⟩ := wellBracketed_slice_positional tokens (a + 1) (b - 1)
      (by omega) (by omega) h_int_wb
    have h_a_len : a < tokens.toList.length := by rw [Array.length_toList]; omega
    have h_step : flowBracketBalance tokens a (a + 1) = 1 := by
      rw [flowBracketBalance_single tokens a h_a_len, ← tok_bang_eq_toList tokens a (by omega),
        h_op]
      decide
    have h_c := flowBracketBalance_compose tokens a (a + 1) k (by omega) (by omega)
    rcases Nat.lt_or_ge k (b - 1) with h_k_int | h_k_cl
    · have := h_int_floor k (by omega) (by omega)
      omega
    · have h_k_eq : k = b - 1 := by omega
      subst h_k_eq
      have h_c2 := flowBracketBalance_compose tokens (a + 1) (b - 1) (b - 1)
        (by omega) (by omega)
      omega
  · have h_int_wb : WellBracketed ((tokens.toList.take (b - 1)).drop (a + 1)) :=
      (RecMapBodyDeep.toFlat h_int).toWellBracketed
    obtain ⟨h_int_bal, h_int_floor⟩ := wellBracketed_slice_positional tokens (a + 1) (b - 1)
      (by omega) (by omega) h_int_wb
    have h_a_len : a < tokens.toList.length := by rw [Array.length_toList]; omega
    have h_step : flowBracketBalance tokens a (a + 1) = 1 := by
      rw [flowBracketBalance_single tokens a h_a_len, ← tok_bang_eq_toList tokens a (by omega),
        h_op]
      decide
    have h_c := flowBracketBalance_compose tokens a (a + 1) k (by omega) (by omega)
    rcases Nat.lt_or_ge k (b - 1) with h_k_int | h_k_cl
    · have := h_int_floor k (by omega) (by omega)
      omega
    · have h_k_eq : k = b - 1 := by omega
      subst h_k_eq
      have h_c2 := flowBracketBalance_compose tokens (a + 1) (b - 1) (b - 1)
        (by omega) (by omega)
      omega

/-- A deep entry (block) spanning `[a, b)` is balanced: `flowBracketBalance tokens a b = 0`. -/
lemma recentrydeep_balanced (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h_ab : a ≤ b) (h_b_sz : b ≤ tokens.size)
    (h_e : RecEntryDeep ((tokens.toList.take b).drop a)) :
    flowBracketBalance tokens a b = 0 :=
  (wellBracketed_slice_positional tokens a b h_ab h_b_sz
    (RecEntryDeep.toFlat h_e).toWellBracketed).1

/-- A deep map body is at least one token wide. -/
lemma recmapbodydeep_width_pos (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h_ab : a ≤ b) (h_b_sz : b ≤ tokens.size)
    (h_body : RecMapBodyDeep ((tokens.toList.take b).drop a)) : a < b := by
  have h_slice_len : ((tokens.toList.take b).drop a).length = b - a := by
    rw [List.length_drop, List.length_take, Array.length_toList, Nat.min_eq_left h_b_sz]
  have h_ne : ((tokens.toList.take b).drop a).length > 0 := by
    generalize h_shape : (tokens.toList.take b).drop a = l at h_body h_slice_len
    cases h_body with
    | single p h_ne _ _ => exact List.length_pos_iff.mpr h_ne
    | cons p fe rest h_ne _ _ _ _ =>
      have := List.length_pos_iff.mpr h_ne
      simp [List.length_append]
      omega
  omega

/-- **Depth-`0` position classification of a deep map body.**  Every depth-`0` position of the
    body `[lo0, hi0)` is a pair head (`.key`, with its value separator, blocks, and pair-end
    marker), a value separator (`.value`, with its block and pair-end marker), a depth-`0`
    `.flowEntry` (followed by the next pair's `.key`), or a block head (carrying its own stored
    entry).  The payloads are exactly what the ten `MapBodyProps` fields read off. -/
lemma recmapbodydeep_depth0_classify (tokens : Array (Positioned YamlToken)) :
    ∀ (span lo0 hi0 : Nat), hi0 - lo0 ≤ span → hi0 ≤ tokens.size →
      RecMapBodyDeep ((tokens.toList.take hi0).drop lo0) →
      ∀ k, lo0 ≤ k → k < hi0 → flowBracketBalance tokens lo0 k = 0 →
      (tokens[k]!.val = .key ∧ ∃ kv e, k < kv ∧ kv < e ∧ e ≤ hi0
          ∧ tokens[kv]!.val = .value
          ∧ RecEntryDeep ((tokens.toList.take kv).drop (k + 1))
          ∧ RecEntryDeep ((tokens.toList.take e).drop (kv + 1))
          ∧ (e = hi0 ∨ tokens[e]!.val = .flowEntry))
      ∨ (tokens[k]!.val = .value ∧ ∃ e, k < e ∧ e ≤ hi0
          ∧ RecEntryDeep ((tokens.toList.take e).drop (k + 1))
          ∧ (e = hi0 ∨ tokens[e]!.val = .flowEntry))
      ∨ (tokens[k]!.val = .flowEntry ∧ k + 1 < hi0 ∧ tokens[k + 1]!.val = .key)
      ∨ (∃ b, k < b ∧ b ≤ hi0 ∧ RecEntryDeep ((tokens.toList.take b).drop k)) := by
  intro span
  induction span using Nat.strongRecOn with
  | ind span IH =>
    intro lo0 hi0 h_span h_hi0_sz h_body k h_lo0_k h_k_hi0 h_k_d0
    have h_lo0_hi0 : lo0 ≤ hi0 := by omega
    rcases recmapbodydeep_window_split tokens lo0 hi0 h_lo0_hi0 h_hi0_sz h_body with
      h_pair | ⟨m, h_lo0_m, h_m_hi0, h_m_fe, h_pair, h_rest⟩
    · -- single pair spanning `[lo0, hi0)`
      obtain ⟨kv, h_lo0_kv, h_kv_m, h_kt, h_vt, h_bk, h_bv⟩ :=
        recmappairdeep_window_descent tokens lo0 hi0 (by omega) h_hi0_sz h_pair
      have h_bk_w := recentrydeep_width_pos tokens (lo0 + 1) kv (by omega) (by omega) h_bk
      have h_bv_w := recentrydeep_width_pos tokens (kv + 1) hi0 (by omega) (by omega) h_bv
      rcases Nat.eq_or_lt_of_le h_lo0_k with h_eq | h_k_gt
      · exact Or.inl ⟨h_eq ▸ h_kt, kv, hi0, by omega, by omega, Nat.le_refl _, h_vt, by
          rw [← h_eq]; exact h_bk, h_bv, Or.inl rfl⟩
      · rcases Nat.lt_trichotomy k kv with h_k_bk | h_k_kv | h_kv_k
        · -- in the key block zone
          rcases Nat.eq_or_lt_of_le (show lo0 + 1 ≤ k from by omega) with h_head | h_inside
          · exact Or.inr (Or.inr (Or.inr ⟨kv, by omega, by omega, h_head ▸ h_bk⟩))
          · exfalso
            have := recentrydeep_interior_pos tokens (lo0 + 1) kv k (by omega) (by omega)
              h_bk h_inside h_k_bk
            have h_b1 : flowBracketBalance tokens lo0 (lo0 + 1) = 0 := by
              rw [flowBracketBalance_single tokens lo0
                  (by rw [Array.length_toList]; omega),
                ← tok_bang_eq_toList tokens lo0 (by omega), h_kt]
              rfl
            have h_c := flowBracketBalance_compose tokens lo0 (lo0 + 1) k (by omega) (by omega)
            omega
        · exact Or.inr (Or.inl ⟨h_k_kv ▸ h_vt, hi0, by omega, Nat.le_refl _, by
            rw [h_k_kv]; exact h_bv, Or.inl rfl⟩)
        · -- in the value block zone
          rcases Nat.eq_or_lt_of_le (show kv + 1 ≤ k from by omega) with h_head | h_inside
          · exact Or.inr (Or.inr (Or.inr ⟨hi0, by omega, Nat.le_refl _, h_head ▸ h_bv⟩))
          · exfalso
            have := recentrydeep_interior_pos tokens (kv + 1) hi0 k (by omega) h_hi0_sz
              h_bv h_inside h_k_hi0
            have h_b1 : flowBracketBalance tokens lo0 (lo0 + 1) = 0 := by
              rw [flowBracketBalance_single tokens lo0
                  (by rw [Array.length_toList]; omega),
                ← tok_bang_eq_toList tokens lo0 (by omega), h_kt]
              rfl
            have h_b2 := recentrydeep_balanced tokens (lo0 + 1) kv (by omega) (by omega) h_bk
            have h_b3 : flowBracketBalance tokens kv (kv + 1) = 0 := by
              rw [flowBracketBalance_single tokens kv
                  (by rw [Array.length_toList]; omega),
                ← tok_bang_eq_toList tokens kv (by omega), h_vt]
              rfl
            have h_c1 := flowBracketBalance_compose tokens lo0 (lo0 + 1) kv (by omega) (by omega)
            have h_c2 := flowBracketBalance_compose tokens lo0 kv (kv + 1) (by omega) (by omega)
            have h_c3 := flowBracketBalance_compose tokens lo0 (kv + 1) k (by omega) (by omega)
            omega
    · -- cons: pair `[lo0, m)`, separator at `m`, rest `[m+1, hi0)`
      obtain ⟨kv, h_lo0_kv, h_kv_m, h_kt, h_vt, h_bk, h_bv⟩ :=
        recmappairdeep_window_descent tokens lo0 m h_lo0_m (by omega) h_pair
      have h_bk_w := recentrydeep_width_pos tokens (lo0 + 1) kv (by omega) (by omega) h_bk
      have h_bv_w := recentrydeep_width_pos tokens (kv + 1) m (by omega) (by omega) h_bv
      -- shared balance chain to the separator and past it
      have h_b1 : flowBracketBalance tokens lo0 (lo0 + 1) = 0 := by
        rw [flowBracketBalance_single tokens lo0 (by rw [Array.length_toList]; omega),
          ← tok_bang_eq_toList tokens lo0 (by omega), h_kt]
        rfl
      have h_b2 := recentrydeep_balanced tokens (lo0 + 1) kv (by omega) (by omega) h_bk
      have h_b3 : flowBracketBalance tokens kv (kv + 1) = 0 := by
        rw [flowBracketBalance_single tokens kv (by rw [Array.length_toList]; omega),
          ← tok_bang_eq_toList tokens kv (by omega), h_vt]
        rfl
      have h_b4 := recentrydeep_balanced tokens (kv + 1) m (by omega) (by omega) h_bv
      have h_b5 : flowBracketBalance tokens m (m + 1) = 0 := by
        rw [flowBracketBalance_single tokens m (by rw [Array.length_toList]; omega),
          ← tok_bang_eq_toList tokens m (by omega), h_m_fe]
        rfl
      have h_d0_m1 : flowBracketBalance tokens lo0 (m + 1) = 0 := by
        have c1 := flowBracketBalance_compose tokens lo0 (lo0 + 1) kv (by omega) (by omega)
        have c2 := flowBracketBalance_compose tokens lo0 kv (kv + 1) (by omega) (by omega)
        have c3 := flowBracketBalance_compose tokens lo0 (kv + 1) m (by omega) (by omega)
        have c4 := flowBracketBalance_compose tokens lo0 m (m + 1) (by omega) (by omega)
        omega
      rcases Nat.lt_trichotomy k m with h_k_lt_m | h_k_eq_m | h_m_lt_k
      · -- inside the first pair (same dispatch as the single case, with `e := m` and the
        -- `.flowEntry` marker)
        rcases Nat.eq_or_lt_of_le h_lo0_k with h_eq | h_k_gt
        · exact Or.inl ⟨h_eq ▸ h_kt, kv, m, by omega, by omega, by omega, h_vt, by
            rw [← h_eq]; exact h_bk, h_bv, Or.inr h_m_fe⟩
        · rcases Nat.lt_trichotomy k kv with h_k_bk | h_k_kv | h_kv_k
          · rcases Nat.eq_or_lt_of_le (show lo0 + 1 ≤ k from by omega) with h_head | h_inside
            · exact Or.inr (Or.inr (Or.inr ⟨kv, by omega, by omega, h_head ▸ h_bk⟩))
            · exfalso
              have := recentrydeep_interior_pos tokens (lo0 + 1) kv k (by omega) (by omega)
                h_bk h_inside h_k_bk
              have h_c := flowBracketBalance_compose tokens lo0 (lo0 + 1) k (by omega) (by omega)
              omega
          · exact Or.inr (Or.inl ⟨h_k_kv ▸ h_vt, m, by omega, by omega, by
              rw [h_k_kv]; exact h_bv, Or.inr h_m_fe⟩)
          · rcases Nat.eq_or_lt_of_le (show kv + 1 ≤ k from by omega) with h_head | h_inside
            · exact Or.inr (Or.inr (Or.inr ⟨m, by omega, by omega, h_head ▸ h_bv⟩))
            · exfalso
              have := recentrydeep_interior_pos tokens (kv + 1) m k (by omega) (by omega)
                h_bv h_inside h_k_lt_m
              have h_c1 := flowBracketBalance_compose tokens lo0 (lo0 + 1) kv (by omega) (by omega)
              have h_c2 := flowBracketBalance_compose tokens lo0 kv (kv + 1) (by omega) (by omega)
              have h_c3 := flowBracketBalance_compose tokens lo0 (kv + 1) k (by omega) (by omega)
              omega
      · -- at the separator: the next pair's head follows
        subst h_k_eq_m
        rcases recmapbodydeep_window_split tokens (k + 1) hi0 (by omega) h_hi0_sz h_rest with
          h_pair' | ⟨m', h_m1_m', h_m'_hi0, h_m'_fe, h_pair', h_rest'⟩
        · have h_rest_w := recmapbodydeep_width_pos tokens (k + 1) hi0 (by omega) h_hi0_sz h_rest
          obtain ⟨kv', h1, h2, h_kt', _, _, _⟩ :=
            recmappairdeep_window_descent tokens (k + 1) hi0 h_rest_w h_hi0_sz h_pair'
          exact Or.inr (Or.inr (Or.inl ⟨h_m_fe, by omega, h_kt'⟩))
        · obtain ⟨kv', h1, h2, h_kt', _, _, _⟩ :=
            recmappairdeep_window_descent tokens (k + 1) m' h_m1_m' (by omega) h_pair'
          exact Or.inr (Or.inr (Or.inl ⟨h_m_fe, by omega, h_kt'⟩))
      · -- past the separator: recurse into the rest (re-based depth `0`)
        have h_k_d0' : flowBracketBalance tokens (m + 1) k = 0 := by
          have h_c := flowBracketBalance_compose tokens lo0 (m + 1) k (by omega) (by omega)
          omega
        have h_out := IH (hi0 - (m + 1)) (by omega) (m + 1) hi0 (Nat.le_refl _) h_hi0_sz
          h_rest k (by omega) h_k_hi0 h_k_d0'
        -- the payload windows all live in `[m+1, hi0) ⊆ [lo0, hi0)`; re-package verbatim
        exact h_out

/-- The head token of a deep entry is a flow content-start. -/
lemma recentrydeep_head_contentStart (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h_ab : a ≤ b) (h_b_sz : b ≤ tokens.size)
    (h_e : RecEntryDeep ((tokens.toList.take b).drop a)) :
    isFlowContentStart tokens[a]!.val := by
  unfold isFlowContentStart
  exact recentrydeep_head_shapes tokens a b h_ab h_b_sz h_e

/-- **Per-window `MapBodyProps` directly from the deep body** — no carrier, no lifted ∀-`j`
    bracket-`succ` primitives: every field is read off the classified pair structure, with each
    bracket's successor pinned to its OWN stored close. -/
lemma mapBodyProps_of_recmapbodydeep (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (h_hi_sz : hi ≤ tokens.size)
    (h_close : tokens[hi]!.val = .flowMappingEnd)
    (h_body : RecMapBodyDeep ((tokens.toList.take hi).drop lo)) :
    MapBodyProps tokens lo hi := by
  have h_lo_hi : lo < hi := by
    rcases Nat.lt_or_ge lo hi with h_lt | h
    · exact h_lt
    exfalso
    have h_len : ((tokens.toList.take hi).drop lo).length = 0 := by
      rw [List.length_drop, List.length_take, Array.length_toList]
      omega
    generalize h_shape : (tokens.toList.take hi).drop lo = l at h_body h_len
    cases h_body with
    | single p h_ne _ _ =>
      exact h_ne (List.length_eq_zero_iff.mp h_len)
    | cons p fe rest h_ne _ _ _ _ =>
      rw [List.length_append, List.length_cons] at h_len
      have := List.length_pos_iff.mpr h_ne
      omega
  have classify := recmapbodydeep_depth0_classify tokens (hi - lo) lo hi (Nat.le_refl _)
    h_hi_sz h_body
  -- M1: the body head is the first pair's `.key`.
  have h_m1 : lo < hi → tokens[lo]!.val = .key := by
    intro _
    rcases recmapbodydeep_window_split tokens lo hi (by omega) h_hi_sz h_body with
      h_pair | ⟨m, h_lo_m, h_m_hi, _, h_pair, _⟩
    · obtain ⟨kv, _, _, h_kt, _, _, _⟩ :=
        recmappairdeep_window_descent tokens lo hi h_lo_hi h_hi_sz h_pair
      exact h_kt
    · obtain ⟨kv, _, _, h_kt, _, _, _⟩ :=
        recmappairdeep_window_descent tokens lo m h_lo_m (by omega) h_pair
      exact h_kt
  refine ⟨h_m1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- M2 after_fe
    intro k hk1 hk2 h_d0 h_fe
    rcases classify k hk1 hk2 h_d0 with
      ⟨h_tok, _⟩ | ⟨h_tok, _⟩ | ⟨_, h_lt, h_key⟩ | ⟨b, h_kb, h_b_hi, h_blk⟩
    · rw [h_fe] at h_tok; cases h_tok
    · rw [h_fe] at h_tok; cases h_tok
    · exact ⟨by omega, h_key⟩
    · rcases recentrydeep_head_shapes tokens k b (by omega) (by omega) h_blk with
        ⟨c, s, h_sc⟩ | h_op | h_op
      · rw [h_fe] at h_sc; cases h_sc
      · rw [h_fe] at h_op; cases h_op
      · rw [h_fe] at h_op; cases h_op
  · -- M3 key_content
    intro k hk1 hk2 h_d0 h_key
    rcases classify k hk1 hk2 h_d0 with
      ⟨_, kv, e, h_k_kv, h_kv_e, h_e_hi, _, h_bk, _, _⟩ | ⟨h_tok, _⟩
      | ⟨h_tok, _, _⟩ | ⟨b, h_kb, h_b_hi, h_blk⟩
    · have h_w := recentrydeep_width_pos tokens (k + 1) kv (by omega) (by omega) h_bk
      exact ⟨by omega, recentrydeep_head_contentStart tokens (k + 1) kv (by omega) (by omega) h_bk⟩
    · rw [h_key] at h_tok; cases h_tok
    · rw [h_key] at h_tok; cases h_tok
    · rcases recentrydeep_head_shapes tokens k b (by omega) (by omega) h_blk with
        ⟨c, s, h_sc⟩ | h_op | h_op
      · rw [h_key] at h_sc; cases h_sc
      · rw [h_key] at h_op; cases h_op
      · rw [h_key] at h_op; cases h_op
  · -- M4 key_scalar_value
    intro k hk1 hk2 h_d0 h_key h_sc1
    rcases classify k hk1 hk2 h_d0 with
      ⟨_, kv, e, h_k_kv, h_kv_e, h_e_hi, h_vt, h_bk, _, _⟩ | ⟨h_tok, _⟩
      | ⟨h_tok, _, _⟩ | ⟨b, h_kb, h_b_hi, h_blk⟩
    · rcases recentrydeep_window_cases tokens (k + 1) kv (by omega) (by omega) h_bk with
        ⟨h_kv_eq, c, s, _⟩ | ⟨_, h_op, _⟩ | ⟨_, h_op, _⟩ | ⟨_, h_op, _, _⟩ | ⟨_, h_op, _, _⟩
      · refine ⟨by omega, ?_⟩
        rw [show k + 2 = kv by omega]
        exact h_vt
      all_goals
        obtain ⟨c, s, h_sc⟩ := h_sc1
        rw [h_op] at h_sc
        cases h_sc
    · rw [h_key] at h_tok; cases h_tok
    · rw [h_key] at h_tok; cases h_tok
    · rcases recentrydeep_head_shapes tokens k b (by omega) (by omega) h_blk with
        ⟨c, s, h_sc⟩ | h_op | h_op
      · rw [h_key] at h_sc; cases h_sc
      · rw [h_key] at h_op; cases h_op
      · rw [h_key] at h_op; cases h_op
  · -- M5 key_bracket_value
    intro k hk1 hk2 h_d0 h_key h_br
    rcases classify k hk1 hk2 h_d0 with
      ⟨_, kv, e, h_k_kv, h_kv_e, h_e_hi, h_vt, h_bk, _, _⟩ | ⟨h_tok, _⟩
      | ⟨h_tok, _, _⟩ | ⟨b, h_kb, h_b_hi, h_blk⟩
    · rcases recentrydeep_window_cases tokens (k + 1) kv (by omega) (by omega) h_bk with
        ⟨_, c, s, h_sc⟩ | ⟨h_kv_eq, h_op, h_cl⟩ | ⟨h_kv_eq, h_op, h_cl⟩
        | ⟨h_gt, h_op, h_cl, h_int⟩ | ⟨h_gt, h_op, h_cl, h_int⟩
      · rcases h_br with h_op | h_op <;> (rw [h_op] at h_sc; cases h_sc)
      · -- empty `[ ]` key: own close at `k+2`, `.value` at `k+3 = kv`
        refine ⟨k + 2, by omega, by omega, Or.inl ⟨h_op, by
            rw [show k + 2 = k + 1 + 1 from rfl]; exact h_cl⟩, ?_, by omega, by
            rw [show k + 2 + 1 = kv by omega]; exact h_vt, ?_⟩
        · unfold flowBracketBalance
          rw [if_pos (Nat.le_refl _)]
        · intro p hp1 hp2
          have : p = k + 2 := by omega
          subst this
          unfold flowBracketBalance
          rw [if_pos (Nat.le_refl _)]
          decide
      · refine ⟨k + 2, by omega, by omega, Or.inr ⟨h_op, by
            rw [show k + 2 = k + 1 + 1 from rfl]; exact h_cl⟩, ?_, by omega, by
            rw [show k + 2 + 1 = kv by omega]; exact h_vt, ?_⟩
        · unfold flowBracketBalance
          rw [if_pos (Nat.le_refl _)]
        · intro p hp1 hp2
          have : p = k + 2 := by omega
          subst this
          unfold flowBracketBalance
          rw [if_pos (Nat.le_refl _)]
          decide
      · -- `[ interior ]` key: own close at `kv - 1`, interior balanced + floored
        obtain ⟨h_int_bal, h_int_floor⟩ := wellBracketed_slice_positional tokens (k + 2) (kv - 1)
          (by omega) (by omega) (RecSeqBodyDeep.toFlat h_int).toWellBracketed
        refine ⟨kv - 1, by omega, by omega, Or.inl ⟨h_op, h_cl⟩, h_int_bal, by omega, by
            rw [show kv - 1 + 1 = kv by omega]; exact h_vt, ?_⟩
        intro p hp1 hp2
        exact h_int_floor p hp1 hp2
      · obtain ⟨h_int_bal, h_int_floor⟩ := wellBracketed_slice_positional tokens (k + 2) (kv - 1)
          (by omega) (by omega) (RecMapBodyDeep.toFlat h_int).toWellBracketed
        refine ⟨kv - 1, by omega, by omega, Or.inr ⟨h_op, h_cl⟩, h_int_bal, by omega, by
            rw [show kv - 1 + 1 = kv by omega]; exact h_vt, ?_⟩
        intro p hp1 hp2
        exact h_int_floor p hp1 hp2
    · rw [h_key] at h_tok; cases h_tok
    · rw [h_key] at h_tok; cases h_tok
    · rcases recentrydeep_head_shapes tokens k b (by omega) (by omega) h_blk with
        ⟨c, s, h_sc⟩ | h_op | h_op
      · rw [h_key] at h_sc; cases h_sc
      · rw [h_key] at h_op; cases h_op
      · rw [h_key] at h_op; cases h_op
  · -- M6 value_content
    intro k hk1 hk2 h_d0 h_val
    rcases classify k hk1 hk2 h_d0 with
      ⟨h_tok, _⟩ | ⟨_, e, h_k_e, h_e_hi, h_bv, _⟩ | ⟨h_tok, _, _⟩ | ⟨b, h_kb, h_b_hi, h_blk⟩
    · rw [h_val] at h_tok; cases h_tok
    · have h_w := recentrydeep_width_pos tokens (k + 1) e (by omega) (by omega) h_bv
      exact ⟨by omega, recentrydeep_head_contentStart tokens (k + 1) e (by omega) (by omega) h_bv⟩
    · rw [h_val] at h_tok; cases h_tok
    · rcases recentrydeep_head_shapes tokens k b (by omega) (by omega) h_blk with
        ⟨c, s, h_sc⟩ | h_op | h_op
      · rw [h_val] at h_sc; cases h_sc
      · rw [h_val] at h_op; cases h_op
      · rw [h_val] at h_op; cases h_op
  · -- M7 value_scalar_succ
    intro k hk1 hk2 h_d0 h_val h_sc1
    rcases classify k hk1 hk2 h_d0 with
      ⟨h_tok, _⟩ | ⟨_, e, h_k_e, h_e_hi, h_bv, h_marker⟩ | ⟨h_tok, _, _⟩
      | ⟨b, h_kb, h_b_hi, h_blk⟩
    · rw [h_val] at h_tok; cases h_tok
    · rcases recentrydeep_window_cases tokens (k + 1) e (by omega) (by omega) h_bv with
        ⟨h_e_eq, c, s, _⟩ | ⟨_, h_op, _⟩ | ⟨_, h_op, _⟩ | ⟨_, h_op, _, _⟩ | ⟨_, h_op, _, _⟩
      · refine ⟨by omega, ?_⟩
        rcases h_marker with h_e_hi' | h_fe
        · refine Or.inr ⟨?_, by omega⟩
          rw [show k + 2 = hi by omega]
          exact h_close
        · exact Or.inl (by rw [show k + 2 = e by omega]; exact h_fe)
      all_goals
        obtain ⟨c, s, h_sc⟩ := h_sc1
        rw [h_op] at h_sc
        cases h_sc
    · rw [h_val] at h_tok; cases h_tok
    · rcases recentrydeep_head_shapes tokens k b (by omega) (by omega) h_blk with
        ⟨c, s, h_sc⟩ | h_op | h_op
      · rw [h_val] at h_sc; cases h_sc
      · rw [h_val] at h_op; cases h_op
      · rw [h_val] at h_op; cases h_op
  · -- M8 value_bracket_succ
    intro k hk1 hk2 h_d0 h_val h_br
    rcases classify k hk1 hk2 h_d0 with
      ⟨h_tok, _⟩ | ⟨_, e, h_k_e, h_e_hi, h_bv, h_marker⟩ | ⟨h_tok, _, _⟩
      | ⟨b, h_kb, h_b_hi, h_blk⟩
    · rw [h_val] at h_tok; cases h_tok
    · have h_succ : e ≤ hi ∧ (tokens[e]!.val = .flowEntry ∨
          (tokens[e]!.val = .flowMappingEnd ∧ e = hi)) := by
        rcases h_marker with h_e_hi' | h_fe
        · exact ⟨by omega, Or.inr ⟨by rw [h_e_hi']; exact h_close, h_e_hi'⟩⟩
        · exact ⟨by omega, Or.inl h_fe⟩
      rcases recentrydeep_window_cases tokens (k + 1) e (by omega) (by omega) h_bv with
        ⟨_, c, s, h_sc⟩ | ⟨h_e_eq, h_op, h_cl⟩ | ⟨h_e_eq, h_op, h_cl⟩
        | ⟨h_gt, h_op, h_cl, h_int⟩ | ⟨h_gt, h_op, h_cl, h_int⟩
      · rcases h_br with h_op | h_op <;> (rw [h_op] at h_sc; cases h_sc)
      · refine ⟨k + 2, by omega, by omega, Or.inl ⟨h_op, by
            rw [show k + 2 = k + 1 + 1 from rfl]; exact h_cl⟩, ?_, by omega, by
            rw [show k + 2 + 1 = e by omega]; exact h_succ.2, ?_⟩
        · unfold flowBracketBalance
          rw [if_pos (Nat.le_refl _)]
        · intro p hp1 hp2
          have : p = k + 2 := by omega
          subst this
          unfold flowBracketBalance
          rw [if_pos (Nat.le_refl _)]
          decide
      · refine ⟨k + 2, by omega, by omega, Or.inr ⟨h_op, by
            rw [show k + 2 = k + 1 + 1 from rfl]; exact h_cl⟩, ?_, by omega, by
            rw [show k + 2 + 1 = e by omega]; exact h_succ.2, ?_⟩
        · unfold flowBracketBalance
          rw [if_pos (Nat.le_refl _)]
        · intro p hp1 hp2
          have : p = k + 2 := by omega
          subst this
          unfold flowBracketBalance
          rw [if_pos (Nat.le_refl _)]
          decide
      · obtain ⟨h_int_bal, h_int_floor⟩ := wellBracketed_slice_positional tokens (k + 2) (e - 1)
          (by omega) (by omega) (RecSeqBodyDeep.toFlat h_int).toWellBracketed
        refine ⟨e - 1, by omega, by omega, Or.inl ⟨h_op, h_cl⟩, h_int_bal, by omega, by
            rw [show e - 1 + 1 = e by omega]; exact h_succ.2, ?_⟩
        intro p hp1 hp2
        exact h_int_floor p hp1 hp2
      · obtain ⟨h_int_bal, h_int_floor⟩ := wellBracketed_slice_positional tokens (k + 2) (e - 1)
          (by omega) (by omega) (RecMapBodyDeep.toFlat h_int).toWellBracketed
        refine ⟨e - 1, by omega, by omega, Or.inr ⟨h_op, h_cl⟩, h_int_bal, by omega, by
            rw [show e - 1 + 1 = e by omega]; exact h_succ.2, ?_⟩
        intro p hp1 hp2
        exact h_int_floor p hp1 hp2
    · rw [h_val] at h_tok; cases h_tok
    · rcases recentrydeep_head_shapes tokens k b (by omega) (by omega) h_blk with
        ⟨c, s, h_sc⟩ | h_op | h_op
      · rw [h_val] at h_sc; cases h_sc
      · rw [h_val] at h_op; cases h_op
      · rw [h_val] at h_op; cases h_op
  · -- M9 bracket_seq
    intro k hk1 hk2 h_d0 h_op0
    rcases classify k hk1 hk2 h_d0 with
      ⟨h_tok, _⟩ | ⟨h_tok, _⟩ | ⟨h_tok, _, _⟩ | ⟨b, h_kb, h_b_hi, h_blk⟩
    · rw [h_op0] at h_tok; cases h_tok
    · rw [h_op0] at h_tok; cases h_tok
    · rw [h_op0] at h_tok; cases h_tok
    · rcases recentrydeep_window_cases tokens k b (by omega) (by omega) h_blk with
        ⟨_, c, s, h_sc⟩ | ⟨h_b_eq, h_op, h_cl⟩ | ⟨h_b_eq, h_op, h_cl⟩
        | ⟨h_gt, h_op, h_cl, h_int⟩ | ⟨h_gt, h_op, h_cl, h_int⟩
      · rw [h_op0] at h_sc; cases h_sc
      · refine ⟨k + 1, by omega, by omega, h_cl, ?_⟩
        unfold flowBracketBalance
        rw [if_pos (Nat.le_refl _)]
      · rw [h_op0] at h_op; cases h_op
      · obtain ⟨h_int_bal, _⟩ := wellBracketed_slice_positional tokens (k + 1) (b - 1)
          (by omega) (by omega) (RecSeqBodyDeep.toFlat h_int).toWellBracketed
        exact ⟨b - 1, by omega, by omega, h_cl, h_int_bal⟩
      · rw [h_op0] at h_op; cases h_op
  · -- M10 bracket_map
    intro k hk1 hk2 h_d0 h_op0
    rcases classify k hk1 hk2 h_d0 with
      ⟨h_tok, _⟩ | ⟨h_tok, _⟩ | ⟨h_tok, _, _⟩ | ⟨b, h_kb, h_b_hi, h_blk⟩
    · rw [h_op0] at h_tok; cases h_tok
    · rw [h_op0] at h_tok; cases h_tok
    · rw [h_op0] at h_tok; cases h_tok
    · rcases recentrydeep_window_cases tokens k b (by omega) (by omega) h_blk with
        ⟨_, c, s, h_sc⟩ | ⟨h_b_eq, h_op, h_cl⟩ | ⟨h_b_eq, h_op, h_cl⟩
        | ⟨h_gt, h_op, h_cl, h_int⟩ | ⟨h_gt, h_op, h_cl, h_int⟩
      · rw [h_op0] at h_sc; cases h_sc
      · rw [h_op0] at h_op; cases h_op
      · refine ⟨k + 1, by omega, by omega, h_cl, ?_⟩
        unfold flowBracketBalance
        rw [if_pos (Nat.le_refl _)]
      · rw [h_op0] at h_op; cases h_op
      · obtain ⟨h_int_bal, _⟩ := wellBracketed_slice_positional tokens (k + 1) (b - 1)
          (by omega) (by omega) (RecMapBodyDeep.toFlat h_int).toWellBracketed
        exact ⟨b - 1, by omega, by omega, h_cl, h_int_bal⟩

/-! ## §7 `FlowSubrangesOk` directly from the deep root

The `FlowSubrangesOk` fields ARE per-window `SeqBodyProps` / `MapBodyProps`, and with the joint
navigator every gated window has its deep body: the seq half assembles through the landed
windowed-`SafeBody` joint, the map half through the direct §6 producer.  No carrier, no six-fact
assembler. -/

lemma flowSubrangesOk_of_deep_nav (tokens : Array (Positioned YamlToken))
    (h_sz5 : tokens.size ≥ 5)
    (h_t0 : tokens[0]!.val = .streamStart)
    (h_tlast : tokens[tokens.size - 1]!.val = .streamEnd)
    (h_wt_outer : WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2))
    (h_nav : ∀ lo hi, DeepNavGate tokens 2 (tokens.size - 2) lo hi → DeepNavOut tokens lo hi) :
    FlowSubrangesOk tokens := by
  constructor
  · -- seq windows
    intro lo hi h_lo_hi h_hi_sz h_close h_bal h_open h_dyck
    rcases Nat.eq_or_lt_of_le h_lo_hi with h_eq | h_lt
    · exact seqBodyProps_empty tokens lo hi h_eq
    · have h_lo2 : 2 ≤ lo := by
        rcases Nat.lt_or_ge lo 2 with h | h
        · exfalso
          have h_lo1 : lo - 1 = 0 := by omega
          rw [h_lo1, h_t0] at h_open
          cases h_open
        · exact h
      have h_hi_le : hi ≤ tokens.size - 2 := by
        rcases Nat.lt_or_ge hi (tokens.size - 1) with h | h
        · omega
        · exfalso
          have h_hi_eq : hi = tokens.size - 1 := by omega
          rw [h_hi_eq, h_tlast] at h_close
          cases h_close
      have h_body := ((h_nav lo hi ⟨h_lo2, h_lt, h_hi_le, h_bal, h_dyck,
        Or.inl ⟨h_close, Or.inr h_open⟩⟩).1 h_close).toFlat
      have h_wt : WellTyped ((tokens.toList.take hi).drop lo) :=
        WellTyped_subrange tokens 2 lo hi (tokens.size - 2) h_lo2 h_lo_hi h_hi_le
          (by omega) h_wt_outer h_bal h_dyck
      have h_cs : isFlowContentStart tokens[lo]!.val := by
        obtain ⟨hl, hQ⟩ := h_body.toSafeBody.head_Q
        have h_lo_sz : lo < tokens.size := by omega
        have h_get : (((tokens.toList.take hi).drop lo)[0]'hl).val
            = (tokens[lo]'h_lo_sz).val := by
          rw [List.getElem_drop, List.getElem_take, Array.getElem_toList]
          congr 2
        rw [getElem!_pos tokens lo h_lo_sz, ← h_get]
        exact hQ
      exact seqBodyProps_of_windowed_safebody tokens lo hi (by omega) h_close h_bal h_dyck
        h_wt h_cs h_body.toSafeBody h_body.toSafeBodyUnit
  · -- map windows
    intro lo hi h_lo_hi h_hi_sz h_close h_bal h_open h_dyck
    rcases Nat.eq_or_lt_of_le h_lo_hi with h_eq | h_lt
    · exact mapBodyProps_empty tokens lo hi h_eq
    · have h_lo2 : 2 ≤ lo := by
        rcases Nat.lt_or_ge lo 2 with h | h
        · exfalso
          have h_lo1 : lo - 1 = 0 := by omega
          rw [h_lo1, h_t0] at h_open
          cases h_open
        · exact h
      have h_hi_le : hi ≤ tokens.size - 2 := by
        rcases Nat.lt_or_ge hi (tokens.size - 1) with h | h
        · omega
        · exfalso
          have h_hi_eq : hi = tokens.size - 1 := by omega
          rw [h_hi_eq, h_tlast] at h_close
          cases h_close
      have h_body := (h_nav lo hi ⟨h_lo2, h_lt, h_hi_le, h_bal, h_dyck,
        Or.inr ⟨h_close, Or.inr h_open⟩⟩).2 h_close
      exact mapBodyProps_of_recmapbodydeep tokens lo hi (by omega) h_close h_body

/-- `FlowSubrangesOk` from the SEQ-emission deep root (`[ … ]`): navigate the stored root
    `RecSeqBodyDeep`. -/
lemma flowSubrangesOk_of_deep_root (tokens : Array (Positioned YamlToken))
    (h_sz5 : tokens.size ≥ 5)
    (h_t0 : tokens[0]!.val = .streamStart)
    (h_tlast : tokens[tokens.size - 1]!.val = .streamEnd)
    (h_tpe : tokens[tokens.size - 2]!.val = .flowSequenceEnd)
    (h_wt_outer : WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2))
    (h_root : RecSeqBodyDeep ((tokens.toList.take (tokens.size - 2)).drop 2)) :
    FlowSubrangesOk tokens :=
  flowSubrangesOk_of_deep_nav tokens h_sz5 h_t0 h_tlast h_wt_outer
    ((deep_navigate_core tokens ((tokens.size - 2) - 2) 2 (tokens.size - 2)
      (Nat.le_refl _) (by omega)).1 h_root h_tpe)

/-- `FlowSubrangesOk` from the MAP-emission deep root (`{ … }`): navigate the stored root
    `RecMapBodyDeep` — the mirror wrapper `scanFiltered_emitMap_nonempty_structure`'s relocated
    consumer uses. -/
lemma flowSubrangesOk_of_deep_root_map (tokens : Array (Positioned YamlToken))
    (h_sz5 : tokens.size ≥ 5)
    (h_t0 : tokens[0]!.val = .streamStart)
    (h_tlast : tokens[tokens.size - 1]!.val = .streamEnd)
    (h_tpe : tokens[tokens.size - 2]!.val = .flowMappingEnd)
    (h_wt_outer : WellTyped ((tokens.toList.take (tokens.size - 2)).drop 2))
    (h_root : RecMapBodyDeep ((tokens.toList.take (tokens.size - 2)).drop 2)) :
    FlowSubrangesOk tokens :=
  flowSubrangesOk_of_deep_nav tokens h_sz5 h_t0 h_tlast h_wt_outer
    ((deep_navigate_core tokens ((tokens.size - 2) - 2) 2 (tokens.size - 2)
      (Nat.le_refl _) (by omega)).2 h_root h_tpe)

/-! ## §8 The deep MAP root seed

The `{ … }` mirror of §4: replay the open-brace → pair-body → close-brace chain, feeding the body
through `emitPairList_scans_recmapbodyDeep`. -/

lemma emitPairList_body_recmapbodyDeep
    (pairs : List (YamlValue × YamlValue)) (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansInFlowSavedKeyRecEntryDeep p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansInFlowRecEntryDeep p.2)
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
    ∧ RecMapBodyDeep ((s'.tokens.filter p).toList.drop old_sz) := by
  obtain ⟨n, s', block, h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, h_block_eq, h_wb, h_wt,
          h_rec, _h_oa, _h_sa, _h_n3⟩ :=
    emitPairList_scans_recmapbodyDeep pairs h_ne h_all_k h_all_v s rest h_corr h_flow h_fl
      h_indent h_col h_ek h_atol h_endline h_ska h_sync
  have h_drop : (s'.tokens.filter (fun t => t.val != .placeholder)).toList.drop
      (s.tokens.filter (fun t => t.val != .placeholder)).size = block := by
    rw [h_block_eq,
      show (s.tokens.filter (fun t => t.val != .placeholder)).size
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList.length
        from Array.length_toList.symm,
      List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
  refine ⟨n, s', h_chain.toScanChain, h_corr', h_fl', h_dp', h_ids', h_ek',
          h_col', h_inflow', h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, ?_⟩
  show RecMapBodyDeep ((s'.tokens.filter (fun t => t.val != .placeholder)).toList.drop
      (s.tokens.filter (fun t => t.val != .placeholder)).size)
  rw [h_drop]; exact h_rec

/-- **Deep map root seed** — `RecMapBodyDeep` of the root body window `[2, size-2)` off the map
    emission `"{" ++ emitPairList pairs ++ "}"`; the `{`-mirror of `seqRoot_recseqbodyDeep`. -/
lemma mapRoot_recmapbodydeep
    (pairs : Array (YamlValue × YamlValue)) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}") = .ok tokens)
    (h_ne : pairs.toList ≠ [])
    (h_all_k : ∀ p ∈ pairs.toList, EmitScansInFlowSavedKeyRecEntryDeep p.1)
    (h_all_v : ∀ p ∈ pairs.toList, EmitScansInFlowRecEntryDeep p.2) :
    RecMapBodyDeep ((tokens.toList.take (tokens.size - 2)).drop 2) := by
  let input := "{" ++ emit.emitPairList pairs.toList ++ "}"
  let p := fun (t : Positioned YamlToken) => t.val != .placeholder
  have h_toList : input.toList = '{' :: (emit.emitPairList pairs.toList).toList ++ ['}'] := by
    simp only [input, String.toList_append]; rfl
  -- Open brace → s₁
  obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
          h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, h_sk₁, h_filt₁,
          h_sync₁, h_ska₁, _h_ssv₁⟩ :=
    scanNextToken_flow_open_mapping_init input
      ((emit.emitPairList pairs.toList).toList ++ ['}']) h_toList
  -- Pair body → s₂ via the DEEP producer
  obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_inflow₂,
          h_indent₂, h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂, h_rec₂⟩ :=
    emitPairList_body_recmapbodyDeep pairs.toList h_ne h_all_k h_all_v s₁ ['}']
      h_corr₁ h_inflow₁ (by rw [h_fl₁]; omega) h_indent₁ (by rw [h_col₁]; omega)
      h_ek₁ (h_line₁ ▸ h_atol₁) h_endline₁ h_ska₁ h_sync₁
  -- Close brace → s₃
  obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃, h_ids₃, ⟨tok_fme, h_tok_fme_val, h_filt₃⟩⟩ :=
    scanNextToken_flow_close_mapping_outermost_ext s₂ h_corr₂ h_inflow₂ h_indent₂ h_col₂
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
    have ⟨h_pk, _⟩ := peek_of_chars_cons _ '{'
      ((emit.emitPairList pairs.toList).toList ++ ['}']) 0 h_corr
    rw [h_pk]; decide
  -- Indents chain
  have h_indents_small : s₃.indents.size ≤ 1 := by
    rw [h_ids₃, h_ids₂, h_ids₁]
    unfold ScannerState.emit ScannerState.mk'
    dsimp only []
    decide
  -- Token equation
  have h_tok_eq : Scanner.scanFiltered input =
      .ok ((s₃.emit .streamEnd).tokens.filter p) :=
    scanFiltered_tokens_eq_of_chain_short_stack input _ s₃ _ rfl h_no_bom
      h_chain_all h_eof h_fl₃ h_dp₃
      (ScanChain.fuel_bound _ _ _ _ rfl h_chain_all h_eof)
      h_indents_small
  have h_tokens_eq : tokens = (s₃.emit .streamEnd).tokens.filter p := by
    have : Scanner.scanFiltered input = .ok tokens := h_scan
    rw [h_tok_eq] at this; exact (Except.ok.inj this).symm
  have h_emit_se_tokens : (s₃.emit .streamEnd).tokens =
      s₃.tokens.push { pos := s₃.currentPos, val := .streamEnd } := by
    unfold ScannerState.emit; rfl
  have h_final_filter : (s₃.emit .streamEnd).tokens.filter p =
      (s₃.tokens.filter p).push { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_emit_se_tokens, Array.filter_push]; rfl
  have h_tokens_decomp : tokens = ((s₂.tokens.filter p).push tok_fme).push
      { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_tokens_eq, h_final_filter, h_filt₃]
  have h_filt₁_sz : (s₁.tokens.filter p).size = 2 := by
    have : ((s₁.tokens.filter p).map (·.val)).size = 2 := by rw [h_filt₁]; rfl
    simpa [Array.size_map] using this
  have h_tokens_sz_eq : tokens.size - 2 = (s₂.tokens.filter p).size := by
    rw [h_tokens_decomp]; simp [Array.size_push]
  have h_take_eq : tokens.toList.take (tokens.size - 2) = (s₂.tokens.filter p).toList := by
    have h_sz : tokens.size - 2 = (s₂.tokens.filter p).toList.length := by
      rw [h_tokens_sz_eq, Array.length_toList]
    rw [h_sz, h_tokens_decomp, Array.toList_push, Array.toList_push, List.append_assoc,
      List.take_left]
  rw [h_filt₁_sz] at h_rec₂
  rw [h_take_eq]
  exact h_rec₂

end L4YAML.Proofs.EmitterScannability
