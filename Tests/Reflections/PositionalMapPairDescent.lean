/-! # Reflection 509 — the value position is DETERMINED by the key-block length, not located

R508 ([[CrossFrameStructuralDescent]]) landed the LIST-level map→seq edge `recmappair_block_descent`:
a `RecMapPair` decomposes structurally as `key :: (block_k ++ value :: block_v)` with each block a
`RecSeqEntry`. R509 lands its first CONSUMER and the POSITIONAL dual: `recmappair_window_descent`,
the inverse of the build-UP lemma `recmappair_window`. Given a `RecMapPair` over a positional window
`(take m).drop lo`, it recovers the pair's own value-separator position `kv` and the two key/value
sub-windows as `RecSeqEntry`s — the navigator's map-pair *descend* step.

The decisive subtlety this demo isolates is SOUNDNESS. One might try to LOCATE the value separator by
scanning for the first `.value` token after the key — but that is UNSOUND: a key block can itself be a
nested map, so it carries its OWN `.value` token at depth `0` *relative to itself*. A first-`.value`
scan then mis-splits INSIDE the key block. The brick avoids this entirely: it reads `kv` off the
recovered `block_k` as `kv = lo + 1 + block_k.length` — the value position is DETERMINED by the
structural decomposition, never located by minimality. (This is the same soundness reason R508's doc
gives for bundling the nested-seq extract as an inner `∀` over the pair's OWN blocks rather than taking
an external split: the `block_k ++ value :: block_v` append does not split uniquely.)

This demo models the pair window abstractly (`Nat` "tokens", sentinel markers — no real tokens) and
shows the contrast on a concrete pair whose key block nests a `VALUE`:
* a naive first-`VALUE` scan mis-splits at the nested marker (`naive_firstValue`), so it DISAGREES
  with the determined position (`naive_unsound`) — minimality location would be unsound;
* the determined position `1 + |block_k|` recovers the key and value blocks positionally, both on the
  concrete pair (`key_recovered_ex`/`value_recovered_ex`) and for EVERY pair
  (`key_block_general`/`value_half_general`, the brick's `take_left` / `← drop_drop`+`drop_left` core).

The `decide` facts are fully axiom-free; the two general recoveries (and the bundled `demo`) use
`[propext]` only, through the `rw` of the core `List.take_left`/`List.drop_left` slicing lemmas — the
same profile as the real positional descents in the module.
-/

namespace PositionalMapPairDescent

/-- Sentinel "key" marker. -/
def KEY : Nat := 100
/-- Sentinel "value" marker. -/
def VALUE : Nat := 200

/-- A map-pair window `key :: (block_k ++ value :: block_v)` (mirrors a `RecMapPair`'s shape). -/
def pairList (block_k block_v : List Nat) : List Nat :=
  KEY :: (block_k ++ VALUE :: block_v)

-- ── (1) Determined, not located: read `kv` off the key block, never scan for it. ──

/-- A key block that ITSELF nests a `VALUE` (a nested-map key) — the case that breaks minimality. -/
def block_k_nested : List Nat := [VALUE, 7]
/-- The pair's value block. -/
def block_v_ex : List Nat := [9]
/-- The concrete pair `[KEY, VALUE, 7, VALUE, 9]`. -/
def p_ex : List Nat := pairList block_k_nested block_v_ex

theorem p_ex_unfold : p_ex = [KEY, VALUE, 7, VALUE, 9] := by decide

/-- A naive "first `VALUE` after the key" scan mis-splits: it lands at relative index 0 of the body —
    i.e. the `VALUE` INSIDE the key block, not the pair's separator. -/
theorem naive_firstValue : ((p_ex.drop 1).findIdx (· == VALUE)) = 0 := by decide

/-- The DETERMINED value position skips the whole key block: `1 + |block_k|` = 3. -/
theorem determined_pos : 1 + block_k_nested.length = 3 := by decide

theorem p_ex_at_determined : p_ex[1 + block_k_nested.length]? = some VALUE := by decide

/-- The naive scan and the determined position DISAGREE — locating the separator by minimality would
    be UNSOUND; reading it off `block_k.length` is the only correct choice. -/
theorem naive_unsound :
    (1 + ((p_ex.drop 1).findIdx (· == VALUE))) ≠ 1 + block_k_nested.length := by decide

-- ── (2) Positional recovery at the determined position (concrete). ──

theorem key_recovered_ex :
    (p_ex.drop 1).take block_k_nested.length = block_k_nested := by decide

theorem value_recovered_ex :
    p_ex.drop (1 + block_k_nested.length) = VALUE :: block_v_ex := by decide

-- ── (3) Positional recovery holds for ALL key/value blocks (the brick's `h_bk`/`h_drop_kv` core). ──

/-- Key block recovered: drop the key marker, take `|block_k|` (mirrors the brick's `take_left` slice). -/
theorem key_block_general (block_k block_v : List Nat) :
    ((pairList block_k block_v).drop 1).take block_k.length = block_k := by
  unfold pairList
  rw [List.drop_one, List.tail_cons, List.take_left]

/-- Value half recovered: drop `1 + |block_k|` lands exactly on the value marker (mirrors the brick's
    `← List.drop_drop` + `List.drop_left` peel) — the value position is `1 + |block_k|`, determined. -/
theorem value_half_general (block_k block_v : List Nat) :
    (pairList block_k block_v).drop (1 + block_k.length) = VALUE :: block_v := by
  unfold pairList
  rw [← List.drop_drop, List.drop_one, List.tail_cons, List.drop_left]

/-- The demo deliverable: the value separator's position is DETERMINED by `|block_k|` (read off the
    structural decomposition), not located by scanning — a naive first-`VALUE` scan mis-splits inside a
    nested key block (`naive_unsound`), while `1 + |block_k|` recovers the key and value blocks
    positionally for every pair (`key_block_general` ∧ `value_half_general`). This is exactly why
    `recmappair_window_descent` reads `kv` off `recmappair_block_descent`'s `block_k`, never by
    minimality. -/
theorem demo :
    ((1 + ((p_ex.drop 1).findIdx (· == VALUE))) ≠ 1 + block_k_nested.length)
    ∧ (∀ bk bv, ((pairList bk bv).drop 1).take bk.length = bk)
    ∧ (∀ bk bv, (pairList bk bv).drop (1 + bk.length) = VALUE :: bv) :=
  ⟨by decide, key_block_general, value_half_general⟩

end PositionalMapPairDescent
