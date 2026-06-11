/-
Reflection 372 — a slice→token positional bridge must transport its index arithmetic in the
proof-term-free Option `getElem?` (`l[i]?`), NOT the dependent `getElem` (`l[i]'h`).

The bridge fact is trivial ("the element at slice index `k` is the underlying element at `off + k`"),
but the obvious authoring — index the slice with the DEPENDENT `((l.take H).drop off)[k]'h_bound` form
and `rw` a structural list equation through it — fails with `motive is not type correct`, because the
bound proof `h_bound : k < ((l.take H).drop off).length` mentions the very list being rewritten, and
`fun a => a[k]'(… a …)` is ill-typed.

The fix: the Option-valued `l[i]?` carries NO proof argument, so `getElem?_drop` / `getElem?_take` /
`getElem?_append_right` are UNCONDITIONAL equations, freely `rw`-able.  Do the whole index transport in
`getElem?`, then cash out to `getElem` ONCE at the end via `getElem?_eq_getElem` + `Option.some.inj`.

Self-contained `Nat`-list toy (no project deps).  POSITIVE: the `getElem?` route closes both the head
bridge and the separator bridge.  NEGATIVE: the dependent-`getElem` attempt is shown (commented) to
reproduce the motive failure, and `#guard`s pin the concrete positional facts.
-/

namespace Tests.Reflections.SlicePositionalBridgeGetElemQ

set_option autoImplicit false

/-! ## POSITIVE — the head bridge via `getElem?`. -/

/-- The HEAD positional bridge: a slice `body = (l.take H).drop off` that opens with `x` puts `x` at
    underlying index `off`.  The toy of `nestedSeq_recseqentry_locate_head_pos` (the array-list
    `tokens[off]!` bridge is replaced by the pure list `l[off]?`, the only project-specific tail). -/
theorem head_bridge
    (l : List Nat) (body xs : List Nat) (x : Nat) (off H : Nat)
    (h_slice : body = (l.take H).drop off)
    (h_bound : off + body.length ≤ H)
    (h_cons : body = x :: xs) :
    l[off]? = some x := by
  have h_pos : 0 < body.length := by rw [h_cons]; simp
  have h_eq : (l.take H).drop off = x :: xs := by rw [← h_slice]; exact h_cons
  -- transport ENTIRELY in `getElem?` — every step an unconditional equation, no bound proof to poison.
  have hc : ((l.take H).drop off)[0]? = some x := by rw [h_eq]; rfl
  rw [List.getElem?_drop, List.getElem?_take, Nat.add_zero, if_pos (by omega : off < H)] at hc
  exact hc

/-! ## POSITIVE — the separator bridge via `getElem?`. -/

/-- The SEPARATOR positional bridge: in a slice decomposing as `e ++ fe :: rest`, the separator `fe`
    sits at underlying index `off + e.length`.  Toy of `nestedSeq_recseqentry_locate_sep_pos`. -/
theorem sep_bridge
    (l : List Nat) (body rest e : List Nat) (fe : Nat) (off H : Nat)
    (h_slice : body = (l.take H).drop off)
    (h_bound : off + body.length ≤ H)
    (h_prefix : body = e ++ fe :: rest) :
    l[off + e.length]? = some fe := by
  have h_blen : body.length = e.length + 1 + rest.length := by
    rw [h_prefix, List.length_append, List.length_cons]; omega
  have h_eq : (l.take H).drop off = e ++ fe :: rest := by rw [← h_slice]; exact h_prefix
  have hc : ((l.take H).drop off)[e.length]? = some fe := by
    rw [h_eq, List.getElem?_append_right (Nat.le_refl e.length), Nat.sub_self]; rfl
  rw [List.getElem?_drop, List.getElem?_take, if_pos (by omega : off + e.length < H)] at hc
  exact hc

/-! ## Cashing out `getElem?` → `getElem` in ONE final non-rewriting step. -/

/-- The end-of-proof conversion: once the index arithmetic is done in `getElem?`, recover the dependent
    `getElem` with `getElem?_eq_getElem` + `Option.some.inj` — no further `rw` through a dependent index,
    so no motive failure.  (In the real bridges this is followed by `getElem!_pos` + `←Array.getElem_toList`
    to reach `tokens[off]!`; the list-only toy stops at `l[off]`.) -/
theorem cash_out
    (l : List Nat) (off : Nat) (x : Nat) (h_len : off < l.length)
    (h_q : l[off]? = some x) :
    l[off]'h_len = x := by
  have := List.getElem?_eq_getElem h_len
  rw [h_q] at this
  exact (Option.some.inj this).symm

/-! ## NEGATIVE — the dependent-`getElem` route reproduces the motive failure (shown commented).

    The naive attempt below does NOT compile — uncommenting it yields
      `Tactic rewrite failed: motive is not type correct: fun a => a[0] = x`
    because `h_eq`'s LHS occurs inside the dependent bound proof of `((l.take H).drop off)[0]'_`:

    theorem head_bridge_BAD
        (l : List Nat) (body xs : List Nat) (x : Nat) (off H : Nat)
        (h_slice : body = (l.take H).drop off) (h_bound : off + body.length ≤ H)
        (h_cons : body = x :: xs) : l[off]? = some x := by
      have h_eq : (l.take H).drop off = x :: xs := by rw [← h_slice]; exact h_cons
      have hc : ((l.take H).drop off)[0]'(by rw [h_eq]; simp) = x := by
        rw [h_eq]   -- ← FAILS HERE: motive is not type correct
        rfl
      sorry
-/

/-! ## Concrete witnesses (`#guard`-backed) on `l = [10, 20, 30, 40, 50]`. -/

/-- The toy underlying list. -/
def L : List Nat := [10, 20, 30, 40, 50]

-- HEAD: the slice `[1, 4)` of `L` is `[20, 30, 40]`, opening with `20` at underlying index `1`.
#guard (L.take 4).drop 1 == [20, 30, 40]
#guard L[1]? == some 20

-- SEPARATOR: viewing the same slice as `e ++ fe :: rest` with `e = [20]` (length 1), the separator
-- `fe = 30` sits at underlying index `off + e.length = 1 + 1 = 2`.
#guard ([20] ++ 30 :: [40] : List Nat) == [20, 30, 40]
#guard L[1 + ([20] : List Nat).length]? == some 30

-- The transports are genuine arithmetic, not identities: the take/drop guard `off + k < H` is required
-- (here `2 < 4`), and out of range the option route correctly yields `none` (index `5 ≥ L.length`).
#guard decide (2 < 4)
#guard L[5]? == none

end Tests.Reflections.SlicePositionalBridgeGetElemQ
