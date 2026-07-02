/-!
# Reflection 378 — a prefix-length positional bridge is reusable for ANY structured element by
re-association; the feared "close bridge" is the separator bridge with a re-bracketed prefix

Self-contained core-Lean toy of L4YAML BRICK D's carved seq/seqEmpty CONS dispatch
(`nestedSeq_recseqentry_locate_seq_cons_step`).

A positional recursion already has a SEPARATOR bridge — "in `pre ++ x :: tail`, the token at index
`pre.length` is `x`."  Assembling the dispatch, a boundary-exclusion brick needs to read the CLOSE
`cl` of a head entry `op :: (interior ++ [cl])`.  That looks like a new "last-element bridge", but
re-associate `op :: (interior ++ [cl]) ++ rest = (op :: interior) ++ cl :: rest`: now `cl` is the
FIRST token past the `op :: interior` prefix, so the SAME separator bridge reads it with
`pre := op :: interior`.  One prefix-length bridge serves the head (prefix `[]`), the close
(prefix `op :: interior`), and the separator (prefix `op :: (interior ++ [cl])`) — the prefix
choice selects the token, because the bridge is BLIND to the prefix's contents.
-/

namespace Tests.Reflections.RebracketReusesPrefixBridge

set_option autoImplicit false

/-- **The single PREFIX-LENGTH positional bridge.**  In `pre ++ x :: tail`, the element at index
    `pre.length` is `x`.  It reads ONLY the prefix's LENGTH — never its contents — so re-associating
    a list to expose a different prefix re-aims the same lemma at a different token, for free. -/
theorem prefix_read {α : Type} (pre tail : List α) (x : α) :
    (pre ++ x :: tail)[pre.length]? = some x := by
  rw [List.getElem?_append_right (Nat.le_refl pre.length), Nat.sub_self]; rfl

/-- **Re-bracketing** a structured head block `op :: (interior ++ [cl]) ++ rest` exposes its CLOSE
    `cl` as the first token past the `op :: interior` prefix.  Pure `cons_append`/`append_assoc`. -/
theorem rebracket {α : Type} (op cl : α) (interior rest : List α) :
    (op :: (interior ++ [cl])) ++ rest = (op :: interior) ++ cl :: rest := by simp

/-! ## POSITIVE — ONE bridge reads the HEAD, the CLOSE, and the SEPARATOR of a CONS body. -/

/-- HEAD read: the bridge with the EMPTY prefix. -/
theorem read_head {α : Type} (op cl fe : α) (interior rest : List α) :
    ((op :: (interior ++ [cl])) ++ fe :: rest)[0]? = some op := by
  have h := prefix_read ([] : List α) ((interior ++ [cl]) ++ fe :: rest) op
  exact h

/-- CLOSE read with NO new bridge: re-bracket, then the bridge with `pre := op :: interior`. -/
theorem read_close {α : Type} (op cl fe : α) (interior rest : List α) :
    ((op :: (interior ++ [cl])) ++ fe :: rest)[(op :: interior).length]? = some cl := by
  rw [rebracket]
  exact prefix_read (op :: interior) (fe :: rest) cl

/-- SEPARATOR read: the SAME bridge with the FULL entry as prefix. -/
theorem read_sep {α : Type} (op cl fe : α) (interior rest : List α) :
    ((op :: (interior ++ [cl])) ++ fe :: rest)[(op :: (interior ++ [cl])).length]? = some fe :=
  prefix_read (op :: (interior ++ [cl])) rest fe

-- Concrete witness: op=0, interior=[1,2], cl=3, fe=9, rest=[4] ⇒ block = [0,1,2,3,9,4].
-- head@0 = 0;  close@(op::interior).length=3 = 3;  separator@entry.length=4 = 9.
#guard ([0, 1, 2, 3, 9, 4] : List Nat)[0]? == some 0    -- head
#guard ([0, 1, 2, 3, 9, 4] : List Nat)[3]? == some 3    -- close: (0 :: [1,2]).length = 3
#guard ([0, 1, 2, 3, 9, 4] : List Nat)[4]? == some 9    -- separator: [0,1,2,3].length = 4

/-! ## NEGATIVE — a token with NO structural boundary at its index needs the INNER decomposition. -/

/-- Block re-association exposes prefixes of length `0` (head), `(op::interior).length` (close), and
    `entry.length` (separator) — the STRUCTURAL boundaries.  A token strictly INSIDE `interior` sits
    at none of them: to read it the bridge needs a prefix of THAT length, which only `interior`'s OWN
    decomposition provides.  Re-associating the BLOCK alone never produces it — the bridge applies
    exactly where there is a boundary. -/
theorem read_interior_needs_inner {α : Type} (op i0 i1 : α) (irest rest : List α) :
    (op :: ((i0 :: i1 :: irest) ++ rest))[(op :: i0 :: ([] : List α)).length]? = some i1 := by
  -- prefix := [op, i0]; available ONLY because we decomposed interior = i0 :: i1 :: irest.
  have h := prefix_read (op :: i0 :: ([] : List α)) (irest ++ rest) i1
  exact h

-- The interior index 1 is NOT a block-level boundary {0, 3, 4} for [0,1,2,3,9,4]:
#guard !([0, 3, 4] : List Nat).contains 1

end Tests.Reflections.RebracketReusesPrefixBridge
