/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Reflection 245 — the producer's per-level assembler is the constructive dual of the consumer joint

Self-contained (core Lean, no `L4YAML` import) runnable demonstration of the principle in
Blueprint Reflection 245: when the consumer-side bridge that *reads* a recursive deliverable off a
positionally-windowed slice is already proven, its **write direction is a separate, immediately
landable brick** — the same positional-slicing lemma, run in the opposite direction, terminated by
the deliverable type's *constructor* instead of its *eliminator*.  Build it before the recursion: it
is the recursion's per-level final-assembly step, it reuses the consumer's slicing verbatim (no new
analysis), and it peels the non-recursive packaging off the deliverable, leaving the producer's
residual as *exactly* the recursive sub-deliverable.

The L4YAML instance: `seqBodyProps_of_located_entry` (R236, the consumer) *reads* a located
`RecSeqEntry` off the opener-window `(take (hi+1)).drop (lo-1)` to assemble `SeqBodyProps`;
`located_entry_of_recseqbody` (R245, the producer) *builds* that `RecSeqEntry` from the inner-window
`RecSeqBody ((take hi).drop lo)` — exactly the `SeqLocated.entry` the locate must deliver.  Both run
the same positional bridge (rest-decomposition `List.take_add_one` + `List.drop_append_of_le_length`,
opener-peel `List.getElem_cons_drop`); one descends via `seq_interior` (eliminator), the other
applies `RecSeqEntry.seq` (constructor).

This toy strips it to a skeleton over a one-kind bracket language (`os`/`cs` = `[`/`]`, `a` = atom):

* `RBody` / `REntry` — the recursive deliverable (toy `RecSeqBody` / `RecSeqEntry`): an entry is an
  atom or a `[ … ]` frame over a body; a body wraps one entry.
* `window_split`  — the shared positional bridge: the opener-window `(l.take (hi+1)).drop (lo-1)`
  equals `l[lo-1] :: ((l.take hi).drop lo ++ [l[hi]])`.  Proved by the take/drop slicing both
  directions run.  (Toy of `interior_window_eq`'s slice + the opener peel.)
* `readLocated`   — the CONSUMER (eliminator): from the located `REntry` of the opener-window, recover
  the inner-window `RBody`.  Toy `seqBodyProps_of_located_entry`'s core (`window_split` + `descent`).
* `buildLocated`  — the PRODUCER (constructor): from the inner-window `RBody`, build the located
  `REntry` of the opener-window.  Toy `located_entry_of_recseqbody` (`window_split` + `REntry.seq`).

`buildLocated` and `readLocated` are exact duals: same `window_split`, opposite direction, the
deliverable's constructor vs. its eliminator.  The producer reduces "produce the located entry" to
"produce the inner-window `RBody`" — the recursive obligation.  Positive witnesses build an entry and
read it back; the opener guard is load-bearing (a window whose `l[lo-1] ≠ .os` cannot be built).

Build: `lake build Tests.Reflections.ProducerDualOfConsumer`.
-/

namespace ProducerDualOfConsumer

/-- A tiny one-kind bracket language.  `os`/`cs` = square `[`/`]`, `a` = atom. -/
inductive Tok | os | cs | a
  deriving DecidableEq, Repr

/-- Append-singleton injectivity (core Lean, no Mathlib): from `a ++ [x] = b ++ [y]` recover both
    `a = b` and `x = y`.  The toy of `append_singleton_inj`, used by both directions. -/
theorem append_singleton_inj {a b : List Tok} {x y : Tok}
    (h : a ++ [x] = b ++ [y]) : a = b ∧ x = y := by
  have hr := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hr
  injection hr with hxy har
  exact ⟨List.reverse_inj.mp har, hxy⟩

/-! ## The recursive deliverable — `RBody` / `REntry` (toy `RecSeqBody` / `RecSeqEntry`) -/

mutual
  /-- A body wraps one entry (toy `RecSeqBody.single`; the comma/`flowEntry` recursion is elided —
      the nesting recursion runs through `REntry.seq`). -/
  inductive RBody : List Tok → Prop where
    | single (e : List Tok) (h : REntry e) : RBody e
  /-- An entry is an atom or a `[ … ]` frame over a recursive body (toy `RecSeqEntry.scalar`/`.seq`). -/
  inductive REntry : List Tok → Prop where
    | atom : REntry [.a]
    | seq (interior : List Tok) (h : RBody interior) : REntry (.os :: (interior ++ [.cs]))
end

/-! ## The shared positional bridge — `window_split` (the slice BOTH directions run) -/

/-- **The shared bridge.**  The opener-window `(l.take (hi+1)).drop (lo-1)` decomposes as
    `l[lo-1] :: ((l.take hi).drop lo ++ [l[hi]])`: the opener `l[lo-1]`, the inner window
    `(l.take hi).drop lo`, the closer `l[hi]`.  Pure take/drop slicing — the toy of the identity
    `interior_window_eq` (slice half) plus the opener peel, exactly what both `readLocated` (read it
    off) and `buildLocated` (assemble onto it) run, in opposite directions. -/
theorem window_split (l : List Tok) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi : hi < l.length) :
    (l.take (hi + 1)).drop (lo - 1)
      = l[lo - 1]'(by omega) :: ((l.take hi).drop lo ++ [l[hi]'h_hi]) := by
  -- rest-decomposition (mirrors `seqBodyProps_of_located_entry` / `located_entry_of_recseqbody`).
  have h_rest : (l.take (hi + 1)).drop lo
      = (l.take hi).drop lo ++ [l[hi]'h_hi] := by
    have h_ts : l.take (hi + 1) = l.take hi ++ [l[hi]'h_hi] := by
      rw [List.take_add_one, List.getElem?_eq_getElem h_hi]; rfl
    rw [h_ts]
    have h_len : lo ≤ (l.take hi).length := by rw [List.length_take]; omega
    rw [List.drop_append_of_le_length h_len]
  -- opener peel (mirrors the `List.getElem_cons_drop`, using `1 ≤ lo`).
  have h_peel : (l.take (hi + 1)).drop (lo - 1)
      = l[lo - 1]'(by omega) :: (l.take (hi + 1)).drop lo := by
    have hlen : lo - 1 < (l.take (hi + 1)).length := by rw [List.length_take]; omega
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take] at h
    rw [show lo - 1 + 1 = lo from by omega] at h
    exact h
  rw [h_peel, h_rest]

/-! ## The CONSUMER (eliminator) — `readLocated` (toy `seqBodyProps_of_located_entry`'s core) -/

/-- Single-level descent (toy `RecSeqEntry.seq_interior`): a located `REntry` whose shape is a `[ … ]`
    frame has a body interior.  The `atom` constructor is ruled out by the `.os` head. -/
theorem REntry.descent {e interior : List Tok} {cl : Tok}
    (h : REntry e) (h_eq : e = .os :: (interior ++ [cl])) : RBody interior := by
  cases h with
  | atom => injection h_eq with h1 _; exact absurd h1 (by decide)
  | seq interior' h' => injection h_eq with _h1 h2; exact (append_singleton_inj h2).1 ▸ h'

/-- **The consumer (eliminator direction).**  From the located `REntry` of the opener-window and the
    opener fact `l[lo-1] = .os`, *read off* the inner-window `RBody`.  It runs `window_split` to put
    the window in `.os :: (interior ++ [cl])` shape, then `REntry.descent` reads the interior.  Toy of
    `seqBodyProps_of_located_entry` (which then feeds `seqBodyProps_of_recseqbody_window`). -/
theorem readLocated (l : List Tok) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi : hi < l.length)
    (h_op : l[lo - 1]'(by omega) = .os)
    (h_entry : REntry ((l.take (hi + 1)).drop (lo - 1))) :
    RBody ((l.take hi).drop lo) := by
  rw [window_split l lo hi h_lo h_lo_hi h_hi, h_op] at h_entry
  exact REntry.descent h_entry rfl

/-! ## The PRODUCER (constructor) — `buildLocated` (toy `located_entry_of_recseqbody`) -/

/-- **The producer (constructor direction).**  The constructive *dual* of `readLocated`: from the
    inner-window `RBody` (the locate's recursive deliverable) and the opener/closer facts, *build* the
    located `REntry` of the opener-window — exactly the `SeqLocated.entry` field.  Same `window_split`,
    then `REntry.seq` (the constructor) where `readLocated` ran `REntry.descent` (the eliminator).
    Toy of `located_entry_of_recseqbody`. -/
theorem buildLocated (l : List Tok) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi : hi < l.length)
    (h_op : l[lo - 1]'(by omega) = .os) (h_cl : l[hi]'h_hi = .cs)
    (h_rec : RBody ((l.take hi).drop lo)) :
    REntry ((l.take (hi + 1)).drop (lo - 1)) := by
  rw [window_split l lo hi h_lo h_lo_hi h_hi, h_op, h_cl]
  exact REntry.seq _ h_rec

/-! ## Positive witnesses — build an entry, then read it back (constructor ∘ then ∘ eliminator) -/

/-- The inner body `[a]` for the window `[ a ]` (`l = [os, a, cs]`, `lo = 1`, `hi = 2`). -/
def rbody_a : RBody (([Tok.os, .a, .cs].take 2).drop 1) := by
  show RBody [.a]
  exact .single [.a] .atom

/-- The PRODUCER builds the located entry `REntry [os, a, cs]` from the inner body. -/
def built : REntry (([Tok.os, .a, .cs].take (2 + 1)).drop (1 - 1)) :=
  buildLocated [.os, .a, .cs] 1 2 (by omega) (by omega) (by decide) (by decide) (by decide) rbody_a

/-- ...and the CONSUMER reads the inner body back off it — the constructor/eliminator round-trip. -/
def read_back : RBody (([Tok.os, .a, .cs].take 2).drop 1) :=
  readLocated [.os, .a, .cs] 1 2 (by omega) (by omega) (by decide) (by decide) built

/-! ## The opener guard is load-bearing, and decidable balance sanity checks -/

/-- Count-based bracket balance (`[` `+1`, `]` `-1`, underflow → `none`), a decidable recognizer used
    only for the `#guard` witnesses below. -/
def bal (d0 : Option Nat) (l : List Tok) : Option Nat :=
  l.foldl (fun acc t => acc.bind (fun d =>
    match t with
    | .os => some (d + 1)
    | .cs => if d = 0 then none else some (d - 1)
    | .a  => some d)) d0

/-- The producer's opener guard `l[lo-1] = .os` is not free: an atom is not an opener, so a window
    whose front token is `.a` cannot be built into a `[ … ]` entry. -/
theorem opener_guard_load_bearing : (Tok.a = Tok.os) = False := by simp

-- Decidable sanity checks (fail the build if any witness drifts).
#guard decide (Tok.a = Tok.os) = false             -- the opener guard discriminates
#guard bal (some 0) [.os, .a, .cs] = some 0         -- the built window `[ a ]` is balanced
#guard bal (some 0) [.os, .a] = some 1              -- ...missing closer: ends at depth 1, not 0
#guard bal (some 0) [.a] = some 0                   -- the inner body `[a]` (an atom) is balanced
#guard bal (some 0) [.os, .os, .a, .cs, .cs] = some 0  -- a nested window `[ [ a ] ]` is balanced
#guard bal (some 0) [.cs, .os] = none               -- close-before-open underflows

end ProducerDualOfConsumer
