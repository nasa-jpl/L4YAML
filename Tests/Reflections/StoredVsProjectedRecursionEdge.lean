/-!
# Reflections 251 + 252 — stored-vs-projected severs the producer's recursion edge; the dependent twin's IH is dead

Self-contained core-Lean toy (no `L4YAML` import) for the principle: **a recursive-deliverable
inductive's STORAGE choices set the shape of the PRODUCER's recursion graph.**  A member that
*stores* its recursive sub-structure forces the producer's case to recurse; a sibling that
*projects* a flat invariant instead severs that edge, making the producer's case a pure leaf.

**R252 (the dependent twin, at the bottom of this file): in a storage-ordered producer family the
*base* member carries the only live self-recursion, and each *dependent* member consumes the base as
a black box and recurses on nothing of its own — so its induction hypothesis is entirely dead.**
Modelled by a second deliverable `KeyEntry e := Entry e ∧ bal e = 0` whose producer `buildKeyEntry`
is *non-recursive*: it routes the `Entry` part to the base `buildEntry` and the extra flat fact to
`bal_emit`, never calling itself.

Toy model:

* `Tok` — a token alphabet with a bracket-balance `bal` (the *flat* invariant).
* `Entry`/`Body` — the recursive deliverable (mirrors `RecSeqEntry`/`RecSeqBody`):
  - `Entry.seq` **stores** `Body interior` (a recursive premise) — the storing member;
  - `Entry.map` **projects**: its premise is only `bal interior = 0` (a flat, decidable fact),
    *not* a recursive `Body` — the projecting member.
* The producer side:
  - `mapLeaf` — a **non-recursive leaf builder** for the projecting member: it builds an `Entry`
    from a pure balance fact, *no recursion*.  There is deliberately **no** analogous `seqLeaf`,
    because `Entry.seq`'s premise is `Body interior`, not `bal interior = 0`.
  - `buildEntry`/`buildBody` — the full `Val → Entry (emit v)` producer: its `map` case is a
    **leaf** (calls the flat `bal_emitList`, never `buildBody`), its `seq` case **recurses** (calls
    `buildBody`).  The recursion graph is read straight off which premise each member stores.

Witnesses (positive *and* negative) of the severed edge:

* The projecting member accepts an interior with **no `Body`** — `Entry.map [] (by decide)` builds
  `Entry [om, cm]` from `bal [] = 0`, even though `Body []` is uninhabited (`not_body_nil`).
* The storing member needs a dedicated `seqEmpty` constructor precisely *because* `Body []` is
  uninhabited — another facet of the same asymmetry (`map` needs no `mapEmpty`; its flat premise
  already covers the empty interior).

Mutual-inductive gotchas observed elsewhere and respected here: no doc-comment immediately
before `mutual`; invert variable-indexed hypotheses with `cases` (never against a concrete
append-indexed list); prove projections by structural recursive calls inside `cases`, not
`induction`.
-/

namespace Tests.Reflections.StoredVsProjectedRecursionEdge

inductive Tok | a | os | cs | om | cm
  deriving DecidableEq, Repr

/-- Bracket delta of a token: openers `+1`, closers `-1`, atom `0`. -/
def tokDelta : Tok → Int
  | .os | .om => 1
  | .cs | .cm => -1
  | .a => 0

/-- Flat bracket balance — the *projected* invariant the `map` member stores. -/
def bal : List Tok → Int
  | [] => 0
  | t :: ts => tokDelta t + bal ts

theorem bal_append (a b : List Tok) : bal (a ++ b) = bal a + bal b := by
  induction a with
  | nil => simp [bal]
  | cons t ts ih => simp only [List.cons_append, bal, ih]; omega

/-- Source values, with collections carrying a `List Val` (the nested-inductive shape that makes
    the producer's recursion graph nontrivial). -/
inductive Val | a | seq (items : List Val) | map (items : List Val)

mutual
/-- Emit a value to tokens. -/
def emit : Val → List Tok
  | .a => [Tok.a]
  | .seq xs => Tok.os :: (emitList xs ++ [Tok.cs])
  | .map xs => Tok.om :: (emitList xs ++ [Tok.cm])
/-- Emit a list of values (the body). -/
def emitList : List Val → List Tok
  | [] => []
  | x :: xs => emit x ++ emitList xs
end

mutual
/-- Every emitted value is balanced — a *flat* induction, the substrate the `map` producer case
    leans on (and the proof that it can be a leaf). -/
theorem bal_emit (v : Val) : bal (emit v) = 0 := by
  cases v with
  | a => decide
  | seq xs => simp only [emit, bal, bal_append, bal_emitList xs]; decide
  | map xs => simp only [emit, bal, bal_append, bal_emitList xs]; decide
theorem bal_emitList (xs : List Val) : bal (emitList xs) = 0 := by
  cases xs with
  | nil => decide
  | cons x xs => simp only [emitList, bal_append, bal_emit x, bal_emitList xs]; omega
end

/-! ### The recursive deliverable: `seq` stores `Body`, `map` projects `bal` -/
mutual
inductive Body : List Tok → Prop where
  | single (e : List Tok) (h : Entry e) : Body e
  | cons (e rest : List Tok) (h : Entry e) (hr : Body rest) : Body (e ++ rest)
inductive Entry : List Tok → Prop where
  | atom : Entry [Tok.a]
  | seqEmpty : Entry [Tok.os, Tok.cs]
  /-- **Storing** member: premise is the recursive `Body interior`. -/
  | seq (interior : List Tok) (h : Body interior) :
      Entry (Tok.os :: (interior ++ [Tok.cs]))
  /-- **Projecting** member: premise is only the flat `bal interior = 0`. -/
  | map (interior : List Tok) (h : bal interior = 0) :
      Entry (Tok.om :: (interior ++ [Tok.cm]))
end

/-! ### The severed edge, at the builder level -/

/-- The **projecting** member has a flat *leaf* builder: from a pure balance fact, **no recursion**
    into `Entry`/`Body`.  (There is deliberately no `seqLeaf (bal interior = 0) → Entry (os :: …)` —
    `Entry.seq`'s premise is `Body interior`, the edge the storing member keeps.) -/
def mapLeaf (interior : List Tok) (h : bal interior = 0) :
    Entry (Tok.om :: (interior ++ [Tok.cm])) :=
  Entry.map interior h

/-! ### Negatives: no empty `Entry`/`Body` (so the storing member *needs* `seqEmpty`) -/

theorem entry_ne_nil (e : List Tok) (h : Entry e) : e ≠ [] := by
  cases h with
  | atom => simp
  | seqEmpty => simp
  | seq interior hb => simp
  | map interior hh => simp

theorem body_ne_nil (l : List Tok) (h : Body l) : l ≠ [] := by
  cases h with
  | single e he => exact entry_ne_nil _ he
  | cons e rest he hr =>
      cases e with
      | nil => exact absurd rfl (entry_ne_nil [] he)
      | cons c e' => simp

theorem not_entry_nil : ¬ Entry [] := fun h => entry_ne_nil [] h rfl
theorem not_body_nil : ¬ Body [] := fun h => body_ne_nil [] h rfl

/-! ### The full producer: `map` case is a leaf, `seq` case recurses

    The recursion graph is exactly: `buildEntry`'s `seq` case → `buildBody` (edge present, because
    `Entry.seq` stores `Body`); `buildEntry`'s `map` case → `bal_emitList` only (edge severed,
    because `Entry.map` projects `bal`).  A *keyed* twin producer would share `buildBody`, hence
    depend on `buildEntry` for its own `seq` case — the dependency ordering R251 reads off this graph. -/
mutual
def buildEntry : (v : Val) → Entry (emit v)
  | .a => Entry.atom
  | .seq [] => Entry.seqEmpty
  | .seq (x :: xs) => Entry.seq (emitList (x :: xs)) (buildBody (x :: xs) (by simp))
  | .map xs => Entry.map (emitList xs) (bal_emitList xs)        -- LEAF: no buildBody/buildEntry call
def buildBody : (xs : List Val) → xs ≠ [] → Body (emitList xs)
  | [], h => absurd rfl h
  | [x], _ => by
      have he : emitList [x] = emit x := by simp [emitList]
      rw [he]; exact Body.single (emit x) (buildEntry x)
  | x :: y :: xs, _ => by
      have he : emitList (x :: y :: xs) = emit x ++ emitList (y :: xs) := by simp [emitList]
      rw [he]
      exact Body.cons (emit x) (emitList (y :: xs)) (buildEntry x) (buildBody (y :: xs) (by simp))
end

/-! ### Decidable checks — fail the build if the model drifts -/

-- emit shapes
theorem emit_map_empty : emit (Val.map []) = [Tok.om, Tok.cm] := by decide
theorem emit_seq_empty : emit (Val.seq []) = [Tok.os, Tok.cs] := by decide
theorem emit_seq_one  : emit (Val.seq [Val.a]) = [Tok.os, Tok.a, Tok.cs] := by decide

-- flat balance: positive (map premise holds) and negative (unbalanced → map premise fails)
theorem bal_empty_zero : bal ([] : List Tok) = 0 := by decide
theorem bal_aa_zero    : bal [Tok.a, Tok.a] = 0 := by decide
theorem bal_om_nonzero : bal [Tok.om] ≠ 0 := by decide

-- POSITIVE: the projecting member builds from a flat fact, with NO `Body` for its interior
def built_map_empty : Entry [Tok.om, Tok.cm] := Entry.map [] (by decide)
def built_map_leaf  : Entry [Tok.om, Tok.a, Tok.a, Tok.cm] := mapLeaf [Tok.a, Tok.a] (by decide)

-- The storing member genuinely needs a recursive `Body` (here `Body.single … Entry.atom`) …
def built_seq_one   : Entry [Tok.os, Tok.a, Tok.cs] :=
  Entry.seq [Tok.a] (Body.single [Tok.a] Entry.atom)
-- … and a dedicated empty constructor, because `Body []` is uninhabited (`not_body_nil`).
def built_seq_empty : Entry [Tok.os, Tok.cs] := Entry.seqEmpty

#guard decide (emit (Val.map []) = [Tok.om, Tok.cm])
#guard decide (emit (Val.seq []) = [Tok.os, Tok.cs])
#guard decide (bal ([] : List Tok) = 0)         -- map's empty-interior premise holds …
#guard decide (bal [Tok.om] ≠ 0)                -- … but an unbalanced interior is rejected
-- (`Body []` is uninhabited — `not_body_nil` above — so the storing member has no empty interior.)

/-! ### Reflection 252 — the dependent twin's induction hypothesis is dead

`KeyEntry` is a *second* deliverable (the saved-key twin): the same recursive `Entry` PLUS one
extra flat fact (`bal e = 0`).  Its producer `buildKeyEntry` is the **dependent** member of the
storage-ordered family — and the point is that it does **not** recurse on itself.  It consumes the
**base** producer `buildEntry` as a black box (for the `Entry` part) and supplies the extra fact
flatly via `bal_emit`.  It is *literally non-recursive* (its body contains no `buildKeyEntry` call),
so an `induction`/`Val.rec` framing of it would leave the induction hypothesis entirely unused — the
"dead IH" of R252.  Contrast `buildEntry` above, whose `seq` case genuinely self-recurses through
`buildBody`: the base carries the family's only live self-recursion. -/

/-- The dependent deliverable: the recursive `Entry` plus one extra flat fact. -/
def KeyEntry (e : List Tok) : Prop := Entry e ∧ bal e = 0

/-- The dependent producer — non-recursive: `Entry` part from the BASE sibling `buildEntry`, the
    extra fact from the flat `bal_emit`.  No `buildKeyEntry` call in its own body ⇒ its IH is dead. -/
def buildKeyEntry (v : Val) : KeyEntry (emit v) := ⟨buildEntry v, bal_emit v⟩

-- POSITIVE: the dependent twin builds for every shape, with NO self-recursion …
def built_key_atom : KeyEntry [Tok.a]                 := buildKeyEntry Val.a
def built_key_seq  : KeyEntry [Tok.os, Tok.a, Tok.cs] := buildKeyEntry (Val.seq [Val.a])
def built_key_map  : KeyEntry [Tok.om, Tok.cm]        := buildKeyEntry (Val.map [])

-- … and projecting it back recovers exactly the base `Entry` (the dependent stores nothing new
-- structurally — only the extra flat fact, which holds on every emit block, fails on unbalanced).
def key_projects_to_entry : Entry [Tok.os, Tok.a, Tok.cs] := built_key_seq.1
#guard decide (bal (emit (Val.seq [Val.a])) = 0)   -- the extra fact holds on an emit block …
#guard decide (bal [Tok.os, Tok.a] ≠ 0)            -- … but not on an unbalanced one ⇒ no KeyEntry

end Tests.Reflections.StoredVsProjectedRecursionEdge
