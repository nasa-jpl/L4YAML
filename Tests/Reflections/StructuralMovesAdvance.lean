/-
# Reflection 262 — the locate recursion's three *structural moves* (descend + build + advance), the advance step being the positional lift of the body constructor

Self-contained, `L4YAML`-free runnable illustration of the proof-engineering principle in
Blueprint Reflection 262 (and memory `ref-structural-moves-complete-recursion`).

**The principle.** A recursion that produces a *recursive-deliverable* inductive (here a toy of
`RecSeqBody`/`RecSeqEntry`) is built from exactly **one positional move per way the deliverable's
constructors compose their argument**. For a body-of-entries deliverable there are two compositions,
giving three moves:

  - **DESCEND** — from a located *entry* of a nested bracket window, step one nesting level *into*
    its interior body (the entry constructor's `OB :: (interior ++ [CB])`, eliminator direction).
  - **BUILD** — from a recursively-established inner-window body, package the bracket window *as* an
    entry (the *same* composition, constructor direction — descend's dual).
  - **ADVANCE** — chain entries *along* the body: from a leading entry + a separator + a trailing
    body, produce the whole body (the body constructor's `e ++ fe :: rest`).

Once every constructor-composition has its positional lift landed (each a cheap, verified brick),
the recursion's residual collapses to the purely **analytical** part: *locating* the split points
the moves consume (the depth-`0` extent of a window's first entry and its trailing separator). That
analytical entry-boundary location is the genuine bulk; the structural moves are mechanical.

**A subsidiary point — projection-as-free-side-field.** The body constructor's `h_ne` / `h_head`
side-fields are *not* threaded obligations: they are free structural projections of the entry
(`REntry.ne_nil` / `REntry.head_cstart` below), so the ADVANCE assembler's caller supplies only the
located entry, the separator, and the recursive rest.

**The toy.** `REntry`/`RBody`: an entry is a scalar `[A]` or a nested bracket `OB :: (interior ++
[CB])` carrying `RBody interior`; a body is one entry (`single`) or an entry, a separator `FE`, and a
trailing body (`cons`). `recbody_of_entry` is DESCEND, `entry_of_recbody` is BUILD, `recbody_cons` is
ADVANCE (the lift of `RBody.cons`, discharging `h_ne`/`h_head` via the two projections). The positive
witnesses build and descend a *multi-entry* nested body `[OB, A, FE, A, CB]` using all three moves;
the negatives show an entry is never empty and never a bare separator.

(This toy keeps the list-append essence of the real `recseqbody_cons_window`; the real lemma adds the
array take/drop *window* identity `(take hi).drop lo = (take m).drop lo ++ tokens[m] :: (take
hi).drop (m+1)`, the `L4YAML`-specific positional plumbing the principle is otherwise agnostic to.)
-/

namespace Tests.Reflections.StructuralMovesAdvance

inductive Tok | A | OB | CB | FE
  deriving DecidableEq, Inhabited, Repr

/-- toy of `ContentStartTok`: the value of an entry's first token — a scalar `A` or an opener `OB`. -/
def CStart (t : Tok) : Prop := t = Tok.A ∨ t = Tok.OB

-- toy of `RecSeqBody` / `RecSeqEntry` (mutual; no `/--` directly before `mutual`, R234).  Unlike the
-- descend demo's body, `RBody` carries a real `cons` constructor (entry, `FE` separator, trailing
-- body) — the composition the ADVANCE move lifts.
mutual
  inductive RBody : List Tok → Prop where
    | single (e : List Tok) (h_ne : e ≠ []) (h_e : REntry e) (h_head : CStart (e.head h_ne)) :
        RBody e
    | cons (e : List Tok) (fe : Tok) (rest : List Tok) (h_ne : e ≠ [])
        (h_e : REntry e) (h_head : CStart (e.head h_ne)) (h_fe : fe = Tok.FE) (h_rest : RBody rest) :
        RBody (e ++ fe :: rest)
  inductive REntry : List Tok → Prop where
    | scalar : REntry [Tok.A]
    | seq (interior : List Tok) (h : RBody interior) : REntry (Tok.OB :: (interior ++ [Tok.CB]))
end

/-! ### The free side-field projections (`h_ne` / `h_head`) -/

/-- **An entry is non-empty** (toy of `RecSeqEntry.ne_nil`): every constructor yields a `cons` list. -/
theorem REntry.ne_nil {e : List Tok} (h : REntry e) : e ≠ [] := by
  cases h <;> simp

/-- **An entry's head is a content-start** (toy of `RecSeqEntry.head_contentStart`): a scalar head is
    `A`, a bracket head is `OB` — exactly the two `CStart` cases.  Threaded `h_ne` is proof-irrelevant
    for `List.head`. -/
theorem REntry.head_cstart {e : List Tok} (h : REntry e) (h_ne : e ≠ []) : CStart (e.head h_ne) := by
  cases h with
  | scalar => rw [List.head_cons]; exact Or.inl rfl
  | seq i hi => rw [List.head_cons]; exact Or.inr rfl

/-! ### The shared positional helper -/

/-- right-cancel a trailing singleton (toy of the project's `append_singleton_inj`). -/
theorem app_single_inj {α} {a b : List α} {c : α} (h : a ++ [c] = b ++ [c]) : a = b := by
  simpa using congrArg List.reverse h

/-! ### Move 1 — DESCEND (into a nested entry's interior) -/

/-- **DESCEND** (toy of `recseqbody_window_of_located_entry`): a bracket-shaped entry
    `OB :: (interior ++ [CB])` descends to its interior body — the navigation recursion's IH input one
    nesting level down.  (The `scalar` case is ruled out by the `OB` head.) -/
theorem recbody_of_entry {e interior : List Tok} (h : REntry e)
    (h_eq : e = Tok.OB :: (interior ++ [Tok.CB])) : RBody interior := by
  cases h with
  | scalar => exfalso; injection h_eq with h1 _; exact absurd h1 (by decide)
  | seq i hi => injection h_eq with _ h2; exact (app_single_inj h2) ▸ hi

/-! ### Move 2 — BUILD (an entry from its inner-window body) — descend's constructor-direction dual -/

/-- **BUILD** (toy of `located_entry_of_recseqbody`): package a recursively-established inner body as
    the bracket entry `OB :: (interior ++ [CB])`.  Descend's dual — same composition, constructor side. -/
theorem entry_of_recbody (interior : List Tok) (h : RBody interior) :
    REntry (Tok.OB :: (interior ++ [Tok.CB])) :=
  REntry.seq interior h

/-! ### Move 3 — ADVANCE (chain entries along the body) — the lift of `RBody.cons` (THIS reflection) -/

/-- **ADVANCE** (toy of `recseqbody_cons_window`): from a leading entry, a separator, and a trailing
    body, produce the whole body `e ++ FE :: rest`.  The `RBody.cons` side-fields `h_ne` / `h_head`
    are discharged by the two projections above, so the caller supplies only the entry, the separator
    (implicit `FE`), and the recursive rest — the third and last *structural* move. -/
theorem recbody_cons (e rest : List Tok) (h_e : REntry e) (h_rest : RBody rest) :
    RBody (e ++ Tok.FE :: rest) :=
  RBody.cons e Tok.FE rest (REntry.ne_nil h_e) h_e
    (REntry.head_cstart h_e (REntry.ne_nil h_e)) rfl h_rest

/-! ### Positive — all three moves compose to build and descend a *multi-entry* nested body -/

/-- a one-scalar body `[A]` (the `single` leaf). -/
def bodyA : RBody [Tok.A] :=
  RBody.single [Tok.A] (by simp) REntry.scalar (by rw [List.head_cons]; exact Or.inl rfl)

/-- ADVANCE builds the multi-entry body `[A, FE, A]` = `[A] ++ FE :: [A]` from two scalar entries. -/
def body_AFA : RBody [Tok.A, Tok.FE, Tok.A] :=
  recbody_cons [Tok.A] [Tok.A] REntry.scalar bodyA

/-- BUILD wraps that multi-entry body into the nested bracket entry `[OB, A, FE, A, CB]`. -/
def entry_AFA : REntry [Tok.OB, Tok.A, Tok.FE, Tok.A, Tok.CB] :=
  entry_of_recbody [Tok.A, Tok.FE, Tok.A] body_AFA

/-- DESCEND recovers the *multi-entry* interior `[A, FE, A]` from that entry — the recursion then
    processes it with ADVANCE, the moves composing as the recursion intends. -/
theorem descend_multi : RBody [Tok.A, Tok.FE, Tok.A] :=
  recbody_of_entry (interior := [Tok.A, Tok.FE, Tok.A]) entry_AFA rfl

/-- ADVANCE again: extend the nested entry into a still-larger body `[OB,A,FE,A,CB] ++ FE :: [A]`. -/
def body_full : RBody [Tok.OB, Tok.A, Tok.FE, Tok.A, Tok.CB, Tok.FE, Tok.A] :=
  recbody_cons [Tok.OB, Tok.A, Tok.FE, Tok.A, Tok.CB] [Tok.A] entry_AFA bodyA

/-! ### Negative — an entry is never empty and never a bare separator (so the moves never misfire) -/

theorem no_entry_empty : ¬ REntry ([] : List Tok) := by intro h; exact REntry.ne_nil h rfl

theorem no_entry_separator : ¬ REntry [Tok.FE] := by intro h; cases h

#guard ([Tok.A, Tok.FE, Tok.A] : List Tok).length == 3
#guard ([Tok.OB, Tok.A, Tok.FE, Tok.A, Tok.CB] : List Tok).length == 5
#guard ([Tok.OB, Tok.A, Tok.FE, Tok.A, Tok.CB, Tok.FE, Tok.A] : List Tok).length == 7

end Tests.Reflections.StructuralMovesAdvance
