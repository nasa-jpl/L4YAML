/-!
# Reflection 403 — a severed-edge constructor blocks PROJECTING an orthogonal field,
forcing it to be a STORED carrier threaded through every producer in the cluster.

When an orthogonal field `F` must be threaded through a recursive deliverable, the first
instinct is to PROJECT it (`Rec l → F l`), like the existing weak projections
(`toWellBracketed`, `toEntrySafe`).  But a **severed-edge** constructor — one that stores
only a WEAK summary of its interior, deliberately dropping the recursive structure (mirrors
`RecSeqEntry.map`, which stores only `WellBracketed interior`) — BLOCKS the projection: `F`
is not derivable from the weak summary.  And you cannot just add `F` to the constructor,
because its RECONSTRUCTION sites (where it is rebuilt from a located window that carries only
the weak summary) cannot supply `F` either.  So `F` must be a STORED field on the FLAT
producer's predicate, threaded through every producer in the cluster — never a projection.

The toy: `Rec.severed` stores only `WeakOk interior` (nonemptiness).  The weak field PROJECTS
(positive); the orthogonal field `Adj` does NOT — a `severed`-built entry can fail `Adj`
(negative), so no `Rec l → Adj l` projection exists.

R404 sharpens this: the BOUNDARY side-inputs `Adj`'s consumer needs (head/tail) DO project
through `severed` — they read the constructor SHAPE (non-leaf entries end in `cls`), not the
severed interior — so `rec_lastNotOpn` is a clean `cases`.  That is exactly why the producer
pre-staging (R401–R404) is possible: only the interior field needs threading, never its
boundary side-inputs.

R405 closes the arc constructively: since `Adj` cannot be projected, it is CO-PRODUCED —
threaded through the SAME recursion that assembles the deliverable, gluing each item's stored
`Adj` with the seam (`adj_append`, toy `OpenerAdj_seam`) and OUTPUTTING `Adj` alongside the body
(`coproduce_adj`).  One induction yields both; the orthogonal field rides the assembler, never a
projection of its result.
-/

namespace Tests.Reflections.SeveredEdgeBlocksProjection

set_option autoImplicit false

inductive Tok | opn | cls | content
  deriving DecidableEq, Repr

/-- The weak summary the severed edge stores: the interior is nonempty. -/
def WeakOk (l : List Tok) : Prop := l ≠ []

/-- The orthogonal field (toy `OpenerAdj`): every `opn` is immediately followed by `content`. -/
def Adj (l : List Tok) : Prop :=
  ∀ i, (h : i + 1 < l.length) → l[i]'(Nat.lt_of_succ_lt h) = Tok.opn → l[i + 1]'h = Tok.content

/-- A recursive deliverable with a SEVERED EDGE.  `wrap` stores the full recursion
    (`h : Rec body`); `severed` stores ONLY the weak summary `WeakOk interior` — the
    recursive structure of `interior` is dropped (the toy of `RecSeqEntry.map`). -/
inductive Rec : List Tok → Prop where
  | leaf : Rec [Tok.content]
  | wrap (body : List Tok) (h : Rec body) : Rec (Tok.opn :: (body ++ [Tok.cls]))
  | severed (interior : List Tok) (h : WeakOk interior) : Rec (Tok.opn :: (interior ++ [Tok.cls]))

/-- **POSITIVE — the WEAK field PROJECTS through every constructor, including `severed`.**
    The severed edge stores exactly enough for it, so `toNonempty` is a clean structural
    recursion (the mirror of `RecSeqEntry.toWellBracketed`). -/
theorem Rec.toNonempty : {l : List Tok} → Rec l → l ≠ []
  | _, .leaf => by decide
  | _, .wrap _ _ => by simp
  | _, .severed _ _ => by simp

/-- **NEGATIVE — the ORTHOGONAL field does NOT project.**  A `severed`-built entry whose
    interior is itself `[opn]` is a valid `Rec` (the weak summary `WeakOk [opn]` holds), yet
    the whole entry `[opn, opn, cls]` fails `Adj` (position 0 is `opn`, position 1 is `opn`,
    not `content`).  So there is no `Rec l → Adj l` projection — the severed edge genuinely
    lacks the information.  Hence `Adj` must be a STORED field on the flat producer's
    predicate, threaded through every producer, not derived from the deliverable. -/
theorem rec_severed_not_adj :
    Rec [Tok.opn, Tok.opn, Tok.cls] ∧ ¬ Adj [Tok.opn, Tok.opn, Tok.cls] := by
  refine ⟨Rec.severed [Tok.opn] (List.cons_ne_nil _ _), ?_⟩
  intro h
  exact absurd (h 0 (by decide) (by decide)) (by decide)

/-- **POSITIVE (R404) — the BOUNDARY fact PROJECTS through the severed edge.**  Although the
    orthogonal *interior* field `Adj` does not project (above), the boundary side-inputs its
    consumer needs — here "the last token is never an opener `opn`" — DO project through every
    constructor, `severed` included, because they read the constructor SHAPE (every non-leaf ends
    in `cls`; the leaf is `[content]`), never the severed interior.  This is the toy of
    `RecSeqBody.lastNonOpener`: the severed edge severs the *interior recursion*, not the *body
    boundary*, so the head/tail side-inputs the `OpenerAdj` wrap consumes are always recoverable —
    which is exactly why the pre-staging (R401–R404) is possible at all. -/
theorem rec_lastNotOpn : {l : List Tok} → Rec l → ∃ t, l.getLast? = some t ∧ t ≠ Tok.opn := by
  intro l h
  cases h with
  | leaf => exact ⟨Tok.content, by decide, by decide⟩
  | wrap body _ =>
      refine ⟨Tok.cls, ?_, by decide⟩
      rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_concat]
  | severed interior _ =>
      refine ⟨Tok.cls, ?_, by decide⟩
      rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_concat]

/-- **POSITIVE — `Adj` WOULD project if the severed edge stored it.**  When the interior's
    `Adj` is available (here as an explicit hypothesis standing in for a stored field), the
    wrap closes: `opn` head followed by the interior's head, which `Adj`+nonemptiness keep a
    `content`.  This is exactly why the field must be STORED (threaded) — supply it and the
    composition is routine; the only gap is the severed edge's missing datum. -/
theorem adj_wrap_if_stored (interior : List Tok)
    (h_ne : interior ≠ []) (h_head : interior[0]'(by
      cases interior with | nil => exact absurd rfl h_ne | cons _ _ => simp) = Tok.content)
    (h_int : Adj interior) :
    Adj (Tok.opn :: interior) := by
  intro i h hopn
  match i with
  | 0 => simpa using h_head
  | k + 1 =>
    have hk : k + 1 < interior.length := by simpa using h
    have := h_int k hk (by simpa using hopn)
    simpa using this

/-- The toy `OpenerAdj_append`/seam: concatenating two `Adj` blocks preserves `Adj`, given the
    left block's last token is not an opener (`opn`).  Mirrors `OpenerAdj_append`/`OpenerAdj_seam`:
    inside `a` and inside `b` the field is local; the only boundary is `a`'s last token, discharged
    by the tail bridge. -/
theorem adj_append (a b : List Tok) (ha : Adj a) (hb : Adj b)
    (h_tail : ∀ (h : 0 < a.length), a[a.length - 1]'(Nat.sub_lt h Nat.one_pos) ≠ Tok.opn) :
    Adj (a ++ b) := by
  intro i hi hopn
  rcases Nat.lt_or_ge (i + 1) a.length with h1 | _
  · have ek : (a ++ b)[i]'(Nat.lt_of_succ_lt hi) = a[i]'(by omega) := List.getElem_append_left (by omega)
    have ek1 : (a ++ b)[i + 1]'hi = a[i + 1]'h1 := List.getElem_append_left h1
    rw [ek1]; rw [ek] at hopn; exact ha i h1 hopn
  · rcases Nat.lt_or_ge i a.length with hia | _
    · exfalso
      have hlast : i = a.length - 1 := by omega
      have ek : (a ++ b)[i]'(Nat.lt_of_succ_lt hi) = a[i]'hia := List.getElem_append_left hia
      rw [ek] at hopn
      have hidx : a[a.length - 1]'(Nat.sub_lt (by omega) Nat.one_pos) = a[i]'hia := by
        congr 1; omega
      exact h_tail (by omega) (hidx.trans hopn)
    · obtain ⟨m, rfl⟩ : ∃ m, i = a.length + m := ⟨i - a.length, by omega⟩
      have hb1 : m + 1 < b.length := by rw [List.length_append] at hi; omega
      have ek : (a ++ b)[a.length + m]'(Nat.lt_of_succ_lt hi) = b[m]'(by omega) := by
        rw [List.getElem_append_right (by omega)]; congr 1; omega
      have ek1 : (a ++ b)[a.length + m + 1]'hi = b[m + 1]'hb1 := by
        rw [List.getElem_append_right (by omega)]; congr 1; omega
      rw [ek1]; rw [ek] at hopn; exact hb m hb1 hopn

/-- The tail bridge's append law (toy `lastNonOpener_append_right`): `a ++ b` ends with `b`'s last
    token, so a non-opener tail on the non-empty `b` lifts to the concatenation. -/
theorem tail_append_right (a b : List Tok) (hb : 0 < b.length)
    (h : b[b.length - 1]'(Nat.sub_lt hb Nat.one_pos) ≠ Tok.opn) :
    ∀ (h0 : 0 < (a ++ b).length),
      (a ++ b)[(a ++ b).length - 1]'(Nat.sub_lt h0 Nat.one_pos) ≠ Tok.opn := by
  intro h0
  have hlen : (a ++ b).length = a.length + b.length := List.length_append
  have ek : (a ++ b)[(a ++ b).length - 1]'(Nat.sub_lt h0 Nat.one_pos)
      = b[b.length - 1]'(Nat.sub_lt hb Nat.one_pos) := by
    rw [List.getElem_append_right (by omega)]; congr 1; omega
  rw [ek]; exact h

/-- **POSITIVE (R405) — CO-PRODUCTION.**  `Adj` does NOT project off the deliverable
    (`rec_severed_not_adj`), but it is CO-PRODUCED by threading it through the SAME recursion that
    concatenates the per-item blocks: each block carries its own `Adj` + non-opener tail (its
    STORED fields), and the running body's `Adj` is folded with the seam `adj_append`, OUTPUTTING
    `Adj` *alongside* the deliverable (here the flattened body) rather than projecting it.  The fold
    also outputs the running tail — the seam's left side-condition — exactly as the real
    `emitList_scans_recseqbody` was strengthened to output `OpenerAdj` (via `OpenerAdj_seam`) next to
    `RecSeqBody`, its per-item tail supplied by each entry's `EntryUnit`.  One induction yields both
    the deliverable and the orthogonal field; projection is impossible, co-production is routine. -/
theorem coproduce_adj : (blocks : List (List Tok)) →
    (∀ b ∈ blocks, b ≠ [] ∧ Adj b ∧
      (∀ (h : 0 < b.length), b[b.length - 1]'(Nat.sub_lt h Nat.one_pos) ≠ Tok.opn)) →
    Adj blocks.flatten ∧
      (∀ (h0 : 0 < blocks.flatten.length),
        blocks.flatten[blocks.flatten.length - 1]'(Nat.sub_lt h0 Nat.one_pos) ≠ Tok.opn)
  | [], _ => ⟨by intro i h; simp at h, by intro h; simp at h⟩
  | [b], hall => by
      obtain ⟨_, h_adj, h_tail⟩ := hall b (by simp)
      simpa using ⟨h_adj, h_tail⟩
  | b :: c :: rest, hall => by
      obtain ⟨_, h_b_adj, h_b_tail⟩ := hall b (by simp)
      obtain ⟨h_rest_adj, h_rest_tail⟩ :=
        coproduce_adj (c :: rest) (fun x hx => hall x (by simp [hx]))
      have h_cne : c ≠ [] := (hall c (by simp)).1
      have h_rest_ne : 0 < (c :: rest).flatten.length := by
        cases c with
        | nil => exact absurd rfl h_cne
        | cons _ _ => simp [List.flatten]
      have h_flat : (b :: c :: rest).flatten = b ++ (c :: rest).flatten := by
        simp [List.flatten]
      rw [h_flat]
      exact ⟨adj_append b _ h_b_adj h_rest_adj h_b_tail,
             tail_append_right b _ h_rest_ne (h_rest_tail h_rest_ne)⟩

-- The severed witness `[opn, opn, cls]` has an `opn` at position 1 (so it fails `Adj`).
#guard ([Tok.opn, Tok.opn, Tok.cls][1]? == some Tok.opn)
-- a `wrap`/`leaf` path that DOES satisfy Adj, for contrast: `[opn, content, cls]`.
#guard ([Tok.opn, Tok.content, Tok.cls][1]? == some Tok.content)
-- R404 boundary fact: the severed witness ends in `cls` (a close), never an opener — so the
-- tail-not-opener side-input projects even through the severed edge that defeats `Adj`.
#guard ([Tok.opn, Tok.opn, Tok.cls].getLast? == some Tok.cls)
-- R405 co-production: a body assembled from per-item Adj blocks (each ending in a non-opener)
-- flattens to a body that still ends in a non-opener `content` — the running tail `coproduce_adj`
-- threads as the seam's left side-condition.
#guard ([[Tok.opn, Tok.content], [Tok.content]].flatten.getLast? == some Tok.content)

end Tests.Reflections.SeveredEdgeBlocksProjection
