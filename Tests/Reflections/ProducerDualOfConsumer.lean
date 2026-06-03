/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Reflections 245 + 246 + 247 — the producer-dual of a consumer joint, its non-verbatim symmetric mirror, and the bundle assembler that lifts a field-level dual to the consumer's bundled deliverable

Self-contained (core Lean, no `L4YAML` import) runnable demonstration of three paired principles.

**Reflection 245** — when the consumer-side bridge that *reads* a recursive deliverable off a
positionally-windowed slice is already proven, its **write direction is a separate, immediately
landable brick**: the same positional-slicing lemma, run in the opposite direction, terminated by
the deliverable type's *constructor* instead of its *eliminator*.  It is the recursion's per-level
final-assembly step, it reuses the consumer's slicing verbatim, and it peels the non-recursive
packaging off the deliverable, leaving the producer's residual as *exactly* the recursive
sub-deliverable.

**Reflection 246** — the *symmetric mirror* of such a producer-dual (the same construction on the
other half of an additive parallel-type pair) transports the **positional plumbing verbatim**, but
its **terminal constructor call is *not* verbatim**: it sheds (or adds) exactly the fields the
parallel type chose to *store* vs. *project*.  Read the parallel type's constructor signature first —
its arity differs from the sibling's by precisely the stored-vs-projected split (R244).

**Reflection 247** — a producer-dual reduces one *field*, but the consumer joint demands a *bundle*.
The field-level dual (R245/R246) produces only the recursive `entry` field, yet the locate consumer
joint consumes a whole `SeqLocated`/`MapLocated` *bundle*.  Close the arity gap with a trivial
**bundle assembler** whose only non-pass-through field is the recursive one: the other fields are
window-guard pass-throughs (`pos`/`dyck`/`wt`), so the bundle's residual collapses to *exactly* the
recursive field.  It is the producer-side mirror of "universal packaging is its own joint" (R243).
And the map mirror is *not* as clean: the bundled type stores extra primitives the entry producer
does not supply, so the map bundle assembler threads them as further hypotheses — R246's storage
asymmetry reappearing one level up, at the bundle's field count.

The L4YAML instance.  `seqBodyProps_of_located_entry` / `mapBodyProps_of_located_entry` (the
consumers) *read* a located `RecSeqEntry`/`RecMapEntry` off the opener-window `(take (hi+1)).drop
(lo-1)`; `located_entry_of_recseqbody` / `located_mapentry_of_recmapbody` (the producers, R245/R246)
*build* them from the inner-window `RecSeqBody`/`RecMapBody`.  All four run the *same* positional
bridge (rest-decomposition `List.take_add_one` + `List.drop_append_of_le_length`, opener-peel
`List.getElem_cons_drop`).  The asymmetry R246 names: `RecSeqEntry.seq` **stores** a `WellBracketed
interior` field, so the seq producer ends `RecSeqEntry.seq _ _ _ h_op h_cl h_rec.toWellBracketed
h_rec` (the projection fed in); `RecMapEntry.map` (R242's additive type) stores only `RecMapBody`
and **projects** its balance via `RecMapEntry.toWellBracketed` (R244), so the map producer ends
`RecMapEntry.map _ _ _ h_op h_cl h_rec` — one argument shorter, the `WellBracketed` shed.

This toy strips it to a skeleton over a two-kind bracket language (`os`/`cs` = `[`/`]` for the
sequence side, `om`/`cm` = `{`/`}` for the mapping side, `a` = atom):

* `WB`                           — a shallow "matching outer frame, or atom" marker: the toy
  `WellBracketed`, the property one family STORES and the other PROJECTS.
* `SBody` / `SEntry`             — the seq-side deliverable (toy `RecSeqBody`/`RecSeqEntry`); the
  `seq` constructor **stores** a `WB interior` field.
* `MBody` / `MEntry`            — the map-side deliverable (toy `RecMapBody`/`RecMapEntry`, R242's
  additive type); the `map` constructor stores **no** `WB` — `MEntry.toWB` recovers it post-hoc.
* `window_split`                 — the shared, *kind-agnostic* positional bridge: the opener-window
  `(l.take (hi+1)).drop (lo-1)` equals `l[lo-1] :: ((l.take hi).drop lo ++ [l[hi]])`.  BOTH families,
  BOTH directions run it verbatim (R245/R246's "positional plumbing transports verbatim").
* `readLocatedSeq`               — the CONSUMER (eliminator): `window_split` + `SEntry.descent`.
* `buildLocatedSeq`              — the PRODUCER, seq side: `window_split` + `SEntry.seq` — and it must
  **feed** the stored `WB` via `SBody.toWB h_rec` (the extra argument).
* `buildLocatedMap`              — the PRODUCER, map side: `window_split` + `MEntry.map` — the
  constructor call is the seq one minus the `WB` argument (R246's shed field).
* `SLocated` / `MLocated`        — the bundled deliverables (toy `SeqLocated`/`MapLocated`): the
  recursive `entry` field PLUS cheap pass-through fields (`posF`/`wtF` = window guards).  `MLocated`
  additionally STORES `keyF`, a pair-interior primitive the entry producer does not supply.
* `bundleLocatedSeq`             — the BUNDLE assembler, seq side (toy `seqLocated_of_recseqbody`,
  R247): `⟨h_lo, h_lo_hi, buildLocatedSeq …⟩` — only `entry` is non-trivial; the rest are guards.
* `bundleLocatedMap`             — the BUNDLE assembler, map side (toy `mapLocated_of_recmapbody`):
  the same packaging but with **one extra hypothesis** `h_key` for the stored `keyF` — R247/R246's
  storage asymmetry made visible as a bundle-level arity bump over the seq side.
* `mlocated_key` / `mlocated_entry` (R248) — the storage asymmetry is **scale-free**: the *same*
  projected-vs-stored mechanism that *shrinks* the entry constructor (`MEntry.map` sheds `WB`,
  recovered post-hoc by `wb_recovered`) *grows* the bundle assembler (`MLocated` stores `keyF`,
  threaded in as `h_key`).  `mlocated_key` projects the grown-in `keyF` back out; opposite signs, one
  mechanism.  (The toy cannot reproduce R248's *axiom*-ledger half — both toy builds are choice-free
  — but the arity half is exactly these witnesses.)

Positive witnesses build an entry on each side and read the seq one back; `MEntry.toWB` recovers the
`WB` the map constructor never stored.  The opener *kind* is load-bearing (a `{` window is not a `[`
window, an atom is neither); decidable `bal` checks pin the balanced/unbalanced witnesses.

Build: `lake build Tests.Reflections.ProducerDualOfConsumer`.
-/

namespace ProducerDualOfConsumer

/-- A tiny two-kind bracket language.  `os`/`cs` = square `[`/`]` (sequence), `om`/`cm` = curly
    `{`/`}` (mapping), `a` = atom. -/
inductive Tok | os | cs | om | cm | a
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

/-! ## The shared property `WB` — what one family STORES and the other PROJECTS (toy `WellBracketed`) -/

/-- A shallow "matching outer frame, or atom" marker — the toy `WellBracketed`.  This is the property
    the seq entry constructor *stores* as a field and the map entry constructor *omits and projects*;
    R246 is about exactly this storage decision becoming visible at the constructor's arity. -/
inductive WB : List Tok → Prop where
  | atom : WB [.a]
  | frame (op cl : Tok) (inner : List Tok) : WB (op :: (inner ++ [cl]))

/-! ## The two recursive deliverables — seq side STORES `WB`, map side PROJECTS it -/

mutual
  /-- Seq-side body wraps one entry (toy `RecSeqBody.single`). -/
  inductive SBody : List Tok → Prop where
    | single (e : List Tok) (h : SEntry e) : SBody e
  /-- Seq-side entry: an atom or a `[ … ]` frame.  **`seq` STORES `WB interior`** — the faithful toy
      of `RecSeqEntry.seq`, whose `WellBracketed interior` field the seq producer must supply. -/
  inductive SEntry : List Tok → Prop where
    | atom : SEntry [.a]
    | seq (interior : List Tok) (hwb : WB interior) (h : SBody interior) :
        SEntry (.os :: (interior ++ [.cs]))
end

mutual
  /-- Map-side body wraps one entry (toy `RecMapBody.single`). -/
  inductive MBody : List Tok → Prop where
    | single (e : List Tok) (h : MEntry e) : MBody e
  /-- Map-side entry: an atom or a `{ … }` frame.  **`map` STORES NO `WB`** — the faithful toy of
      R242's `RecMapEntry.map`, which keeps only `RecMapBody` and projects its balance post-hoc. -/
  inductive MEntry : List Tok → Prop where
    | atom : MEntry [.a]
    | map (interior : List Tok) (h : MBody interior) :
        MEntry (.om :: (interior ++ [.cm]))
end

/-! ## Projections to `WB` — the seq build FEEDS one, the map build RECOVERS one -/

/-- The seq entry's stored `WB` is recoverable structurally (one-liner over the shallow marker). -/
theorem SEntry.toWB {e : List Tok} (h : SEntry e) : WB e := by
  cases h with
  | atom => exact WB.atom
  | seq interior hwb h => exact WB.frame .os .cs interior

/-- …hence the seq body projects to `WB` — this is what `buildLocatedSeq` feeds into the stored field. -/
theorem SBody.toWB {e : List Tok} (h : SBody e) : WB e := by
  cases h with
  | single e he => exact he.toWB

/-- The map entry's `WB` is recovered **post-hoc** (the toy `RecMapEntry.toWellBracketed`, R244): the
    `map` constructor never stored it, so downstream consumers obtain it by projection, not by field. -/
theorem MEntry.toWB {e : List Tok} (h : MEntry e) : WB e := by
  cases h with
  | atom => exact WB.atom
  | map interior h => exact WB.frame .om .cm interior

/-! ## The shared positional bridge — `window_split` (kind-agnostic; BOTH families, BOTH directions) -/

/-- **The shared bridge.**  The opener-window `(l.take (hi+1)).drop (lo-1)` decomposes as
    `l[lo-1] :: ((l.take hi).drop lo ++ [l[hi]])`.  Pure take/drop slicing — note it mentions **no**
    bracket kind, so the seq and map families, and the read and build directions, all run it
    verbatim.  Toy of `interior_window_eq`'s slice plus the opener peel: the plumbing R245/R246 say
    transports identically across the mirror. -/
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

/-! ## The CONSUMER (eliminator) — `readLocatedSeq` (toy `seqBodyProps_of_located_entry`'s core) -/

/-- Single-level seq descent (toy `RecSeqEntry.seq_interior`): a located `SEntry` whose shape is a
    `[ … ]` frame has a body interior.  The `atom` constructor is ruled out by the `.os` head. -/
theorem SEntry.descent {e interior : List Tok} {cl : Tok}
    (h : SEntry e) (h_eq : e = .os :: (interior ++ [cl])) : SBody interior := by
  cases h with
  | atom => injection h_eq with h1 _; exact absurd h1 (by decide)
  | seq interior' hwb h' => injection h_eq with _h1 h2; exact (append_singleton_inj h2).1 ▸ h'

/-- **The consumer (eliminator direction).**  From the located `SEntry` of the opener-window and the
    opener fact `l[lo-1] = .os`, *read off* the inner-window `SBody`: `window_split` puts the window in
    `.os :: (interior ++ [cl])` shape, then `SEntry.descent` reads the interior. -/
theorem readLocatedSeq (l : List Tok) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi : hi < l.length)
    (h_op : l[lo - 1]'(by omega) = .os)
    (h_entry : SEntry ((l.take (hi + 1)).drop (lo - 1))) :
    SBody ((l.take hi).drop lo) := by
  rw [window_split l lo hi h_lo h_lo_hi h_hi, h_op] at h_entry
  exact SEntry.descent h_entry rfl

/-! ## The PRODUCER (constructor) — the dual (R245), and its non-verbatim mirror (R246) -/

/-- **The producer, SEQ side** (toy `located_entry_of_recseqbody`).  The constructive *dual* of
    `readLocatedSeq`: same `window_split`, terminated by the `SEntry.seq` *constructor*.  Because
    `SEntry.seq` **stores** a `WB interior` field, the build must **feed** it — `SBody.toWB h_rec` is
    the extra argument the map side will shed. -/
theorem buildLocatedSeq (l : List Tok) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi : hi < l.length)
    (h_op : l[lo - 1]'(by omega) = .os) (h_cl : l[hi]'h_hi = .cs)
    (h_rec : SBody ((l.take hi).drop lo)) :
    SEntry ((l.take (hi + 1)).drop (lo - 1)) := by
  rw [window_split l lo hi h_lo h_lo_hi h_hi, h_op, h_cl]
  exact SEntry.seq _ (SBody.toWB h_rec) h_rec

/-- **The producer, MAP side** (toy `located_mapentry_of_recmapbody`).  The *symmetric mirror* of
    `buildLocatedSeq`: the `window_split` plumbing is **verbatim** (only the kinds `.os`/`.cs` →
    `.om`/`.cm` change), but the terminal constructor call is **one argument shorter** — `MEntry.map`
    stores no `WB`, so there is no `SBody.toWB`-style argument to feed.  R246 in one diff: the mirror
    sheds exactly the field the parallel type chose to project rather than store. -/
theorem buildLocatedMap (l : List Tok) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi : hi < l.length)
    (h_op : l[lo - 1]'(by omega) = .om) (h_cl : l[hi]'h_hi = .cm)
    (h_rec : MBody ((l.take hi).drop lo)) :
    MEntry ((l.take (hi + 1)).drop (lo - 1)) := by
  rw [window_split l lo hi h_lo h_lo_hi h_hi, h_op, h_cl]
  exact MEntry.map _ h_rec

/-! ## Positive witnesses — build on each side; read the seq one back; project the map one's `WB` -/

/-- Seq inner body `[a]` for the window `[ a ]` (`l = [os, a, cs]`, `lo = 1`, `hi = 2`). -/
def sbody_a : SBody (([Tok.os, .a, .cs].take 2).drop 1) := by
  show SBody [.a]
  exact .single [.a] .atom

/-- The seq PRODUCER builds the located entry `SEntry [os, a, cs]`, **feeding** the stored `WB`. -/
def built_seq : SEntry (([Tok.os, .a, .cs].take (2 + 1)).drop (1 - 1)) :=
  buildLocatedSeq [.os, .a, .cs] 1 2 (by omega) (by omega) (by decide) (by decide) (by decide) sbody_a

/-- …and the seq CONSUMER reads the inner body back off it — the constructor/eliminator round-trip. -/
def read_back_seq : SBody (([Tok.os, .a, .cs].take 2).drop 1) :=
  readLocatedSeq [.os, .a, .cs] 1 2 (by omega) (by omega) (by decide) (by decide) built_seq

/-- Map inner body `[a]` for the window `{ a }` (`l = [om, a, cm]`, `lo = 1`, `hi = 2`). -/
def mbody_a : MBody (([Tok.om, .a, .cm].take 2).drop 1) := by
  show MBody [.a]
  exact .single [.a] .atom

/-- The map PRODUCER builds the located entry `MEntry [om, a, cm]` — the constructor call **shed** the
    `WB` argument the seq build supplied (R246). -/
def built_map : MEntry (([Tok.om, .a, .cm].take (2 + 1)).drop (1 - 1)) :=
  buildLocatedMap [.om, .a, .cm] 1 2 (by omega) (by omega) (by decide) (by decide) (by decide) mbody_a

/-- …yet the `WB` the `map` constructor never stored is recovered **post-hoc** by projection — exactly
    `RecMapEntry.toWellBracketed`.  This is *why* the field can be shed at construction (R244/R246). -/
def wb_recovered : WB (([Tok.om, .a, .cm].take (2 + 1)).drop (1 - 1)) :=
  MEntry.toWB built_map

/-! ## The BUNDLE assembler (R247) — lift the field-level dual to the consumer's bundled deliverable -/

/-- **Toy `SeqLocated`** — the bundled deliverable the locate consumer joint actually consumes.  Three
    fields: two cheap window-guard **pass-throughs** (`posF`/`wtF`, toy `pos`/`wt`/`dyck`) and the one
    recursive field `entry`.  The whole point of R247 is that only `entry` is non-trivial. -/
structure SLocated (l : List Tok) (lo hi : Nat) : Prop where
  posF : 1 ≤ lo
  wtF  : lo ≤ hi
  entry : SEntry ((l.take (hi + 1)).drop (lo - 1))

/-- **The bundle assembler, SEQ side** (toy `seqLocated_of_recseqbody`, R247).  Pure packaging: the
    recursive `entry` via the field-level dual `buildLocatedSeq`, the other two fields as direct
    window-guard pass-throughs.  Every hypothesis except `h_rec` is a guard, so the bundle's residual
    is *exactly* the recursive sub-deliverable `SBody` — the producer-side mirror of R243. -/
theorem bundleLocatedSeq (l : List Tok) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi : hi < l.length)
    (h_op : l[lo - 1]'(by omega) = .os) (h_cl : l[hi]'h_hi = .cs)
    (h_rec : SBody ((l.take hi).drop lo)) :
    SLocated l lo hi :=
  ⟨h_lo, h_lo_hi, buildLocatedSeq l lo hi h_lo h_lo_hi h_hi h_op h_cl h_rec⟩

/-- **Toy `MapLocated`** — the map-side bundle, which STORES an extra pair-interior primitive `keyF`
    the entry producer `buildLocatedMap` does **not** supply.  This is R247's named asymmetry: the
    bundled type stores more than the entry assembler delivers, so the map bundle's arity must exceed
    the seq bundle's by exactly the projected-not-produced primitive. -/
structure MLocated (l : List Tok) (lo hi : Nat) : Prop where
  posF : 1 ≤ lo
  wtF  : lo ≤ hi
  keyF : hi ≤ l.length
  entry : MEntry ((l.take (hi + 1)).drop (lo - 1))

/-- **The bundle assembler, MAP side** (toy `mapLocated_of_recmapbody`).  The same packaging as
    `bundleLocatedSeq`, but it must **thread one extra hypothesis** `h_key` for the stored `keyF` — the
    entry producer `buildLocatedMap` supplies no such field.  Compare the signatures: this lemma has
    one more argument than `bundleLocatedSeq`, and that argument is exactly the field R247 says the
    bundled map type stores but the entry assembler does not produce (R246's storage split, one
    structural level up). -/
theorem bundleLocatedMap (l : List Tok) (lo hi : Nat)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo ≤ hi) (h_hi : hi < l.length)
    (h_op : l[lo - 1]'(by omega) = .om) (h_cl : l[hi]'h_hi = .cm)
    (h_key : hi ≤ l.length)
    (h_rec : MBody ((l.take hi).drop lo)) :
    MLocated l lo hi :=
  ⟨h_lo, h_lo_hi, h_key, buildLocatedMap l lo hi h_lo h_lo_hi h_hi h_op h_cl h_rec⟩

/-- The seq BUNDLE: every cheap field is `by omega`/`by decide`, only the last argument (`sbody_a`) is
    a real deliverable — the witness encodes "only the recursive field is non-trivial." -/
def slocated_a : SLocated [.os, .a, .cs] 1 2 :=
  bundleLocatedSeq [.os, .a, .cs] 1 2 (by omega) (by omega) (by decide) (by decide) (by decide) sbody_a

/-- The recursive field is the meat: projecting `entry` back out recovers exactly the located entry
    `buildLocatedSeq` produced. -/
def slocated_entry : SEntry (([Tok.os, .a, .cs].take (2 + 1)).drop (1 - 1)) := slocated_a.entry

/-- The map BUNDLE: note the **extra** `(by decide)` for `h_key` — one argument more than the seq
    bundle, the bundle-level arity bump R247 names (the stored pair primitive the entry producer
    doesn't supply). -/
def mlocated_a : MLocated [.om, .a, .cm] 1 2 :=
  bundleLocatedMap [.om, .a, .cm] 1 2 (by omega) (by omega) (by decide) (by decide) (by decide) (by decide) mbody_a

/-! ## R248 — the storage asymmetry is *scale-free*: SHRINK at the entry constructor, GROWTH at the
    bundle, one projected-vs-stored mechanism with opposite signs.

The map family's single storage decision — `MEntry.map` PROJECTS `WB` rather than storing it — shows
up at **two** assembly layers with **opposite signs**:

* At the ENTRY constructor it is a *shrink*: `buildLocatedMap` builds `MEntry.map …` with **no** `WB`
  argument (the seq sibling `buildLocatedSeq` feeds `SBody.toWB h_rec`), and the balance is recovered
  *post-hoc* by the projection — witnessed by `wb_recovered` above (`(buildLocatedMap …).toWB`).
* At the BUNDLE assembler it is a *growth*: `MLocated` STORES `keyF`, so `bundleLocatedMap` must
  *thread it in* as the extra `h_key` hypothesis the seq bundle lacks — witnessed by the extra
  `(by decide)` in `mlocated_a`, and recovered by projecting it back out below.

Same mechanism (what the type stores vs. what the producer delivers), read at two layers, one sign
each.  The toy cannot reproduce R248's *axiom*-ledger half (both toy builds are choice-free), but the
arity half — shrink here, growth there — is exactly these witnesses. -/

/-- GROWTH made concrete: the stored pair primitive `keyF` projects back out of the map bundle (mirror
    of `slocated_entry`), proving it is a genuine stored field the assembler threaded in, not derived. -/
def mlocated_key : (2 : Nat) ≤ [Tok.om, .a, .cm].length := mlocated_a.keyF

/-- The recursive `entry` still projects back out too, exactly as on the seq side — the GROWTH is *only*
    in the extra stored primitive, the recursive field behaves identically across the two bundles. -/
def mlocated_entry : MEntry (([Tok.om, .a, .cm].take (2 + 1)).drop (1 - 1)) := mlocated_a.entry

/-! ## The opener-kind guard is load-bearing, and decidable balance sanity checks -/

/-- Count-based bracket balance — every opener (`[` or `{`) `+1`, every closer (`]` or `}`) `-1`,
    underflow → `none`.  A decidable recognizer used only for the `#guard` witnesses below. -/
def bal (d0 : Option Nat) (l : List Tok) : Option Nat :=
  l.foldl (fun acc t => acc.bind (fun d =>
    match t with
    | .os | .om => some (d + 1)
    | .cs | .cm => if d = 0 then none else some (d - 1)
    | .a        => some d)) d0

/-- The seq opener `[` is not the map opener `{`: the two builds' opener guards discriminate, so a
    `{ … }` window cannot be built by `buildLocatedSeq` nor a `[ … ]` window by `buildLocatedMap`. -/
theorem seq_opener_ne_map : (Tok.os = Tok.om) = False := by simp

/-- An atom is not an opener of either kind, so a window whose front token is `.a` builds no frame. -/
theorem atom_not_opener : (Tok.a = Tok.os) = False := by simp

-- Decidable sanity checks (fail the build if any witness drifts).
#guard decide (Tok.os = Tok.om) = false              -- the two openers are distinct kinds
#guard decide (Tok.a = Tok.os) = false               -- an atom is not the seq opener
#guard bal (some 0) [.os, .a, .cs] = some 0          -- the seq window `[ a ]` is balanced
#guard bal (some 0) [.om, .a, .cm] = some 0          -- the map window `{ a }` is balanced
#guard bal (some 0) [.os, .om, .a, .cm, .cs] = some 0  -- a mixed nest `[ { a } ]` is balanced
#guard bal (some 0) [.om, .a] = some 1               -- ...missing closer: ends at depth 1, not 0
#guard bal (some 0) [.cm, .om] = none                -- close-before-open underflows

end ProducerDualOfConsumer
