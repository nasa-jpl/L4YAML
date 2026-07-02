/-!
# Reflection 459 — a flat-severance constructor that is TOKEN-INDISTINGUISHABLE from its recursive
# sibling blocks `cases`-recovery of the recursion: the body must be THREADED from the producer, not
# RECOVERED by the descent.  The seq/map asymmetry, and the producer→navigator bridge it forces.

Self-contained (core Lean, no `L4YAML` import) toy of the R459 finding, executing STEP D step 4 of the
`mapRec` programme.  After R458 the producer builds `RecSeqEntry.mapRec` (carrying the recursive
`RecMapBody interior`) for non-empty maps and the flat `RecSeqEntry.map` (carrying only `WellBracketed
interior`) for the empty `{}`.  Step 4 needs the *descent*: from a located map entry, recover its inner
`RecMapBody` so the map navigator can recurse.

The plan was to mirror `RecSeqEntry.seq_interior` — a plain `cases`-projection
`RecSeqEntry (.flowSequenceStart-headed) → RecSeqBody interior ∨ interior = []`.  PROBING that plan
([[ref-probe-deferred-universal-before-producing]]) reveals it CANNOT work on the map side, for a
structural reason:

* **`seq_interior` is debt-free** because `RecSeqEntry` has **no flat seq severance** — every nested
  flow-SEQUENCE entry is `.seqEmpty` (empty) or `.seq` (which STORES its `RecSeqBody`).  `cases` digs
  the body straight out of the `.seq` constructor.
* **The map side is asymmetric.**  Alongside recursive `.mapRec` (stores `RecMapBody interior`) there
  is flat `.map` (stores only `WellBracketed interior`), built by the seq-navigator near-leaf that
  severs a map appearing as a sequence ITEM.  And `.map interior` / `.mapRec interior` are
  **token-indistinguishable**: same index `op :: (interior ++ [cl])`, same tokens.  No `cases` can tell
  them apart.  Worse, flat `.map` admits interiors that are `WellBracketed` but NOT a `RecMapBody`, so
  `RecMapBody interior` is a fact about `interior` the entry type genuinely does not determine — *any*
  hypothesis strong enough to conclude it is EQUIVALENT to the conclusion.

So the recursive body cannot be RECOVERED by the descent; it must be THREADED from the PRODUCER (which
holds the body / emptiness at build time).  That threaded body is the descent's DEBT
([[ref-root-seed-discriminator-not-from-gate]]).  The clean way to consume it is the bridge into the
SEVERANCE-FREE recursive entry type `RecMapEntry` (whose own `map_interior` descent IS debt-free,
exactly because `RecMapEntry` has no flat constructor): `RecSeqEntry.toRecMapEntry` reads the closer off
the located entry, dispatches the body's emptiness disjunct to `RecMapEntry.mapEmpty`/`.map`, and the
existing `recmapbody_window_of_located_entry` descends from there.

This toy mirrors all of it with a 5-token alphabet:

* `SeqEntry` — the entry type, with BOTH a flat severance (`mapFlat`, stores only the weak `WB`) and a
  recursive sibling (`mapRec`, stores `Body`), plus the seq constructors (no flat seq severance).
* `seq_interior` — DEBT-FREE `cases`-projection (the seq side; `seqRec` stores the body).
* `mapRec_interior` — the map descent: `cases` recovers the body from `mapRec` with NO debt, but the
  flat `mapFlat` branch can only FORWARD the producer's debt `h_body` — it cannot recover.
* `severance_gap_is_real` — a concrete `mapFlat` whose interior is `WB` but provably NOT `Body`-or-empty:
  the descent genuinely cannot conclude for it, witnessing the debt is not removable.
* `MapEntry` / `MapEntry.map_interior` — the severance-free recursive type and its debt-free descent.
* `toMapEntry` — the producer→navigator bridge: given the producer's body debt, package into `MapEntry`.
* `bridge_roundtrips_debt` — the bridge then `map_interior` returns exactly the debt: the bridge is a
  re-packaging of producer-held data into the navigator's input type, NOT a free descent.
* `seq_map_descent_asymmetry` — the finding in one proposition: the seq descent needs no debt, the map
  descent does, and the debt is unavoidable (the gap is real).

All sorry-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.TokenIndistinguishableSeveranceThreadsRecursionFromProducer

/-- Toy alphabet: `a` content, `mop`/`mcl` map brackets, `sop`/`scl` seq brackets. -/
inductive Tok where
  | a | mop | mcl | sop | scl
deriving DecidableEq

/-- Append-singleton injectivity (core Lean, the same lemma the real descents use). -/
theorem append_singleton_inj {a b : List Tok} {x y : Tok}
    (h : a ++ [x] = b ++ [y]) : a = b ∧ x = y := by
  have hr := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hr
  injection hr with hxy har
  exact ⟨List.reverse_inj.mp har, hxy⟩

/-- The recursive body (mirror `RecMapBody`/`RecSeqBody`): non-empty lists of `a`s. -/
inductive Body : List Tok → Prop where
  | one : Body [Tok.a]
  | more (rest : List Tok) (hr : Body rest) : Body (Tok.a :: rest)

/-- The WEAK bracket fact the flat severance stores (mirror `WellBracketed`): here trivially true of
    ANY interior — which is exactly what lets the flat `.map` carry a non-`Body` interior. -/
def WB (_l : List Tok) : Prop := True

/-- The entry type (mirror `RecSeqEntry`).  Seq side: `scalar`/`seqEmpty` leaves and the RECURSIVE
    `seqRec` (stores `Body`) — **no flat seq severance**.  Map side: the flat `mapFlat` (stores only
    `WB` — the severance the seq-navigator near-leaf builds) AND the recursive `mapRec` (stores `Body`).
    `mapFlat interior` and `mapRec interior` carry the SAME tokens — token-indistinguishable. -/
inductive SeqEntry : List Tok → Prop where
  | scalar : SeqEntry [Tok.a]
  | seqEmpty : SeqEntry (Tok.sop :: ([] ++ [Tok.scl]))
  | seqRec (interior : List Tok) (h : Body interior) :
      SeqEntry (Tok.sop :: (interior ++ [Tok.scl]))
  | mapFlat (interior : List Tok) (hwb : WB interior) :
      SeqEntry (Tok.mop :: (interior ++ [Tok.mcl]))
  | mapRec (interior : List Tok) (hwb : WB interior) (h : Body interior) :
      SeqEntry (Tok.mop :: (interior ++ [Tok.mcl]))

/-- **Seq descent — DEBT-FREE** (mirror `RecSeqEntry.seq_interior`).  A `.sop`-headed entry yields its
    `Body` or is empty, recovered by a plain `cases`: the recursive `seqRec` STORES the body, and there
    is no flat seq severance to block recovery. -/
theorem seq_interior {e interior : List Tok}
    (h : SeqEntry e) (h_eq : e = Tok.sop :: (interior ++ [Tok.scl])) :
    Body interior ∨ interior = [] := by
  cases h with
  | scalar => injection h_eq with _h1 h2; simp at h2
  | seqEmpty =>
      right; injection h_eq with _h1 h2
      simp only [List.nil_append] at h2
      exact (append_singleton_inj h2.symm).1
  | seqRec interior' h =>
      left; injection h_eq with _h1 h2
      exact (append_singleton_inj h2).1 ▸ h
  | mapFlat interior' hwb => injection h_eq with h1 _h2; exact absurd h1 (by decide)
  | mapRec interior' hwb h => injection h_eq with h1 _h2; exact absurd h1 (by decide)

/-- **Map descent — DEBT-REQUIRING** (the would-be `RecSeqEntry.mapRec_interior`).  A `.mop`-headed
    entry: the `cases` recovers the body from `mapRec` with NO debt (it STORES `Body`), but the flat
    `mapFlat` branch — token-indistinguishable and storing only `WB` — can do nothing but FORWARD the
    producer's debt `h_body`.  This is the seq/map asymmetry made executable. -/
theorem mapRec_interior {e interior : List Tok}
    (h : SeqEntry e) (h_eq : e = Tok.mop :: (interior ++ [Tok.mcl]))
    (h_body : Body interior ∨ interior = []) :   -- the producer's DEBT
    Body interior ∨ interior = [] := by
  cases h with
  | scalar => simp at h_eq
  | seqEmpty => simp at h_eq
  | seqRec interior' h => simp at h_eq
  | mapFlat interior' hwb =>
      -- SEVERANCE: only `WB` stored; the body is unrecoverable here ⇒ forward the producer's debt.
      exact h_body
  | mapRec interior' hwb h =>
      -- RECURSIVE: body stored ⇒ recover WITHOUT touching the debt.
      left; injection h_eq with _h1 h2
      exact (append_singleton_inj h2).1 ▸ h

/-- **The gap is real.**  A flat `mapFlat` entry whose interior `[mcl]` is `WB` (trivially) but is
    provably NOT a `Body`-or-empty.  So for this entry `mapRec_interior` genuinely cannot conclude — the
    debt is not a removable artefact, it carries information the type does not.  (On the emit feed such an
    entry never arises: the producer builds `mapRec` for non-empty maps; this off-feed inhabitant exists
    only because the type admits the severance.) -/
theorem severance_gap_is_real :
    SeqEntry (Tok.mop :: ([Tok.mcl] ++ [Tok.mcl])) ∧ ¬ (Body [Tok.mcl] ∨ [Tok.mcl] = []) := by
  refine ⟨SeqEntry.mapFlat [Tok.mcl] trivial, ?_⟩
  rintro (hb | he)
  · cases hb
  · simp at he

/-- The SEVERANCE-FREE recursive map entry (mirror `RecMapEntry`): only `mapEmpty` and a `map` that
    STORES `Body`.  No flat constructor ⇒ its own descent is debt-free. -/
inductive MapEntry : List Tok → Prop where
  | mapEmpty : MapEntry (Tok.mop :: ([] ++ [Tok.mcl]))
  | map (interior : List Tok) (h : Body interior) :
      MapEntry (Tok.mop :: (interior ++ [Tok.mcl]))

/-- **`MapEntry` descent — DEBT-FREE** (mirror `RecMapEntry.map_interior`).  Because `MapEntry` has no
    flat severance, `cases` recovers the body directly — this is why the bridge targets `MapEntry`. -/
theorem MapEntry.map_interior {e interior : List Tok}
    (h : MapEntry e) (h_eq : e = Tok.mop :: (interior ++ [Tok.mcl])) :
    Body interior ∨ interior = [] := by
  cases h with
  | mapEmpty =>
      right; injection h_eq with _h1 h2
      simp only [List.nil_append] at h2
      exact (append_singleton_inj h2.symm).1
  | map interior' h =>
      left; injection h_eq with _h1 h2
      exact (append_singleton_inj h2).1 ▸ h

/-- **Producer→navigator bridge** (mirror `RecSeqEntry.toRecMapEntry`).  Given the located map entry
    `h` and the producer's body debt `h_body`, package into the severance-free `MapEntry` the navigator
    descends.  (`h` is consumed in the real code to read the closer off the located entry; the toy's
    closer is the constant `mcl`, so `h` is carried but not destructured.)  The emptiness disjunct
    selects `mapEmpty` vs `map`. -/
theorem toMapEntry {e interior : List Tok}
    (_h : SeqEntry e) (h_eq : e = Tok.mop :: (interior ++ [Tok.mcl]))
    (h_body : Body interior ∨ interior = []) :
    MapEntry e := by
  subst h_eq
  cases h_body with
  | inl hb => exact MapEntry.map interior hb
  | inr he => subst he; exact MapEntry.mapEmpty

/-- **The bridge is a re-packaging, not a free descent.**  Bridging the producer's debt into `MapEntry`
    and then running the debt-free `MapEntry.map_interior` returns *exactly* the debt — so the recursion
    really did come from the producer, threaded through the type, never manufactured by a `cases`. -/
theorem bridge_roundtrips_debt {e interior : List Tok}
    (h : SeqEntry e) (h_eq : e = Tok.mop :: (interior ++ [Tok.mcl]))
    (h_body : Body interior ∨ interior = []) :
    MapEntry.map_interior (toMapEntry h h_eq h_body) h_eq = h_body := by
  -- proof-irrelevance for `Prop`-valued disjunctions; both sides inhabit the same proposition.
  rfl

/-- **The finding in one proposition.**  (1) the SEQ descent recovers the body with no debt
    (severance-free side); (2) the MAP descent needs the producer's debt; (3) that debt is unavoidable —
    a concrete severance entry exists whose body is genuinely not `Body`-or-empty.  Sharpens
    `[[ref-probe-deferred-universal-before-producing]]`: token-indistinguishable flat/recursive
    constructors make the recursion producer-threaded, not descent-recovered. -/
theorem seq_map_descent_asymmetry :
    (∀ e interior, SeqEntry e → e = Tok.sop :: (interior ++ [Tok.scl]) →
      Body interior ∨ interior = [])                                   -- seq: debt-free
    ∧ (∀ e interior, SeqEntry e → e = Tok.mop :: (interior ++ [Tok.mcl]) →
        (Body interior ∨ interior = []) → Body interior ∨ interior = [])  -- map: needs the debt
    ∧ (SeqEntry (Tok.mop :: ([Tok.mcl] ++ [Tok.mcl]))
        ∧ ¬ (Body [Tok.mcl] ∨ [Tok.mcl] = [])) :=                      -- the debt is unavoidable
  ⟨fun _e _i h h_eq => seq_interior h h_eq,
   fun _e _i h h_eq h_body => mapRec_interior h h_eq h_body,
   severance_gap_is_real⟩

end Tests.Reflections.TokenIndistinguishableSeveranceThreadsRecursionFromProducer
