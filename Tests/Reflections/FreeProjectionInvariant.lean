/-!
# Reflections 253 + 254 — a maintained invariant that is a conjunct of a projected property is a *free field*; and the one invariant with no local projection is recovered *non-locally* from the outer span

Self-contained core-Lean toy (no `L4YAML` import) for the principle: **when a consumer bundle's
field is definitionally a conjunct of a property the recursive deliverable already projects to, that
field is not a threaded obligation — it is a free projection.**  Read the deliverable's projection
family *before* deciding what the recursion must thread.

In L4YAML this is the per-window Dyck floor of `SeqLocated`/`MapLocated`: it is exactly the second
conjunct of `WellBracketed` of the inner window, and `WellBracketed` is what `Rec…Body` projects to
(`toWellBracketed`), so the locate need not thread a Dyck invariant — `dyck_of_wellBracketed_window`
hands it back for free.  By contrast `WellTyped` has **no** `Rec…Body.toWellTyped` projection
(R244 stored-vs-projected), so it stays a genuinely threaded hypothesis.

Toy model (two bracket types, `os/cs` square and `om/cm` curly, with an **untyped** balance that
treats both alike):

* `WB l := balance l = 0 ∧ ∀ i, 0 ≤ balance (l.take i)` — the untyped Dyck property.  Its second
  conjunct *is* the windowed "dyck floor".
* `Rec` — the recursive deliverable.  Its `wrap` constructor stores only `WB inner` (the *projecting*
  member, mirroring `RecSeqEntry.map`) and accepts **any** open paired with **any** close (`os…cm`
  included), so `Rec` is *untyped*.  `Rec.toWB` is the projection (the one real proof; the `wrap`
  case is `WB_wrap`).
* `WT` — *typed* bracket matching (`os` must close with `cs`, `om` with `cm`), a decidable stack
  check.  It is **not** projectable from `Rec` (no `Rec.toWT`), witnessed by a list with
  `Rec ∧ ¬ WT`.
* `Located` — the consumer bundle with two fields: `wt : WT l` (threaded) and
  `dyck : ∀ i, 0 ≤ balance (l.take i)` (the free conjunct).  `located_of_rec` takes **only** `wt`
  and derives `dyck` from `(Rec.toWB h).2` — no `h_dyck` hypothesis.

Witnesses (positive *and* negative):

* positive — `Rec [os,a,cs]` (typed-matched) and `WT [os,a,cs]` assemble a `Located`;
* the free field — `dyck` is available even for the *mismatched* `[os,a,cm]` (the projection needs
  no `WT`): `(rec_mismatched.toWB).2`;
* negative — `Rec [os,a,cm]` holds yet `¬ WT [os,a,cm]`, so `WT` is **not** determined by the
  deliverable and **cannot** be projected — it must be threaded.  No `Located [os,a,cm]` is
  derivable, exactly because its `wt` field has no source.
-/

namespace Tests.Reflections.FreeProjectionInvariant

/-- Token alphabet: square open/close, curly open/close, and a zero-delta scalar. -/
inductive Tok | os | cs | om | cm | a
  deriving DecidableEq

/-- **Untyped** bracket delta: both open kinds `+1`, both close kinds `-1`, scalar `0`. -/
def delta : Tok → Int
  | .os => 1 | .om => 1
  | .cs => -1 | .cm => -1
  | .a => 0

/-- Untyped running balance of a token list. -/
def balance (l : List Tok) : Int := (l.map delta).sum

theorem balance_nil : balance [] = 0 := rfl
theorem balance_cons (t : Tok) (l : List Tok) : balance (t :: l) = delta t + balance l := by
  simp [balance]
theorem balance_append (a b : List Tok) : balance (a ++ b) = balance a + balance b := by
  simp [balance, List.sum_append]
theorem balance_singleton (t : Tok) : balance [t] = delta t := by simp [balance]

/-- The untyped Dyck property: total balance `0` and every prefix balance `≥ 0`.  The second
    conjunct is the "dyck floor" the consumer bundle's `dyck` field wants. -/
def WB (l : List Tok) : Prop := balance l = 0 ∧ ∀ i, 0 ≤ balance (l.take i)

/-- `WB` of a zero-delta singleton (the scalar leaf). -/
theorem WB_scalar : WB [Tok.a] := by
  refine ⟨by decide, fun i => ?_⟩
  cases i with
  | zero => simp [balance]
  | succ k => simp [balance, delta]

/-- **`WB` of a bracket wrap** — the crux projection step.  Any `+1` open and `-1` close wrapping a
    `WB` interior is `WB`: total balance `1 + 0 + (-1) = 0`, and each prefix stays `≥ 0` because the
    `+1` opener floats the interior's own `≥ -1` floor (a close can dip the interior prefix by at
    most one) back to `≥ 0`. -/
theorem WB_wrap (o c : Tok) (inner : List Tok) (ho : delta o = 1) (hc : delta c = -1)
    (h : WB inner) : WB (o :: (inner ++ [c])) := by
  obtain ⟨hbal, hdyck⟩ := h
  refine ⟨?_, fun i => ?_⟩
  · rw [balance_cons, balance_append, balance_singleton, ho, hc, hbal]; omega
  · cases i with
    | zero => simp [balance]
    | succ k =>
      rw [List.take_succ_cons, balance_cons, ho]
      have hk : -1 ≤ balance ((inner ++ [c]).take k) := by
        rw [List.take_append, balance_append]
        have h1 : 0 ≤ balance (inner.take k) := hdyck k
        have h2 : balance ([c].take (k - inner.length)) = 0
            ∨ balance ([c].take (k - inner.length)) = -1 := by
          cases (k - inner.length) with
          | zero => left; simp [balance, List.take_zero]
          | succ m => right; rw [List.take_succ_cons, List.take_nil, balance_singleton, hc]
        omega
      omega

/-- The recursive deliverable.  `wrap` **stores only `WB inner`** (the *projecting* member, like
    `RecSeqEntry.map`) and accepts any open/close pair — so `Rec` is *untyped* and does **not**
    enforce typed bracket matching. -/
inductive Rec : List Tok → Prop
  | scalar : Rec [Tok.a]
  | wrap (o c : Tok) (inner : List Tok) (ho : delta o = 1) (hc : delta c = -1)
      (h : WB inner) : Rec (o :: (inner ++ [c]))

/-- **The projection** `Rec.toWB` (mirror of `RecSeqBody.toWellBracketed`).  The `wrap` case is
    exactly `WB_wrap`; the deliverable carries its `WB` for free. -/
theorem Rec.toWB {l : List Tok} (h : Rec l) : WB l := by
  cases h with
  | scalar => exact WB_scalar
  | wrap o c inner ho hc hwb => exact WB_wrap o c inner ho hc hwb

/-- **Typed** bracket matching as a decidable stack check (the `WellTyped` analog): `os` must close
    with `cs`, `om` with `cm`. -/
def wtAux : List Tok → List Tok → Bool
  | [], stack => stack.isEmpty
  | .a :: rest, stack => wtAux rest stack
  | .os :: rest, stack => wtAux rest (.cs :: stack)
  | .om :: rest, stack => wtAux rest (.cm :: stack)
  | .cs :: rest, c :: stack => (c == Tok.cs) && wtAux rest stack
  | .cm :: rest, c :: stack => (c == Tok.cm) && wtAux rest stack
  | _ :: _, [] => false

/-- Typed well-bracketing: a property `Rec` does **not** project to (no `Rec.toWT`). -/
def WT (l : List Tok) : Prop := wtAux l [] = true

/-- The consumer bundle.  `wt` is threaded (no projection supplies it); `dyck` is the free conjunct
    of the deliverable's `WB`. -/
structure Located (l : List Tok) : Prop where
  wt : WT l
  dyck : ∀ i, 0 ≤ balance (l.take i)

/-- **The assembler reads `dyck` off the deliverable for free.**  It takes only `wt` as a hypothesis
    and derives `dyck` from `(Rec.toWB h).2` — no separate `h_dyck`.  Mirror of the strengthened
    `seqLocated_of_recseqbody`/`mapLocated_of_recmapbody` (Reflection 253). -/
theorem located_of_rec {l : List Tok} (h : Rec l) (hwt : WT l) : Located l :=
  ⟨hwt, (Rec.toWB h).2⟩

/-! ## Positive witness — typed-matched `[os, a, cs]` assembles a `Located`. -/

theorem rec_matched : Rec [Tok.os, Tok.a, Tok.cs] :=
  Rec.wrap Tok.os Tok.cs [Tok.a] (by decide) (by decide) WB_scalar

theorem wt_matched : WT [Tok.os, Tok.a, Tok.cs] := by unfold WT; decide

/-- `Located [os, a, cs]` — the assembler needed no Dyck hypothesis. -/
theorem located_matched : Located [Tok.os, Tok.a, Tok.cs] :=
  located_of_rec rec_matched wt_matched

/-! ## The free field — `dyck` is available even for the *mismatched* `[os, a, cm]`,
    because the projection needs no `WT`. -/

theorem rec_mismatched : Rec [Tok.os, Tok.a, Tok.cm] :=
  Rec.wrap Tok.os Tok.cm [Tok.a] (by decide) (by decide) WB_scalar

/-- The Dyck floor is free for the mismatched list too: it is `(toWB …).2`, no `WT` consulted. -/
theorem dyck_mismatched_free : ∀ i, 0 ≤ balance ([Tok.os, Tok.a, Tok.cm].take i) :=
  (Rec.toWB rec_mismatched).2

/-! ## Negative witness — `WT` is **not** a free projection: `Rec` holds but `WT` fails, so the
    `wt` field has no source and must be threaded.  No `Located [os, a, cm]` is derivable. -/

theorem not_wt_mismatched : ¬ WT [Tok.os, Tok.a, Tok.cm] := by unfold WT; decide

/-- Positive `dyck` / negative `wt`, side by side — the deliverable determines the free field but
    not the threaded one. -/
example : (∀ i, 0 ≤ balance ([Tok.os, Tok.a, Tok.cm].take i)) ∧ ¬ WT [Tok.os, Tok.a, Tok.cm] :=
  ⟨dyck_mismatched_free, not_wt_mismatched⟩

#guard wtAux [Tok.os, Tok.a, Tok.cs] [] = true   -- typed-matched
#guard wtAux [Tok.os, Tok.a, Tok.cm] [] = false  -- type-mismatched: Rec ok, WT not

/-! ## Reflection 254 — the *non-locally* recovered invariant: `WT` from the OUTER `WT`.

R253 (above) showed the window's `dyck` field is free *locally* — `(Rec.toWB h).2`, off the
window's OWN deliverable.  But `WT` has no `Rec.toWT` (the untyped `Rec` accepts `[os,a,cm]`,
which is not `WT` — `rec_mismatched`/`not_wt_mismatched`), so it cannot be recovered locally.
R254's point: it is recovered all the same — **non-locally**, from the *enclosing* window's `WT`,
via a subrange lemma whose two side conditions are themselves the window's *free* balance and
*free* Dyck.

In L4YAML the subrange lemma is `WellTyped_subrange` (proved once, globally, via
`WellTyped_infix_balanced`); the locate's per-window assembler `seqLocated_of_recseqbody_outer`
does not re-prove it — it **calls** it, supplying the two side conditions from the window's own
`Rec`.  We model that interface as `WTsub` and show (i) it is inhabited (non-vacuous, `decide`)
and (ii) the outer assembler `located_of_rec_outer` recovers the window's `wt` through it while
reading its `dyck` and the subrange's balance/Dyck side conditions **for free** off `Rec.toWB` —
no per-window `WT` and no `dyck` hypothesis, only the structural `Rec` and ONE outer `WT`. -/

/-- The subrange interface: a balanced window's `WT` recovered from the OUTER `WT` plus the
    window's balance and Dyck.  (In L4YAML this is `WellTyped_subrange`; here it is the cited
    interface the outer assembler calls — exactly as `seqLocated_of_recseqbody_outer` calls it,
    not re-proving it.) -/
abbrev WTsub (outer window : List Tok) : Prop :=
  WT outer → balance window = 0 → (∀ i, 0 ≤ balance (window.take i)) → WT window

/-- Non-vacuity: the interface holds for a concrete nested witness `{ { a } } ⊃ { a }`. -/
theorem wtsub_concrete : WTsub [Tok.om, Tok.om, Tok.a, Tok.cm, Tok.cm] [Tok.om, Tok.a, Tok.cm] :=
  fun _ _ _ => by unfold WT; decide

/-- The inner window `{ a }` is a `Rec` (untyped) — supplies balance + Dyck for free, but NOT `WT`. -/
theorem rec_window : Rec [Tok.om, Tok.a, Tok.cm] :=
  Rec.wrap Tok.om Tok.cm [Tok.a] (by decide) (by decide) WB_scalar

/-- **The outer locate assembler** (toy mirror of `seqLocated_of_recseqbody_outer`): threads ONE
    outer `WT`, recovers the window's `wt` via the subrange interface, and reads the window's
    `dyck` and the subrange's balance/Dyck side conditions FOR FREE off the window's own
    `Rec.toWB`.  No per-window `WT` hypothesis and no `dyck` hypothesis — only the structural
    `Rec`, the outer `WT`, and the window's (free) balance. -/
theorem located_of_rec_outer (outer window : List Tok)
    (hsub : WTsub outer window) (h_outer : WT outer) (h_rec : Rec window)
    (h_bal : balance window = 0) : Located window :=
  ⟨hsub h_outer h_bal (Rec.toWB h_rec).2, (Rec.toWB h_rec).2⟩

/-- Concrete `Located` assembled the R254 way: the outer `WT` of `{ { a } }` recovers the inner
    `{ a }` window's `WT`; the window's own `Rec` supplies balance + Dyck for free. -/
theorem located_window_via_outer : Located [Tok.om, Tok.a, Tok.cm] :=
  located_of_rec_outer [Tok.om, Tok.om, Tok.a, Tok.cm, Tok.cm] [Tok.om, Tok.a, Tok.cm]
    wtsub_concrete (by unfold WT; decide) rec_window (by decide)

#guard wtAux [Tok.om, Tok.om, Tok.a, Tok.cm, Tok.cm] [] = true  -- outer { { a } } is WT
#guard wtAux [Tok.om, Tok.a, Tok.cm] [] = true                  -- recovered inner { a } is WT

end Tests.Reflections.FreeProjectionInvariant
