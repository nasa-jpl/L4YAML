/-
# Reflection 534 — routing a producer-fact THROUGH an agnostic recursion: strengthen the locate's
existential to EMIT the marker balance the descend consumes, and the width-recursion driver carries it
for free

Self-contained companion to `recbody_joint_navigator_driver_carrier`
(`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`), the carrier-specialised
instantiation of the abstract joint driver `recbody_joint_navigator_driver` (R529) at the named guard
`RecBodyJointGuard` (R533), with the descend slot discharged by `recbody_joint_guard_descend_tail`.

The point this file isolates — **a width-recursion driver runs a strong recursion over a guard `G` and a
locate/assemble/descend triad; the descend (R533) CONSUMES a fact (`Bal lo m`, the located separator's
depth-`0` balance) that the recursion combinator itself never mentions.**  The fix is not to teach the
combinator about the balance — it stays agnostic.  It is to STRENGTHEN the locate to EMIT the balance as
one extra conjunct of its existential, and let the driver body ROUTE it straight from the locate's `∃`
into the descend's premise across the `oracle`/`assemble` stitch.  A producer-side fact (the locate knows
where the separator sits and at what depth) reaches a consumer-side premise (the descend narrows the
carrier there) purely by widening the locate's `∃` and the descend's premise in lockstep.  The cost is
exactly one new binder at three sites: the locate existential, the `obtain`, and the descend call.

What this file does:
* `widthRec` — the agnostic span-bounded strong recursion combinator (the toy of
  `windowWidth_strongRecOn`), which never mentions the balance.
* `driver` — the abstract carrier-specialised driver: locate emits `Bal lo m`, the body threads it into
  `descend` (which produces the guard `G (m+1) hi`, the R533 shape).  This is the artifact whose axioms
  are audited; it is the faithful shape of the real per-window step.
* `routeOnce` — the balance routing in ISOLATION at a single window (tail supplied directly, no
  recursion), instantiated at toy types and RUN end-to-end — the part that elaborates to a closed value,
  since a full recursion run would hit locate's window-non-emptiness demand (a separate brick).

The joint two-branch (seq+map) structure is demoed in `JointGuardDescendTail` (R533); here `driver`
carries a single `Body` so the new content — the balance routing — is the only moving part.
-/

namespace JointNavigatorDriverCarrier

set_option autoImplicit false

/-! ## The agnostic recursion combinator — never mentions the balance. -/

/-- Toy span-bounded strong recursion (the toy of `windowWidth_strongRecOn`): generalise the window
    width to a bound `n` so the IH ranges over every strictly-narrower span.  Agnostic to `G` and to any
    fact a concrete `G`/descend might carry — in particular it never names the balance. -/
theorem widthRec {P : Nat → Nat → Prop} (G : Nat → Nat → Prop)
    (step : ∀ lo hi, G lo hi →
      (∀ lo' hi', hi' - lo' < hi - lo → G lo' hi' → P lo' hi') → P lo hi) :
    ∀ lo hi, G lo hi → P lo hi := by
  have key : ∀ n : Nat, ∀ lo hi : Nat, hi - lo ≤ n → G lo hi → P lo hi := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n IH =>
      intro lo hi h_span h_g
      exact step lo hi h_g (fun lo' hi' h_lt h_g' =>
        IH (hi' - lo') (by omega) lo' hi' (Nat.le_refl _) h_g')
  intro lo hi h_g
  exact key (hi - lo) lo hi (Nat.le_refl _) h_g

/-! ## The driver — locate EMITS the balance, the body ROUTES it into the descend. -/

/-- **The carrier-specialised driver at a concrete guard.**  Parametric in the guard `G`, the per-window
    deliverable `Body`, the located-item predicate `Item`, the marker balance `Bal`, the separator `Sep`,
    and three edges:

    * `assemble` — fold the located first item and the tail into the window deliverable (the toy of
      `recseqbody_window_assemble`).
    * `descend` — advance the GUARD past the located separator to the suffix `[m+1, hi)`, CONSUMING the
      balance `Bal lo m` (the toy of `recbody_joint_guard_descend_tail`, R533): `… → Bal lo m → G (m+1) hi`.
    * `locate` — classify the first item AND EMIT its balance: `… → ∃ m, lo < m ∧ m ≤ hi ∧
      (m = hi ∨ Sep m) ∧ Bal lo m ∧ Item lo m`.  The `Bal lo m` conjunct is the strengthening — without
      it the descend could not be called (no balance in scope).

    The body runs `widthRec`, locates (binding the emitted `h_bal`), assembles, and on the advance branch
    routes `h_bal` straight into `descend`.  Note `widthRec`'s `oracle` carries only `G`/`Body` — the
    balance never passes through it; the locate produces it and the descend consumes it within the same
    per-window step. -/
theorem driver
    (G Body Item Bal : Nat → Nat → Prop) (Sep : Nat → Prop)
    (assemble : ∀ lo m hi, lo < m → m ≤ hi → (m = hi ∨ Sep m) → Item lo m →
        (m < hi → Body (m + 1) hi) → Body lo hi)
    (descend : ∀ lo hi m, G lo hi → lo < m → m < hi → Sep m → Bal lo m → G (m + 1) hi)
    (locate : ∀ lo hi, G lo hi →
        (∀ lo' hi', hi' - lo' < hi - lo → G lo' hi' → Body lo' hi') →
        ∃ m, lo < m ∧ m ≤ hi ∧ (m = hi ∨ Sep m) ∧ Bal lo m ∧ Item lo m) :
    ∀ lo hi, G lo hi → Body lo hi := by
  refine widthRec G (fun lo hi h_g oracle => ?_)
  -- locate emits the balance `h_bal` alongside the item;
  obtain ⟨m, h_lo_m, h_m_hi, h_marker, h_bal, h_item⟩ := locate lo hi h_g oracle
  refine assemble lo m hi h_lo_m h_m_hi h_marker h_item (fun h_lt => ?_)
  -- the advance branch routes `h_bal` straight into the guard descend; the oracle never sees it.
  have h_sep : Sep m := h_marker.resolve_left (by omega)
  exact oracle (m + 1) hi (by omega) (descend lo hi m h_g h_lo_m h_lt h_sep h_bal)

/-! ## The balance routing in ISOLATION — one window, fully runnable. -/

/-- **The routing at a single window** (tail supplied directly — no recursion, so no window-non-emptiness
    obligation).  `locate` has emitted `h_bal : Bal lo m`; `assemble` needs the tail; the tail is the
    descend at the suffix, and the descend CONSUMES `h_bal`.  Isolates exactly the move `driver` performs:
    the located balance flows from the existential into the descend premise. -/
theorem routeOnce
    (Body Item Bal : Nat → Nat → Prop) (Sep : Nat → Prop)
    (assemble : ∀ lo m hi, lo < m → m ≤ hi → (m = hi ∨ Sep m) → Item lo m →
        (m < hi → Body (m + 1) hi) → Body lo hi)
    (descendBody : ∀ lo hi m, lo < m → m < hi → Sep m → Bal lo m → Body (m + 1) hi)
    (lo hi m : Nat) (h_lo_m : lo < m) (h_m_hi : m ≤ hi)
    (h_marker : m = hi ∨ Sep m) (h_bal : Bal lo m) (h_item : Item lo m) :
    Body lo hi :=
  assemble lo m hi h_lo_m h_m_hi h_marker h_item
    (fun h_lt => descendBody lo hi m h_lo_m h_lt (h_marker.resolve_left (by omega)) h_bal)

/-! ## Toy instance: the routing RUNS end-to-end. -/

/-- All predicates trivial; the located item, its balance, and the separator are `True`. -/
def Bd (_ _ : Nat) : Prop := True
def It (_ _ : Nat) : Prop := True
def Bl (_ _ : Nat) : Prop := True
def Sp (_ : Nat) : Prop := True

/-- The toy assemble: the deliverable is `True`, so it folds to `trivial`. -/
theorem assembleToy : ∀ lo m hi, lo < m → m ≤ hi → (m = hi ∨ Sp m) → It lo m →
    (m < hi → Bd (m + 1) hi) → Bd lo hi :=
  fun _ _ _ _ _ _ _ _ => trivial

/-- The toy descend-into-body: the suffix deliverable is `True`; the consumed balance `h_bal` is carried
    but the trivial body needs nothing of it. -/
theorem descendBodyToy : ∀ lo hi m, lo < m → m < hi → Sp m → Bl lo m → Bd (m + 1) hi :=
  fun _ _ _ _ _ _ _ => trivial

/-- The routing RUN: a window `[0, 2)` with the first item located at `m = 1`, its balance `Bl 0 1`
    emitted, threaded through `descendBodyToy` to the suffix.  Elaborates to a closed value. -/
example : Bd 0 2 :=
  routeOnce Bd It Bl Sp assembleToy descendBodyToy 0 2 1 (by omega) (by omega)
    (Or.inr trivial) trivial trivial

/-- The punchline for the axiom audit: the abstract carrier-specialised driver — the full
    locate-emits-balance / body-routes-it-into-descend per-window step, no `sorry`. -/
theorem demo
    (G Body Item Bal : Nat → Nat → Prop) (Sep : Nat → Prop)
    (assemble : ∀ lo m hi, lo < m → m ≤ hi → (m = hi ∨ Sep m) → Item lo m →
        (m < hi → Body (m + 1) hi) → Body lo hi)
    (descend : ∀ lo hi m, G lo hi → lo < m → m < hi → Sep m → Bal lo m → G (m + 1) hi)
    (locate : ∀ lo hi, G lo hi →
        (∀ lo' hi', hi' - lo' < hi - lo → G lo' hi' → Body lo' hi') →
        ∃ m, lo < m ∧ m ≤ hi ∧ (m = hi ∨ Sep m) ∧ Bal lo m ∧ Item lo m) :
    ∀ lo hi, G lo hi → Body lo hi :=
  driver G Body Item Bal Sep assemble descend locate

end JointNavigatorDriverCarrier

/-- info: 'JointNavigatorDriverCarrier.demo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms JointNavigatorDriverCarrier.demo
