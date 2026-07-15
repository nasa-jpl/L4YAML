/-
# Reflection 257 — fold a joint-by-joint consumer chain into ONE lemma keyed only on the producer's contract

Self-contained, `L4YAML`-free runnable illustration of the proof-engineering principle in
Blueprint Reflection 257 (and memory `ref-fold-consumer-chain-to-producer-contract`).

**The principle.** When a consumer side is built up *joint by joint* across several boundaries —
each joint a verified-but-unconsumed lemma reducing one layer — the final move, *before writing the
producer*, is to **compose the whole chain into one lemma whose hypotheses are exactly the
producer's contract**. The fold costs nothing (it composes only landed lemmas, references no `sorry`,
cannot regress) but it converts a *scattered* residual — "thread the producer through three joints at
two call sites" — into one *typed boundary* the producer is written against, and makes the producer's
exact return obligation legible as a single signature.

In the L4YAML Phase-J locate this is `flowSubrangesOk_of_window_producers`, which folds three landed
joints — `flowSubrangesOk_of_locators` (universal packaging, R243) and the two boundary-anchoring
locator joints `seqLocator_of_window_recseqbody`/`mapLocator_of_window_recmapbody` (R255/R256) — into
one lemma keyed only on the still-owed per-window `RecSeqBody`/`RecMapBody` producers.

**The toy.** A framed token stream `SS … SE` (`SS`/`SE` the stream frame, `OB`/`CB` an opener/closer,
`A` content). The chain has two genuine joints and a packaging joint:

* `jBound` — boundary-anchoring: recover `2 ≤ lo` from the frame token `toks[0] = SS` (because
  `SS ≠ OB`), turning the *bounded* per-window producer into the *unbounded* per-window locator.
* `jPack`  — universal packaging: assemble the per-window locators into the universal `Target`.
* `targetOfProducer` — **the R257 fold**: `jPack ∘ jBound`, keyed only on `hProd` (the producer) and
  the frame token `hSS` (an in-scope fact). The producer stays an abstract hypothesis exactly as in
  L4YAML (verified-but-unconsumed: the recursion that discharges it is not yet written).

Positive: on `good = [SS, OB, A, CB, SE]` the frame token is present and `Producer good 2 3` holds.
Negative: on `bad = [OB, A, CB]` (no `SS` frame) the opener guard is satisfied at `lo = 1` — the very
window the missing frame token would have excluded — yet `2 ≤ 1` is false, so the bounded producer
would never reach it: the frame token is *load-bearing* for the fold.
-/

namespace Tests.Reflections.FoldConsumerChain

inductive Tok | SS | OB | CB | SE | A
  deriving DecidableEq, Inhabited, Repr

/-- toy "window slice" `[lo, hi)` of the stream. -/
def win (toks : List Tok) (lo hi : Nat) : List Tok := (toks.take hi).drop lo

/-- The producer's recursive deliverable (toy): the window is content-headed.  This is the
    bare hypothesis the still-unwritten recursion will eventually supply. -/
def Producer (toks : List Tok) (lo hi : Nat) : Prop :=
  (win toks lo hi).headD Tok.SE = Tok.A

/-- The per-window *located* bundle the packaging joint consumes — same field, the consumer form. -/
structure Located (toks : List Tok) (lo hi : Nat) : Prop where
  head : (win toks lo hi).headD Tok.SE = Tok.A

/-- The universal target.  Note the quantifier is **unbounded** in `lo` — only an opener guard,
    no `2 ≤ lo`. -/
def Target (toks : List Tok) : Prop :=
  ∀ lo hi, lo ≤ hi → hi < toks.length → toks[lo - 1]! = Tok.OB → Located toks lo hi

/-! ### The three joints (each a separately-landed brick in the real proof) -/

/-- **Joint A — universal packaging** (toy of `flowSubrangesOk_of_locators`, R243): the per-window
    locators *are* the universal target, field-for-field. -/
theorem jPack (toks : List Tok)
    (hLoc : ∀ lo hi, lo ≤ hi → hi < toks.length → toks[lo - 1]! = Tok.OB → Located toks lo hi) :
    Target toks := hLoc

/-- **Joint B — boundary-anchoring** (toy of `seqLocator_of_window_recseqbody`, R255): recover
    `2 ≤ lo` from the frame token `toks[0] = SS` (since `SS ≠ OB`), threading the *bounded* producer
    into the *unbounded* locator. -/
theorem jBound (toks : List Tok)
    (hSS : toks[0]! = Tok.SS)
    (hProd : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi < toks.length →
        toks[lo - 1]! = Tok.OB → Producer toks lo hi) :
    ∀ lo hi, lo ≤ hi → hi < toks.length → toks[lo - 1]! = Tok.OB → Located toks lo hi := by
  intro lo hi hle hhi hopen
  have hlo2 : 2 ≤ lo := by
    rcases Nat.lt_or_ge lo 2 with h | h
    · exfalso
      have h0 : lo - 1 = 0 := by omega
      rw [h0, hSS] at hopen
      exact absurd hopen (by decide)
    · exact h
  exact ⟨hProd lo hi hlo2 hle hhi hopen⟩

/-- **The R257 fold**: compose the whole chain into one lemma keyed *only* on the producer `hProd`
    (and the in-scope frame fact `hSS`).  Every consumer step downstream of the producer is composed
    here once; the only owed obligation left in the signature is `hProd` — the producer's contract. -/
theorem targetOfProducer (toks : List Tok)
    (hSS : toks[0]! = Tok.SS)
    (hProd : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi < toks.length →
        toks[lo - 1]! = Tok.OB → Producer toks lo hi) :
    Target toks :=
  jPack toks (jBound toks hSS hProd)

/-- The fold's payoff: an *arbitrary*-window `Located` now follows from the producer + frame alone —
    no per-window threading of the three joints at the call site. -/
theorem located_via_fold (toks : List Tok)
    (hSS : toks[0]! = Tok.SS)
    (hProd : ∀ lo hi, 2 ≤ lo → lo ≤ hi → hi < toks.length →
        toks[lo - 1]! = Tok.OB → Producer toks lo hi)
    (lo hi : Nat) (hle : lo ≤ hi) (hhi : hi < toks.length) (hopen : toks[lo - 1]! = Tok.OB) :
    Located toks lo hi :=
  targetOfProducer toks hSS hProd lo hi hle hhi hopen

/-! ### Positive witnesses — `good = [SS, OB, A, CB, SE]` -/

def good : List Tok := [Tok.SS, Tok.OB, Tok.A, Tok.CB, Tok.SE]

-- frame token present, opener at index 1, content window head:
#guard good[0]! == Tok.SS
#guard good[2 - 1]! == Tok.OB
#guard (win good 2 3) == [Tok.A]

/-- the producer holds at the one interior window — computes, no recursion needed for the leaf. -/
theorem prod_good : Producer good 2 3 := rfl

/-- the frame recovers the bound: the recovered `2 ≤ lo` at `lo = 2` is `2 ≤ 2`. -/
theorem bound_good : 2 ≤ 2 := by decide

/-! ### Negative witness — `bad = [OB, A, CB]` (no `SS` frame) -/

def bad : List Tok := [Tok.OB, Tok.A, Tok.CB]

-- the opener guard is satisfied at `lo = 1` (`bad[0]! = OB`) — the window the missing frame
-- token would have excluded — yet the bounded producer needs `2 ≤ 1`, which is false.
#guard bad[1 - 1]! == Tok.OB
#guard (bad[0]! == Tok.SS) == false
#guard decide (2 ≤ 1) == false

/-- without the `SS` frame, `jBound` could not have recovered the bound at this window. -/
theorem neg_no_ss : bad[0]! ≠ Tok.SS := by decide

end Tests.Reflections.FoldConsumerChain
