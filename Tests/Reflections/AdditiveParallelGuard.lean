/-
# Reflection 289 — a too-weak shared guard's missing content is its own additive parallel guard

Self-contained, `L4YAML`-free runnable illustration of the proof-engineering principle in Blueprint
Reflection 289, the guard-layer instance of `ref-additive-parallel-type-over-shared-edit` (and the
content-half companion of `ref-guard-threading-skeleton-before-grammar`).

**The principle.** The metric-recursion's per-window `step` threads a shared guard `FlowBodyWindow`
carrying the BRACKET facts (balance / dyck / WellTyped).  When the grammar core needs to read the head
SHAPE, that guard turns out **provably too weak**: a window headed by a depth-`0` separator (or a
stray) is *still* balanced + dyck + WellTyped, so "the head is a content-start token" — the very thing
the four-way dispatch branches on — does NOT follow.  The dyck floor only forbids a leading *closer*
(which would push the prefix balance to `−1`); it admits a leading separator.

The fix is NOT to strengthen the shared guard in place (that re-touches every landed edge lemma).  It
is to name the missing CONTENT as its own **additive parallel guard** `FlowBodyContent` — defined to be
exactly what the existing consumer (`seqBodyProps_assemble`) already eats — and prove its cheap
(ADVANCE) edge now, leaving the recursive (DESCEND) edge as the isolated residual.

**What this demo asserts (fails the build if it ever drifts):**
  * NEGATIVE — the bracket guard is too weak: `dyck_excludes_closer` shows the guard's dyck floor DOES
    forbid a leading closer (`tokDelta (hd lo) ≥ 0`), but `separator_head_passes_dyck` +
    `separator_head_not_contentstart` show a separator head passes the same floor while NOT being
    content-start; `bracketwin_sep_head` exhibits a whole window satisfying the bracket guard whose head
    (`sep_head_not_cs`) is not content-start.  So "content-start head" is not a function of the guard.
  * POSITIVE — the parallel content guard re-seats the head across ADVANCE: `content_advance` (toy of
    `flowBodyContent_advance`) transports `ContentWin` to the tail by pure re-basing, the tail head
    recovered from `feContentStart` at the separator.  `content_window_good` / `content_advance_good`
    fire it concretely, re-seating `hdGood 0 = scal` to `hdGood 2 = scal` across the separator at `1`.
  * NEGATIVE — `feContentStart` is load-bearing: `not_contentwin_bad` shows an "empty entry" body
    (`scal sep sep scal`) is NOT a `ContentWin`, because the separator at `1` is followed by another
    separator, not a content-start head — exactly the field whose failure would break ADVANCE re-seating.
-/
set_option autoImplicit false

namespace Tests.Reflections.AdditiveParallelGuard

/-! ## The toy token stream and its bracket delta -/

/-- A toy flow token: a content scalar, a body separator, or a bracket opener / closer. -/
inductive Tok | scal | sep | opn | cls
  deriving DecidableEq

/-- Toy of `flowBracketDelta`: openers `+1`, closers `−1`, content/separators `0`. -/
def tokDelta : Tok → Int
  | .opn => 1
  | .cls => -1
  | _ => 0

/-- Toy of `isFlowContentStart`: a head that begins a content entry (scalar or an opener). -/
def isContentStart (t : Tok) : Prop := t = .scal ∨ t = .opn

instance : DecidablePred isContentStart := fun t =>
  decidable_of_iff (t = .scal ∨ t = .opn) Iff.rfl

/-- `bal f a b` — the running depth change over `[a, b)`, with `f i` the cumulative depth after `i`
    tokens (toy of `flowBracketBalance`); re-basing across a split point is plain subtraction. -/
def bal (f : Nat → Int) (a b : Nat) : Int := f b - f a

/-! ## The two parallel guards — brackets (too weak) and content (the missing piece)

`BracketWin` is the toy of `FlowBodyWindow`: it carries ONLY the bracket facts (balanced + dyck).
`ContentWin` is the toy of `FlowBodyContent`: the content the head-shape dispatch actually needs —
the head is content-start (`headContentStart`) and every depth-`0` separator is followed by a
content-start head (`feContentStart`, "no empty entries"). -/

/-- Toy of `FlowBodyWindow` — bracket facts only: the window is balanced and dyck-nonnegative. -/
def BracketWin (f : Nat → Int) (lo hi : Nat) : Prop :=
  bal f lo hi = 0 ∧ (∀ i, lo ≤ i → i ≤ hi → bal f lo i ≥ 0)

/-- Toy of `FlowBodyContent` — the content the bracket guard cannot supply. -/
def ContentWin (f : Nat → Int) (hd : Nat → Tok) (lo hi : Nat) : Prop :=
  isContentStart (hd lo) ∧
  (∀ k, lo ≤ k → k < hi → hd k = .sep → bal f lo k = 0 → isContentStart (hd (k + 1)))

/-! ## NEGATIVE — the bracket guard is provably too weak for the head shape

The dyck floor bounds the head from BELOW (no leading closer) but cannot reach "content-start": a
separator head clears the same floor. -/

/-- The dyck floor DOES exclude a leading closer: a `BracketWin` head has `tokDelta ≥ 0`.  (This is the
    one head-bound the bracket guard genuinely delivers — and all it delivers.)  The toy of "the dyck
    floor excludes a leading `]`/`}`". -/
theorem dyck_excludes_closer (f : Nat → Int) (hd : Nat → Tok) (lo hi : Nat)
    (h_delta : ∀ i, bal f i (i + 1) = tokDelta (hd i))
    (h_bw : BracketWin f lo hi) (h_lo_hi : lo < hi) :
    tokDelta (hd lo) ≥ 0 := by
  obtain ⟨_, h_dyck⟩ := h_bw
  have hbal : bal f lo (lo + 1) ≥ 0 := h_dyck (lo + 1) (Nat.le_succ lo) (by omega)
  -- and `bal f lo (lo+1) = tokDelta (hd lo)` — the head delta IS the first prefix step.
  rw [h_delta lo] at hbal
  exact hbal

/-- A leading CLOSER is genuinely excluded by the floor (`−1 ≥ 0` is false). -/
theorem closer_delta_neg : ¬ (tokDelta .cls ≥ 0) := by decide

/-- But a leading SEPARATOR clears the exact same floor (`0 ≥ 0`). -/
theorem separator_head_passes_dyck : tokDelta .sep ≥ 0 := by decide

/-- …yet a separator head is NOT a content-start.  So "content-start head" is not derivable from the
    bracket guard: the floor admits the separator the dispatch must reject. -/
theorem separator_head_not_contentstart : ¬ isContentStart .sep := by
  rintro (h | h) <;> exact absurd h (by decide)

/-- A constant-separator body — every token a depth-`0` separator (delta `0`), so `f` is flat. -/
def f0 : Nat → Int := fun _ => 0

@[simp] theorem bal_f0 (a b : Nat) : bal f0 a b = 0 := by simp [bal, f0]

def hdSep : Nat → Tok := fun _ => .sep

/-- A WHOLE window satisfying the bracket guard — balanced and dyck-nonnegative everywhere… -/
theorem bracketwin_sep_head : BracketWin f0 0 3 := by
  refine ⟨bal_f0 0 3, ?_⟩
  intro i _ _; rw [bal_f0]; omega

/-- …whose head is a separator, NOT a content-start.  The bracket guard cannot tell this window's head
    apart from a content-headed one — the precise sense in which it is too weak. -/
theorem sep_head_not_cs : ¬ isContentStart (hdSep 0) := by
  rintro (h | h) <;> exact absurd h (by decide)

/-! ## POSITIVE — the parallel content guard re-seats the head across the ADVANCE edge

`content_advance` is the toy of `flowBodyContent_advance`: transport `ContentWin` from `[lo, hi)` to
the tail `[m+1, hi)` after a depth-`0` separator `m`.  Pure re-basing — the tail's `headContentStart`
IS `feContentStart` applied at `m` (the field whose whole purpose is to re-seat the head one entry
along), and the tail's `feContentStart` is the outer one with its balance premise re-based to `lo`. -/

/-- **ADVANCE content-preservation** (toy of `flowBodyContent_advance`). -/
theorem content_advance (f : Nat → Int) (hd : Nat → Tok) (lo m hi : Nat)
    (h_delta : ∀ i, bal f i (i + 1) = tokDelta (hd i))
    (h_cw : ContentWin f hd lo hi)
    (h_lo_m : lo ≤ m) (h_m1_hi : m + 1 < hi)
    (h_m_bal : bal f lo m = 0) (h_sep : hd m = .sep) :
    ContentWin f hd (m + 1) hi := by
  obtain ⟨_h_head, h_fe⟩ := h_cw
  have h_m_hi : m < hi := by omega
  -- The separator has delta `0`, so the prefix `bal lo (m+1)` is still `0`.
  have h_sep_delta : bal f m (m + 1) = 0 := by rw [h_delta m, h_sep]; rfl
  have h_m1_bal : bal f lo (m + 1) = 0 := by unfold bal at h_m_bal h_sep_delta ⊢; omega
  refine ⟨?_, ?_⟩
  · -- head content-start on the tail: the separator `m` is followed by a content-start (no empty entry).
    exact h_fe m h_lo_m h_m_hi h_sep h_m_bal
  · -- feContentStart on the tail: re-base `bal (m+1) k` to the outer origin, then apply the outer field.
    intro k hk1 hk2 hsep hbal
    have hbal' : bal f lo k = 0 := by unfold bal at h_m1_bal hbal ⊢; omega
    exact h_fe k (by omega) hk2 hsep hbal'

/-! ### A concrete body — `scal sep scal` — the head re-seats across the separator -/

/-- `hdGood i = scal` except the separator at `i = 1`: the body `scal , scal`. -/
def hdGood : Nat → Tok := fun i => if i = 1 then .sep else .scal

theorem h_delta_good (i : Nat) : bal f0 i (i + 1) = tokDelta (hdGood i) := by
  rw [bal_f0]; unfold hdGood; split <;> rfl

/-- The body is a `ContentWin`: head `scal` is content-start, and the only separator (at `1`) is
    followed by a content-start head (`hdGood 2 = scal`). -/
theorem content_window_good : ContentWin f0 hdGood 0 3 := by
  refine ⟨by decide, ?_⟩
  intro k _ hk3 hsep _
  match k with
  | 0 => exact absurd hsep (by decide)
  | 1 => exact (by decide : isContentStart (hdGood 2))
  | 2 => exact absurd hsep (by decide)
  | _ + 3 => omega

/-- `content_advance` fires: the tail `[2, 3)` after the separator at `1` is still a `ContentWin`, its
    head re-seated to `hdGood 2 = scal` (content-start) by `feContentStart` — the ADVANCE edge landed. -/
theorem content_advance_good : ContentWin f0 hdGood 2 3 :=
  content_advance f0 hdGood 0 1 3 h_delta_good content_window_good
    (by omega) (by omega) (by decide) (by decide)

-- Re-seating, concretely: head `scal` at `0`, separator at `1`, head `scal` again at `2`.
#guard hdGood 0 = Tok.scal
#guard hdGood 1 = Tok.sep
#guard hdGood 2 = Tok.scal

/-! ### NEGATIVE — `feContentStart` is load-bearing: an "empty entry" breaks the content guard -/

/-- `hdBad` = `scal sep sep scal`: a doubled separator (an empty entry) at positions `1, 2`. -/
def hdBad : Nat → Tok := fun i => if i = 1 ∨ i = 2 then .sep else .scal

/-- The empty-entry body is NOT a `ContentWin`: the separator at `1` is followed by ANOTHER separator,
    not a content-start head — so `feContentStart` fails.  This is exactly the field whose truth makes
    ADVANCE re-seating possible; without it (here) the tail head would be a separator. -/
theorem not_contentwin_bad : ¬ ContentWin f0 hdBad 0 4 := by
  rintro ⟨_, hfe⟩
  have hcs : isContentStart (hdBad 2) :=
    hfe 1 (by omega) (by omega) (by decide) (by decide)
  rcases hcs with h | h <;> exact absurd h (by decide)

end Tests.Reflections.AdditiveParallelGuard
