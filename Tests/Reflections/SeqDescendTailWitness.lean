/-! # Reflection 511 — the navigator's `descend_tail` edge consumes a depth-witness + a content fact,
        NOT the bare separator marker

R510 (`recseqbody_navigator_driver`) folded the width-recursion combinator + the assemble selector
into a driver that reduces the whole seq navigator to two named obligations, `locate` + `descend_tail`.
This reflection lands `descend_tail` (`recseqbody_seq_descend_tail`, extracted verbatim from the inline
ADVANCE block of `seqWindowRecSeqBody_seq_general`, R415) — and in doing so PROBES the obligation
([[ref-probe-deferred-universal-before-producing]], [[ref-minimal-pair-extracts-the-gate]]) and finds
the R510 driver's signature for it was **under-specified**.

**The finding.**  The driver typed `descend_tail` as `∀ lo hi m, G lo hi → lo < m → m < hi →
tokens[m] = .flowEntry → G (m+1) hi` — i.e. keyed on the bare separator marker `tokens[m] = .flowEntry`.
That is UNSOUND for the real token guard, for two independent reasons, each a counterexample the bare
marker cannot see:

* **A `.flowEntry` can sit at any bracket depth.**  A comma nested inside `[ … , … ]` is NOT a
  top-level separator; splitting the window there is garbage.  The descend genuinely needs the
  depth-`0` witness `flowBracketBalance tokens lo m = 0` (`h_bal_m`) — which `locate`/the dispatch
  DOES emit, but the driver's `locate` output dropped.
* **A depth-`0` `.flowEntry` at the last interior slot is a TRAILING comma.**  Its suffix `[m+1, hi)`
  is empty/degenerate (`m + 1 = hi`); the `.cons` it would feed has no body.  Ruling it out needs the
  current window's `FlowBodyContent` (`h_content`): `feContentStart` at `m` forces
  `isFlowContentStart tokens[m+1]`, but `tokens[hi] = .flowSequenceEnd` is not a content start, so
  `m + 1 ≠ hi`.  (The same `h_content` also discharges the re-scoped advance edge's
  `tokens[m+1] ≠ .key` premise.)

So the driver must be re-typed to thread `h_bal_m`, and the guard `G` it recurses on must carry the
window's content provider — which is exactly the carrier-free top-down-content obstacle of
[[ref-width-recursion-cannot-thread-topdown-fact]], now pinned to its precise entry point: the
`descend_tail` edge.  Note `h_content` is CONSUMED, not reproduced — the next window's content is
re-sourced from the carrier/navigator, so the descend outputs only the three structural guards
narrowed to the suffix (`FlowBodyWindow`, `FlowBodyContentDeepSeq`, `SeqEnclosed`) plus `m + 1 < hi`.

This demo (self-contained core Lean, no imports) isolates the finding over a tiny token/balance model:

* `marker_not_depth0` — a SEP nested in a bracket: the bare marker `l[m]? = some SEP` holds yet
  `bal l m ≠ 0`.  The marker does not pin depth-`0`.
* `depth0_marker_can_be_trailing` — a depth-`0` SEP at the last position: marker + `bal l m = 0` both
  hold, yet `m + 1 = l.length` (degenerate empty suffix).  Depth-`0` does not pin non-trailing.
* `WitnessedSep` — the bundle the descend REALLY needs (marker ∧ depth0 ∧ nonTrailing), the toy mirror
  of `recseqbody_seq_descend_tail`'s `(h_sep, h_bal_m, h_content)`.
* `Good` / `good_descend_tail` / `run_tail` — a FLAT body model (no brackets) where the two witnesses
  are automatic, so the descend is the trivial tail.  The flat model HIDES the obstacle precisely
  because it cannot express the two counterexamples — which is why the real, nesting-and-trailing-
  capable grammar must thread the witnesses the driver had dropped.  `witnessed_flat` exhibits the
  same index-1 SEP as a genuine `WitnessedSep` in a well-formed body, contrasting the counterexamples.

Axioms: `demo` depends on `[propext]` only; `run_tail` on none — no `sorryAx`, no `Classical.choice`
(the real `recseqbody_seq_descend_tail` carries `[propext, Classical.choice, Quot.sound]`, the
Classical inherited from the advance edges' WellTyped plumbing; the toy sheds it).
-/

namespace SeqDescendTailWitness

/-- Token alphabet: `0` = separator (comma), `1` = open bracket, `2` = close bracket, `≥ 3` = content. -/
abbrev Tok := Nat
def SEP : Tok := 0
def OPEN : Tok := 1
def CLOSE : Tok := 2

/-- Bracket-depth delta of a token (mirrors `flowBracketDelta`). -/
def delta : Tok → Int
  | 1 => 1
  | 2 => -1
  | _ => 0

/-- Depth (running balance) of the first `n` tokens (mirrors `flowBracketBalance tokens 0 n`).
    `bal l m = 0` ⇔ position `m` is at bracket depth `0`. -/
def bal (l : List Tok) (n : Nat) : Int := ((l.take n).map delta).sum

/-- **The descend trigger `descend_tail` REALLY needs at index `m`** — the bare marker, PLUS the
    depth-`0` witness, PLUS the non-trailing (content) witness.  Toy mirror of
    `recseqbody_seq_descend_tail`'s `(h_sep, h_bal_m, h_content)`. -/
structure WitnessedSep (l : List Tok) (m : Nat) : Prop where
  marker      : l[m]? = some SEP        -- the bare marker (all the naive R510 driver carried)
  depth0      : bal l m = 0             -- `h_bal_m` — rules out a NESTED separator
  nonTrailing : m + 1 < l.length        -- from `h_content` — rules out a TRAILING separator

-- ── (A) THE FINDING: the bare marker is an UNSOUND descend trigger. ──

/-- Counterexample 1 — a SEP NESTED inside a bracket sits at depth `1`, not a real separator.  The
    bare marker does NOT imply depth-`0`. -/
theorem marker_not_depth0 :
    ∃ (l : List Tok) (m : Nat), l[m]? = some SEP ∧ bal l m ≠ 0 :=
  ⟨[OPEN, SEP, CLOSE], 1, by decide, by decide⟩

/-- Counterexample 2 — a depth-`0` SEP at the LAST position is a trailing comma; its suffix
    `l.drop (m+1)` is EMPTY.  Depth-`0` does NOT imply non-trailing; a content fact is also required. -/
theorem depth0_marker_can_be_trailing :
    ∃ (l : List Tok) (m : Nat), l[m]? = some SEP ∧ bal l m = 0 ∧ m + 1 = l.length :=
  ⟨[3, SEP], 1, by decide, by decide, by decide⟩

-- ── (B) A flat body model where the witnesses are automatic: witnessed descend + run. ──

/-- A flat body (mirrors `RecSeqBody`): one-or-more single content atoms separated by single SEPs.
    Has NO brackets — so it cannot express either counterexample above. -/
inductive Good : List Tok → Prop where
  | one (a : Tok) (h : 3 ≤ a) : Good [a]
  | more (a : Tok) (rest : List Tok) (h : 3 ≤ a) (h_rest : Good rest) :
      Good (a :: SEP :: rest)

/-- The witnessed descend over the flat body: peeling the head atom + its SEP yields the suffix body.
    In the flat model the `WitnessedSep` facts at the split are automatic (no brackets ⇒ depth always
    `0`; `Good.more` guarantees a non-empty `rest`) — exactly what the counterexamples show the real
    nesting/trailing-capable model CANNOT assume, forcing the witnesses to be threaded. -/
theorem good_descend_tail (a : Tok) (rest : List Tok) (h_g : Good (a :: SEP :: rest)) :
    Good rest := by
  cases h_g with
  | more a' rest' h h_rest => exact h_rest

/-- The same index-`1` SEP that the counterexamples make pathological is a genuine `WitnessedSep` in a
    well-formed flat body `[5, SEP, 7]`. -/
theorem witnessed_flat : WitnessedSep [5, SEP, 7] 1 :=
  { marker := by decide, depth0 := by decide, nonTrailing := by decide }

/-- A RUN: descend the body `[5, SEP, 7]` past its depth-`0` separator to the suffix body `[7]`. -/
theorem run_tail : Good [7] :=
  good_descend_tail 5 [7] (Good.more 5 [7] (by decide) (Good.one 7 (by decide)))

/-- The demo deliverable: the bare marker is unsound on TWO counts (nested SEP, trailing SEP), the
    descend's real trigger is the three-fact `WitnessedSep` bundle, and with the witnesses the descend
    soundly narrows to the suffix body. -/
theorem demo :
    (∃ (l : List Tok) (m : Nat), l[m]? = some SEP ∧ bal l m ≠ 0)
    ∧ (∃ (l : List Tok) (m : Nat), l[m]? = some SEP ∧ bal l m = 0 ∧ m + 1 = l.length)
    ∧ WitnessedSep [5, SEP, 7] 1
    ∧ Good [7] :=
  ⟨marker_not_depth0, depth0_marker_can_be_trailing, witnessed_flat, run_tail⟩

end SeqDescendTailWitness
