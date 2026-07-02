/-!
# Reflection 433 / 519 — endpoint+balance bracket guards admit cross-matched false windows

Self-contained (core Lean, no `L4YAML` import) toy of the R433 finding, extended (R519) with the MAP
twin and the **Dyck-dependence SPLIT** among a producer's per-window facts.

Context.  The flat per-window provider (`windowFacts`) and the consumer's `h_seq_rec` both quantify over
every window `[lo, hi)` gated by SEVEN bracket-shape facts: `2 ≤ lo`, `lo < hi`, `hi ≤ size-2`,
`hi < size`, `tokens[hi] = .flowSequenceEnd`, `flowBracketBalance lo hi = 0`, and
`tokens[lo-1] = .flowSequenceStart`.  The plan was to "supply the Dyck floor `h_win_dyck` once from
whole-stream well-bracketedness" — treating it as a restriction of a global fact.

The finding.  Those seven guards do NOT pin a MATCHED bracket pair, so the universal is UNSATISFIABLE.
`tokens[lo-1]` and `tokens[hi]` can close DIFFERENT brackets, with `balance lo hi = 0` holding only by
COINCIDENCE across a separator.  Machine-checked (R433, `seqWindowFacts_false_window`): `[[],[a]]` scans to
`streamStart, [, [, ], `,`, [, a, ], ], streamEnd`; the window `[3, 7)` satisfies all seven guards
(`tokens[2] = [`, `tokens[7] = ]`, `balance 3 7 = 0`) yet `balance 3 4 = -1` (its head is the FIRST
element's CLOSE `]`), so the Dyck floor underflows and `FlowBodyWindow` is FALSE.

The fix.  `h_win_dyck` is NOT a global-restriction primitive — it is the GUARD that DEFINES a genuine
window.  Add the Dyck floor `∀ i ∈ [lo, hi], balance lo i ≥ 0` as an extra guard: it EXCLUDES every
cross-matched false window and makes the floor a trivial pass-through.  This is the end-free-gate family —
an endpoint + total-balance gate underdetermines the matched pair; the interior floor is the discriminator.

The toy below models the body `[][a]` (`[ ] , [ a ]`) and exhibits the cross-matched window `[1, 5)`:
endpoint + total-balance guards hold, but the floor underflows at the first step — and the Floor guard
rejects it.
-/

namespace Tests.Reflections.BracketGuardsAdmitCrossMatched

set_option autoImplicit false

/-- Toy bracket-delta: open `1 ↦ +1`, close `2 ↦ -1`, separator/content neutral. -/
def delta : Nat → Int
  | 1 => 1
  | 2 => -1
  | _ => 0

/-- Balance over `[a, b)` (mirror of `flowBracketBalance tokens a b`). -/
def bal (toks : List Nat) (a b : Nat) : Int := (((toks.take b).drop a).map delta).sum

/-- The body of `[[],[a]]`: `[ ] , [ a ]` — an empty seq, a separator, then a singleton seq.
    Indices: 0=`[` 1=`]` 2=`,` 3=`[` 4=`a` 5=`]`. -/
def toks : List Nat := [1, 2, 3, 1, 4, 2]

/-! ## The cross-matched window `[1, 5)` — endpoint + total balance hold, floor underflows. -/

-- `tokens[lo-1]` is an opener and `tokens[hi]` is a closer and the window balances to `0`:
#guard toks[0]! == 1            -- toks[lo-1] = `[`
#guard toks[5]! == 2            -- toks[hi]   = `]`
#guard (bal toks 1 5 == 0)      -- the window balances
-- yet the floor underflows at the very first step (the window head `toks[1]` is a CLOSE):
#guard (bal toks 1 2 == -1)     -- balance dips below 0 ⇒ NOT a matched-pair interior

/-- **Endpoint + total-balance do NOT imply the floor** — the four facts coexist, so the seven-guard
    universal cannot derive `FlowBodyWindow`'s Dyck floor. -/
theorem guards_dont_imply_floor :
    toks[0]! = 1 ∧ toks[5]! = 2 ∧ bal toks 1 5 = 0 ∧ bal toks 1 2 = -1 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

/-- The Dyck floor over `[lo, hi)` (mirror of `FlowBodyWindow.dyck`). -/
def Floor (toks : List Nat) (lo hi : Nat) : Prop := ∀ i, lo ≤ i → i ≤ hi → bal toks lo i ≥ 0

/-- **The fix: the Floor guard REJECTS the cross-matched false window.**  So adding the floor as an extra
    guard excludes `[1, 5)` (and every cross-matched window), restoring satisfiability. -/
theorem false_window_fails_floor : ¬ Floor toks 1 5 := by
  intro hF
  have hd := hF 2 (by omega) (by omega)   -- bal toks 1 2 ≥ 0
  exact absurd hd (by decide)             -- but bal toks 1 2 = -1

/-! ## R519 — the MAP twin, and the Dyck-dependence SPLIT among the producer's facts

The same cross-matched defect breaks the MAP grammar producers (`flowSubrangesOk_of_window_producers`'s
six `h_key_content` … `h_value_bracket_succ`), which carry the SEVEN guards but NOT the Dyck floor.  But
the breakage is NOT uniform — it SPLITS by fact kind:

* the CONTENT-START successor facts (`h_key_content`/`h_value_content`) are Dyck-INDEPENDENT — they hold
  even on a cross-matched window (their conclusion is an emitter-global property of every `.key`/`.value`,
  and `k+1 < hi` is forced by the `.flowMappingEnd` closer);
* the BOUNDARY-referencing successor facts (`h_value_scalar_succ`, …, which name `hi` via `k+2 = hi`) are
  Dyck-DEPENDENT — they are FALSE on a cross-matched window, because the next token is an INNER close `}`
  that is not THIS window's `hi`.

Machine-checked in the library by `mapGrammarFacts_false_window` (`native_decide` on
`{a: {b: c}, d: {e: f}}`, window `[6, 20)`).  The toy below reproduces that window: at the depth-`0`
value `k = 8`, the content-start fact HOLDS but the value-scalar-successor fact FAILS, and the Floor guard
rejects the window — so the single fix (add the Dyck floor as a guard) is what restores ALL six facts. -/

/-- The filtered scan of `{a: {b: c}, d: {e: f}}` as toy codes
    (`0`=stream, `1`=`{`, `2`=`}`, `3`=KEY, `4`=VAL, `5`=scalar, `6`=`,`):

      0:SS 1:{ 2:KEY 3:a 4:VAL 5:{ 6:KEY 7:b 8:VAL 9:c 10:} 11:, 12:KEY 13:d 14:VAL 15:{ 16:KEY 17:e 18:VAL 19:f 20:} 21:} 22:SE -/
def toks2 : List Nat :=
  [0, 1, 3, 5, 4, 1, 3, 5, 4, 5, 2, 6, 3, 5, 4, 1, 3, 5, 4, 5, 2, 2, 0]

def isVal (c : Nat) : Bool := c == 4
def isScalar (c : Nat) : Bool := c == 5
def isComma (c : Nat) : Bool := c == 6
def isMapClose (c : Nat) : Bool := c == 2
def isContentStart (c : Nat) : Bool := c == 5 || c == 1   -- scalar or `{`

/-- Dyck-INDEPENDENT fact (`h_value_content`-shaped): a depth-`0` value has an in-window content-start
    successor.  No reference to the window's close `hi` beyond the forced `k+1 < hi`. -/
def csFact (lo hi k : Nat) : Bool :=
  !(bal toks2 lo k == 0 && isVal toks2[k]!)
    || (decide (k + 1 < hi) && isContentStart toks2[k+1]!)

/-- Dyck-DEPENDENT fact (`h_value_scalar_succ`-shaped): a depth-`0` scalar-valued position is followed by
    a `,` separator OR the window's OWN close (`k+2 = hi`) — it NAMES the boundary `hi`. -/
def vsFact (lo hi k : Nat) : Bool :=
  !(bal toks2 lo k == 0 && isVal toks2[k]! && isScalar toks2[k+1]!)
    || (decide (k + 2 ≤ hi)
        && (isComma toks2[k+2]! || (isMapClose toks2[k+2]! && decide (k + 2 = hi))))

-- the cross-matched window `[6, 20)`: opener at 5, closer at 20, balances, floor underflows at i=11
#guard toks2[5]! == 1
#guard toks2[20]! == 2
#guard bal toks2 6 20 == 0
#guard bal toks2 6 11 == -1
#guard csFact 6 20 8        -- Dyck-independent: HOLDS on the cross-matched window
#guard !vsFact 6 20 8       -- Dyck-dependent: FAILS on the cross-matched window

/-- **The Dyck-dependence SPLIT** — at the depth-`0` value `k = 8` of the cross-matched window `[6, 20)`,
    the content-start fact HOLDS but the value-scalar-successor fact FAILS. -/
theorem split_at_crossmatched :
    csFact 6 20 8 = true ∧ vsFact 6 20 8 = false := by decide

/-- The Floor guard rejects the cross-matched MAP window — so adding it restores ALL six facts at once. -/
theorem map_false_window_fails_floor : ¬ Floor toks2 6 20 := by
  intro hF
  have hd := hF 11 (by omega) (by omega)   -- bal toks2 6 11 ≥ 0
  exact absurd hd (by decide)              -- but bal toks2 6 11 = -1

end Tests.Reflections.BracketGuardsAdmitCrossMatched
