/-!
# Reflection 355 — a position-navigator's per-arm exclusion facts live at DIFFERENT positions

Self-contained (core Lean, no `L4YAML` import) toy model of the R355 finding: a navigator that walks a
recursive structure discharges its arms with facts keyed to DIFFERENT positions — the DESCEND arm's
*domain* at the recursion BASE, the LEAF arm's *classification* at the TARGET WINDOW.  A single carried
invariant at the base does NOT discharge an arm whose obligation lives at the window; that arm must
CONSUME a separate fact about the window.  Don't assume one carried hypothesis closes every arm — locate
each arm's exclusion at ITS position and check whether the carried state even reaches it.

THE SETTING.  A bracket stack is a `List Bool` (head = top; `true` = enclosed by a seq `[`, `false` = by
a map `{`).  A navigator over a recursive seq body is parked at base offset `off` with the PATH stack
`pathStack` (the stack BEFORE `off`).  Its head entry's own opener pushes onto that path to form the
stack at the TARGET window start `a = off+1`:
* a seq head opener `[` pushes `true`  →  window stack `true  :: pathStack`;
* a map head opener `{` pushes `false` →  window stack `false :: pathStack`.

The carried DOMAIN hypothesis `SeqPathAllSeq tokens off` is `allTrue pathStack` — about the PATH, BLIND
to the head opener.  The LEAF arm must reject a map head; that needs `SeqEnclosed tokens a`, the TOP of
the WINDOW stack — the push of the head opener the path stack never saw.

THE TRANSFERABLE RULE.  A position-walking navigator's correctness obligations are keyed to distinct
positions (recursion base vs target window).  A carried base invariant cannot decide a window-local
classification it is blind to; the navigator must additionally CONSUME the window's own fact.
-/

namespace Tests.Reflections.NavigatorArmsKeyedToPositions

set_option autoImplicit false

/-! ## The two projections, at two positions -/

/-- `SeqEnclosed`-style TOP-of-stack projection — the immediate enclosure (the window's `a`). -/
def topTrue : List Bool → Bool
  | b :: _ => b
  | []     => false

/-- `SeqPathAllSeq`-style WHOLE-path projection — every frame a seq (the base's `off`). -/
def allTrue (s : List Bool) : Bool := !s.isEmpty && s.all (· == true)

/-- The PATH stack at the navigator's base `off` (here: the lone root `[`). -/
def pathStack : List Bool := [true]

/-- The window stack at `a = off+1` when the head entry's opener is a SEQ `[` (pushes `true`). -/
def seqHeadWindow : List Bool := true :: pathStack

/-- The window stack at `a = off+1` when the head entry's opener is a MAP `{` (pushes `false`). -/
def mapHeadWindow : List Bool := false :: pathStack

/-! ## The carried base domain is the SAME for both heads — it is blind to the head opener -/

/-- **The carried base domain `SeqPathAllSeq tokens off` HOLDS, identically, whichever head follows.**
    Both window stacks are built by pushing onto this same `pathStack`; the carried domain is computed
    on the PATH, before the head opener, so it cannot depend on the head type. -/
theorem carried_domain_blind_to_head :
    allTrue pathStack = true ∧
    seqHeadWindow.tail = pathStack ∧ mapHeadWindow.tail = pathStack := ⟨rfl, rfl, rfl⟩

/-! ## The LEAF arm's window enclosure SEPARATES the two heads -/

/-- **POSITIVE (seq head) — the window enclosure HOLDS** (leaf admissible). -/
theorem seq_head_window_enclosed : topTrue seqHeadWindow = true := rfl

/-- **NEGATIVE (map head) — the window enclosure FAILS** (leaf inadmissible: a `RecSeqEntry.map` has no
    recursive body and the deliverable demands a seq opener). -/
theorem map_head_window_not_enclosed : topTrue mapHeadWindow = false := rfl

/-! ## The minimal pair: carried base domain EQUAL, window enclosure SEPARATES -/

/-- **THE DISCRIMINATOR — the carried base domain is EQUAL across the pair (so a navigator carrying ONLY
    it cannot exclude the map-headed leaf), while the window enclosure DIFFERS (so it is the necessary
    LEAF-arm discriminator, keyed to the target window, not the base).** -/
theorem base_equal_window_separates :
    allTrue pathStack = allTrue pathStack ∧ topTrue seqHeadWindow ≠ topTrue mapHeadWindow := by
  refine ⟨rfl, ?_⟩; decide

/-- **The carried base domain CANNOT decide the head type** — there exist two window stacks (seq-head and
    map-head) with the SAME carried base domain but OPPOSITE window enclosures.  So no function of
    `allTrue pathStack` alone classifies the head; the navigator must consume the window's own
    `topTrue`. -/
theorem carried_domain_cannot_classify_head :
    allTrue seqHeadWindow.tail = allTrue mapHeadWindow.tail ∧
    topTrue seqHeadWindow ≠ topTrue mapHeadWindow := by
  refine ⟨rfl, ?_⟩; decide

end Tests.Reflections.NavigatorArmsKeyedToPositions
