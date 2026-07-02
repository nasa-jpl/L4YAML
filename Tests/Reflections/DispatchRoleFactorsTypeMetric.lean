/-!
# Reflection 383 — a search-recursion's FIXED N-arm dispatch assigns each arm a ROLE of
PRODUCE / REFUTE / VANISH, and for a SUM-TYPED head the role FACTORS as head-TYPE × head-METRIC

Self-contained core-Lean toy of L4YAML BRICK D's eight-cell `h_step` matrix (the four CONS cells
`nestedSeq_recseqentry_locate_{scalar,seqEmpty,seq,map}_cons_step`), capped by the map CONS cell.

A bottom-up locator's per-window step dispatches on a move trichotomy (LEAF / DESCEND / ADVANCE) AND
on the walking-body head's constructor (scalar / seqEmpty / seq / map). The naive reading is a 4×3
grid of bespoke cells; the real structure is one fixed three-arm SKELETON whose every cell takes one
of three ROLES, with the role a pure function of two INDEPENDENT scalars of the head:

* **head TYPE** decides PRODUCE-vs-REFUTE — does this constructor inhabit the seq deliverable? A
  `seq` head's LEAF/DESCEND PRODUCE; a `map` head's REFUTE (a map open breaks the seq enclosure).
* **head METRIC** (length) decides VANISH — a short head empties the middle (DESCEND) arm; the
  minimum collapses LEAF into the close boundary too.

So four constructors give four distinct dispatch SHAPES from ONE skeleton, reusing the SAME seams;
you assign a role per (type, metric) cell rather than re-deriving an architecture per constructor.
REFUTE ≠ VANISH: a refuted arm is REACHED (inhabited range) and killed by a structural brick; a
vanished arm never arrives (empty range, `omega`).
-/

namespace Tests.Reflections.DispatchRoleFactorsTypeMetric

set_option autoImplicit false

/-- The three dispositions an arm of a fixed-skeleton dispatch can take. -/
inductive Role where
  | produce   -- emit the deliverable / shrink to the IH (the genuine work)
  | refute    -- arm REACHED but contradicts the deliverable; killed by a structural brick
  | vanish    -- arm's index range is empty (or boundary-collapsed); the arm never runs
  deriving DecidableEq, Repr

/-- The walking-body head constructors, abstracted by the two scalars that drive the factorization:
    `inhabits` — does this head inhabit the seq deliverable? (TYPE axis: produce vs refute)
    `len`      — the head entry's length / metric (METRIC axis: drives VANISH). -/
inductive Head where
  | scalar    -- inhabits=false, len=1  (its LEAF collapses into the close boundary)
  | seqEmpty  -- inhabits=true,  len=2
  | seq       -- inhabits=true,  len≥3 (modeled as 3)
  | map       -- inhabits=false, len≥3 (modeled as 3)
  deriving DecidableEq, Repr

def Head.inhabits : Head → Bool
  | .scalar => false | .seqEmpty => true | .seq => true | .map => false

def Head.len : Head → Nat
  | .scalar => 1 | .seqEmpty => 2 | .seq => 3 | .map => 3

/-- The three arms of the move trichotomy. -/
inductive Arm where
  | leaf | descend | advance
  deriving DecidableEq, Repr

/-! ## The factorization — role = head-TYPE × head-METRIC, over a fixed arm skeleton.

METRIC (`len`) gates VANISH first; then TYPE (`inhabits`) splits PRODUCE vs REFUTE. ADVANCE always
produces (the IH-shrinking move). This is the WHOLE dispatch table — no per-constructor architecture. -/

def role (h : Head) (arm : Arm) : Role :=
  match arm with
  | .advance => .produce                         -- ADVANCE always produces (the shrink move)
  | .leaf =>
      if h.len == 1 then .vanish                 -- scalar: LEAF = the close boundary, never runs
      else if h.inhabits then .produce           -- seq / seqEmpty: located target IS a seq
      else .refute                               -- map: a map open breaks the seq enclosure
  | .descend =>
      if h.len ≤ 2 then .vanish                  -- scalar / seqEmpty: no interior sub-window
      else if h.inhabits then .produce           -- seq
      else .refute                               -- map

/-- POSITIVE — the role of every arm is a pure function of the two scalars `(inhabits, len)`, NOT of
    the constructor identity: any two heads agreeing on both scalars agree on every arm's role. This
    IS the factorization. -/
theorem role_factors (h1 h2 : Head) (arm : Arm)
    (h_inh : h1.inhabits = h2.inhabits) (h_len : h1.len = h2.len) :
    role h1 arm = role h2 arm := by
  cases arm <;> simp only [role, h_inh, h_len]

/-! ## The eight-cell matrix (CONS column) — four distinct SHAPES from one skeleton. -/

def shape (h : Head) : Role × Role × Role := (role h .leaf, role h .descend, role h .advance)

#guard decide (shape .scalar   = (.vanish,  .vanish,  .produce))   -- R380: LEAF=bnd, DESC ∅, ADV
#guard decide (shape .seqEmpty = (.produce, .vanish,  .produce))   -- R378: LEAF prod, DESC ∅, ADV
#guard decide (shape .seq      = (.produce, .produce, .produce))   -- R378: all produce/descend
#guard decide (shape .map      = (.refute,  .refute,  .produce))   -- R383: LEAF/DESC refute, ADV
-- four DISTINCT dispatch shapes from one three-arm skeleton
#guard decide (shape .scalar ≠ shape .map)
#guard decide (shape .seqEmpty ≠ shape .seq)

/-! ## REFUTE ≠ VANISH — the two require DIFFERENT proof obligations. -/

/-- NEGATIVE / VANISH — a VANISH arm's index range is EMPTY, so the dispatch never enters it and pure
    `omega` closes it. DESCEND for a short head (`len ≤ 2`): `off+1 < a < off+len` is unsatisfiable. -/
theorem vanish_range_empty (off len a : Nat) (h_short : len ≤ 2)
    (h_lo : off + 1 < a) (h_hi : a < off + len) : False := by omega

/-- POSITIVE / REFUTE — a REFUTE arm's index range is INHABITED, so the dispatch DOES enter it and
    needs a structural brick, not arithmetic. DESCEND for a long head (`len = 3`): `off+1 < a < off+3`
    has the witness `a = off+2`; the `omega` that closed VANISH would FAIL here (range nonempty). -/
theorem refute_range_inhabited (off : Nat) :
    off + 1 < off + 2 ∧ off + 2 < off + 3 := ⟨by omega, by omega⟩

/-- The per-head producing-arm count: scalar 1 (only ADVANCE), seqEmpty 2, seq 3, map 1 — the SHAPE
    varies, but the ADVANCE seam is shared by all four and never refutes/vanishes. -/
def producingArms (h : Head) : Nat :=
  [Arm.leaf, .descend, .advance].foldl
    (fun n arm => if role h arm = .produce then n + 1 else n) 0

#guard producingArms .scalar   == 1     -- only ADVANCE
#guard producingArms .seqEmpty == 2     -- LEAF + ADVANCE
#guard producingArms .seq      == 3     -- LEAF + DESCEND + ADVANCE
#guard producingArms .map      == 1     -- only ADVANCE (LEAF/DESCEND refuted)

end Tests.Reflections.DispatchRoleFactorsTypeMetric
