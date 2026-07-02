/-!
# Reflection 297 — probe a gated universal as a MINIMAL PAIR; the gate is read off, not invented

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind the
`BodySuccSeqDiscriminator` probe: when a deferred `∀`-over-sub-windows is FALSE in general but you
suspect a gate rescues it, do not probe a single (holding) instance — that only confirms what you
hoped.  Probe a **minimal pair inside one concrete object**: one window that HOLDS the property and a
sibling that FAILS it.  The probe then does triple duty —

* confirms the gate is **sufficient** (the holding window),
* proves the gate is **necessary** (the failing sibling — the gate is not decorative), and
* **names** the gate as the existing computation that SEPARATES the pair (here a typed-stack top),
  so the discriminator predicate is read off the pair, not invented.

The object: `[ { k : v } , x ]` (`stream` below) — a sequence holding a mapping AND a scalar, so one
token stream contains a seq-typed interior `[1,8)` and a map-typed interior `[2,5)`.  `succHolds`
(toy of `bodySucc`) holds on the seq interior and fails on the map interior; `enclosingMark` (toy of
`WellTyped`/`btFold`'s stack top: `seqOpen ↦ true`, `mapOpen ↦ false`) is the structural feature that
differs between them — the gate.
-/

namespace Tests.Reflections.MinimalPairExtractsTheGate

set_option autoImplicit false

/-- Toy token alphabet with DISTINCT seq/map brackets (so the typed stack can tell them apart) and
    a `colon` value-separator (the map analogue of the `value` token that breaks `bodySucc`). -/
inductive Tok | seqOpen | seqClose | mapOpen | mapClose | comma | colon | scal
  deriving DecidableEq, Repr, Inhabited

/-- Bracket delta: any opener `+1`, any closer `-1`, content `0`. -/
def delta : Tok → Int
  | .seqOpen | .mapOpen => 1
  | .seqClose | .mapClose => -1
  | _ => 0

/-- The minimal pair `[ { k : v } , x ]` as an indexed stream. -/
def tok : Nat → Tok
  | 0 => .seqOpen   -- `[`  opener of seq window [1,8)
  | 1 => .mapOpen   -- `{`  opener of map window [2,5)
  | 2 => .scal      -- `k`
  | 3 => .colon     -- `:`  (map separator — NOT a comma)
  | 4 => .scal      -- `v`
  | 5 => .mapClose  -- `}`
  | 6 => .comma     -- `,`  (seq separator)
  | 7 => .scal      -- `x`
  | 8 => .seqClose  -- `]`
  | _ => .seqClose

/-- Prefix balance from `0` to `m`. -/
def balAux : Nat → Int
  | 0       => 0
  | (m + 1) => balAux m + delta (tok m)

/-- Window balance from `lo` to `m` as a prefix difference. -/
def bal (lo m : Nat) : Int := balAux m - balAux lo

/-- Toy of `bodySucc` over window `[lo,hi)`: at every depth-`0` balanced-prefix end that is not a
    `comma`, the window must either end (`k+1 = hi`) or be followed by a `comma` separator. -/
def succHolds (lo hi : Nat) : Bool :=
  (List.range hi).all fun k =>
    if lo ≤ k ∧ k < hi then
      if bal lo (k + 1) = 0 ∧ tok k ≠ .comma then
        decide (k + 1 = hi) || decide (tok (k + 1) = .comma)
      else true
    else true

/-! ## The gate: a typed-stack top that already distinguishes seq from map -/

/-- Toy of `WellTyped`/`btStep`: seq opener pushes `true`, map opener pushes `false`, any closer pops. -/
def stStep : Tok → List Bool → Option (List Bool)
  | .seqOpen, s => some (true :: s)
  | .mapOpen, s => some (false :: s)
  | .seqClose, (_ :: s) => some s
  | .mapClose, (_ :: s) => some s
  | .seqClose, [] => none
  | .mapClose, [] => none
  | _, s => some s

/-- Fold the typed stack over a token list. -/
def stFold (s0 : Option (List Bool)) : List Tok → Option (List Bool)
  | []      => s0
  | t :: ts => stFold (s0.bind (stStep t)) ts

/-- The enclosing-bracket mark of the window whose opener is at index `opener`: the head of the typed
    stack after consuming `[0, opener]`.  `true` = sequence, `false` = mapping. -/
def enclosingMark (opener : Nat) : Option Bool :=
  (stFold (some []) ((List.range (opener + 1)).map tok)).bind (·.head?)

/-! ## POSITIVE — the seq interior HOLDS, and the gate classifies it `true` (sufficient) -/

theorem seq_window_holds : succHolds 1 8 = true := by decide
theorem seq_window_is_seq_typed : enclosingMark 0 = some true := by decide

/-! ## NEGATIVE — the map interior FAILS, and the gate classifies it `false` (necessary) -/

theorem map_window_fails : succHolds 2 5 = false := by decide
theorem map_window_is_map_typed : enclosingMark 1 = some false := by decide

-- The balances that drive the pair: the seq window's depth-0 ends are the comma (k=6) and the last
-- scalar (k=7); the map window's depth-0 end at the key (k=2) is followed by `colon`, not `comma`.
#guard bal 1 7 == 0          -- seq window: comma at k=6 is a depth-0 end
#guard bal 1 8 == 0          -- seq window: last scalar at k=7 is a depth-0 end
#guard bal 2 3 == 0          -- map window: the key at k=2 is a depth-0 end…
#guard decide (tok 3 = Tok.comma) == false   -- …but is followed by `colon`, not a separator
#guard succHolds 1 8         -- positive
#guard !succHolds 2 5        -- negative
#guard enclosingMark 0 == some true
#guard enclosingMark 1 == some false

end Tests.Reflections.MinimalPairExtractsTheGate
