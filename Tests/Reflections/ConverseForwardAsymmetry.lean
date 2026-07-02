/-!
# Converse/forward invariant-asymmetry — runnable demonstration

A self-contained (core Lean, no `L4YAML` import) illustration of the proof-engineering principle
documented in `Blueprint/08-initiative-4-intrinsic-foundations.md`, Reflection 219: a property and
its **converse** over the same inductive structure can demand **different invariant strengths** —
the forward direction frequently needs a strictly *stronger* invariant to exclude a larger class of
false positives.

The structure here is a flow body: unit entries `e₁ , e₂ , … , eₙ` separated by depth-0 separators
(`,`). At every balance-0 boundary the token is either a *separator* or an entry's *last token* (a
value-end). These two readings are duals and share one induction skeleton, yet:

* **Converse / separator direction** (`sepChar`, real lemma `SafeBody_flowEntry_zero_balance`):
  needs only `EntrySafe` ("every interior separator is at balance ≥ 1"). To call a balance-0 `,` a
  separator you need only exclude it being nested inside a value.
* **Forward / value-end direction** (`valEndChar`, real lemma `SafeBodyUnit_succ`): needs the
  strictly stronger `EntryUnit` ("every *proper nonempty prefix* is at balance ≥ 1"). To call a
  balance-0 *non*-separator a value *end* you must also exclude it being an entry-*interior split* —
  a depth-0 position *inside* an entry, like the gap in `scalar scalar`.

The discriminating witness is the entry `s s` (two scalars, no separator): it is `EntrySafe` but
**not** `EntryUnit`. The body `bad = s s , s` built from it is a legitimate `EntrySafe` body on
which `sepChar` (converse) still holds — yet `valEndChar` (forward) is **false**. The same body, one
structure: the weaker invariant carries the converse but not the forward direction.

Run it: open in the IDE (the `#eval`s render in the infoview) or
`lake build Tests.Reflections.ConverseForwardAsymmetry` (the `#guard`s fail the build if any expectation is wrong).
-/

namespace ConverseForwardAsymmetry

/-- Toy tokens: opener `[`, closer `]`, separator `,`, scalar `s`. -/
inductive Tok | opn | cls | sep | scal
deriving DecidableEq, Repr

/-- Bracket delta: +1 open, −1 close, 0 otherwise. -/
def delta : Tok → Int
  | .opn => 1
  | .cls => -1
  | _    => 0

/-- Running bracket balance of the first `n` tokens (`pbalance (e.take n)` in the real proof). -/
def bal (e : List Tok) (n : Nat) : Int :=
  ((e.take n).map delta).foldl (· + ·) 0

/-! ## The two entry invariants — `EntrySafe` ⊋ `EntryUnit`.

Both demand the entry be balanced. They differ on the *interior*: `EntrySafe` only forbids a
separator at depth 0 (a separator inside the entry would split it), while `EntryUnit` forbids *any*
depth-0 interior position — making the entry a single indivisible unit (one scalar, or one matched
pair). `abbrev`, not `def`, so `decide` can synthesize the bounded-∀ `Decidable` instance. -/

/-- Weaker invariant: balanced, and every interior **separator** is nested (balance ≥ 1). The
    `i < e.length` bound leads so `decide` finds the `Nat.decidableBallLT` instance. -/
abbrev EntrySafe (e : List Tok) : Prop :=
  bal e e.length = 0 ∧ ∀ i, i < e.length → 0 < i → e[i]? = some .sep → bal e i ≥ 1

/-- Stronger invariant: balanced, and every proper nonempty prefix is at balance ≥ 1 (no depth-0
    interior position at all). -/
abbrev EntryUnit (e : List Tok) : Prop :=
  bal e e.length = 0 ∧ ∀ i, i < e.length → 0 < i → bal e i ≥ 1

/-- The discriminating entry: `s s` (scalar scalar, no separator). The gap after the first scalar is
    a depth-0 interior position — fine for `EntrySafe`, fatal for `EntryUnit`. -/
def ss : List Tok := [.scal, .scal]

-- `s s` satisfies the weaker invariant but NOT the stronger one. This single gap is the whole story.
#guard  decide (EntrySafe ss)   -- true  : no interior separator to be at depth 0
#guard !decide (EntryUnit ss)   -- false : `bal ss 1 = 0`, an interior depth-0 split

theorem ss_EntrySafe : EntrySafe ss := by decide
theorem ss_not_EntryUnit : ¬ EntryUnit ss := by decide

/-! ## The two body-level characterizations — the duals the real lemmas conclude.

`zeroBoundary ts j` marks a balance-0 boundary after position `j`. At such a boundary the token is
either a separator (→ `sepChar`: a new entry begins after it) or a value-end (→ `valEndChar`: the
body ends, or a separator follows). These are the conclusions of `SafeBody_flowEntry_zero_balance`
and `SafeBodyUnit_succ` respectively. -/

/-- `ts.take (j+1)` is balanced — position `j` sits on a top-level boundary. -/
abbrev zeroBoundary (ts : List Tok) (j : Nat) : Prop := bal ts (j + 1) = 0

/-- CONVERSE / separator direction (real: `SafeBody_flowEntry_zero_balance`). A balance-0 separator
    is genuine: a new entry begins right after it (in bounds, and not itself a separator). -/
abbrev sepChar (ts : List Tok) : Prop :=
  ∀ j, j < ts.length → ts[j]? = some .sep → zeroBoundary ts j →
    j + 1 < ts.length ∧ ts[j+1]? ≠ some .sep

/-- FORWARD / value-end direction (real: `SafeBodyUnit_succ`). A balance-0 *non*-separator is a
    value end: the body ends, or a separator follows. -/
abbrev valEndChar (ts : List Tok) : Prop :=
  ∀ j, j < ts.length → ts[j]? ≠ some .sep → zeroBoundary ts j →
    j + 1 = ts.length ∨ ts[j+1]? = some .sep

/-! ## Two bodies. `bad` is `EntrySafe` but not `EntryUnit`; `good` is `EntryUnit`. -/

/-- `s s , s` — entries `[s,s]` (EntrySafe, ¬EntryUnit) and `[s]`, joined by a top-level `,`. A
    legitimate `EntrySafe` body. -/
def bad : List Tok := [.scal, .scal, .sep, .scal]

/-- `s , s` — entries `[s]`, `[s]`, both `EntryUnit`. -/
def good : List Tok := [.scal, .sep, .scal]

/-! ## `#eval` — see the asymmetry. Per index `j`: token, `bal (j+1)`, boundary?, isSep?. -/

/-- One row of the diagnostic table for index `j` of `ts`. -/
def report (ts : List Tok) (j : Nat) : String :=
  s!"j={j}  tok={repr (ts.getD j .scal)}  bal(j+1)={bal ts (j+1)}  " ++
  s!"boundary={decide (zeroBoundary ts j)}  isSep={decide (ts[j]? = some .sep)}"

-- In `bad`, index 0 (first scalar) is a balance-0 boundary, NOT a separator, yet the next token is a
-- scalar — so the value-end claim is FALSE there. That row is the trap the converse never sees.
-- `#guard_msgs` pins each rendered table as checked documentation AND keeps it out of the build log;
-- a match is swallowed silently, any drift in a row fails the build with an error.
/-- info: ["j=0  tok=ConverseForwardAsymmetry.Tok.scal  bal(j+1)=0  boundary=true  isSep=false",
 "j=1  tok=ConverseForwardAsymmetry.Tok.scal  bal(j+1)=0  boundary=true  isSep=false",
 "j=2  tok=ConverseForwardAsymmetry.Tok.sep  bal(j+1)=0  boundary=true  isSep=true",
 "j=3  tok=ConverseForwardAsymmetry.Tok.scal  bal(j+1)=0  boundary=true  isSep=false"] -/
#guard_msgs in
#eval (List.range bad.length).map (report bad)

/-- info: "j=0  tok=ConverseForwardAsymmetry.Tok.scal  bal(j+1)=0  boundary=true  isSep=false" -/
#guard_msgs in
#eval report bad 0  -- the interior split: valEndChar fails here

/-- info: "j=2  tok=ConverseForwardAsymmetry.Tok.sep  bal(j+1)=0  boundary=true  isSep=true" -/
#guard_msgs in
#eval report bad 2  -- the real separator: sepChar's witness

/-! ## `#guard` — the asymmetry on one body, then the fix. -/

-- On `bad` (EntrySafe, ¬EntryUnit): the CONVERSE holds — `EntrySafe` already suffices for it.
#guard decide (sepChar bad)

-- …but the FORWARD direction is FALSE on the very same body. `EntrySafe` does NOT carry it.
#guard !decide (valEndChar bad)

-- On `good` (every entry `EntryUnit`): BOTH directions hold. The forward direction is recovered
-- exactly when the entries are units — the extra strength `EntryUnit` adds over `EntrySafe`.
#guard decide (sepChar good)
#guard decide (valEndChar good)

/-! ## The statements at work. -/

/-- The converse holds on `bad` under only the weaker invariant — a real (sorry-free) proof. -/
theorem sepChar_bad : sepChar bad := by decide

/-- The forward direction is genuinely FALSE on `bad`: no caller could ever supply it, despite `bad`
    being a perfectly good `EntrySafe` body. This is the asymmetry, made a theorem. -/
theorem valEndChar_bad_is_false : ¬ valEndChar bad := by decide

/-- Strengthen to `EntryUnit` entries (`good`) and the forward direction returns. -/
theorem valEndChar_good : valEndChar good := by decide

end ConverseForwardAsymmetry
