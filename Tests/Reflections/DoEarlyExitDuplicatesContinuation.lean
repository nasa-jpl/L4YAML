module


@[expose] public section Blanket

/-!
# Reflection 613 — a `do`-block guard costs a join-point layer, so count guards, not logic

A statement-style early-exit guard inside a `do` block —

```lean
if cond then throw e
<rest of the block>
```

— does not elaborate to an `ite` over `<rest>`. Lean wraps the continuation in a
**join point**, `have __do_jp := fun __r => <rest>`, and branches to it from both
sides. One guard, one layer. A *second* consecutive guard nests a second layer
**around the first**, and so on.

That nesting is what proofs are coupled to, and the coupling is invisible in the
source. Three consequences, all demonstrated below:

1. **`split at h` splits the wrong condition.** On the two-guard shape it
   descends into the join-point body and splits the *inner* guard first, leaving
   `h` textually unchanged — so the script's next step (`exact h`, or a
   per-arm closer) has nothing to fire on. It does not error; it silently
   produces goals the script did not anticipate.
2. **`simp` normalizing the hypothesis duplicates the continuation.** Zeta-expanding
   a layer inlines `<rest>` at *both* branch references, so k layers yield 2^k
   copies. With a real dispatcher arm that is how `split`'s internal `simp`
   reaches *maximum number of steps exceeded* — a **size** failure, distinct
   from the *opacity* failure the same construct causes when `rw [if_pos]` or
   `split` simply cannot see the arm (DOCS item 9a).
3. **The fix is not "convert to an `else` chain".** That re-shapes the arm, so
   every downstream script written against the old shape breaks too. The fix is
   to add **zero** new guards: fold the new rejection into the existing one via a
   helper returning `Option Err`, checked with `if let some e := … then throw e`.
   One layer in, one layer out — `invert_merged` below is the *same script* as
   `invert_one`, unchanged. **§1's ★ block is the idiom to copy**, and names its
   three parts: `preErr`, `merged`, and an `invert_merged` that needed no work.

So before adding a guard to a `do`-block dispatcher that proofs case-split on,
count the `if`s in the arm. That count, not the guard's logic, is the interface.

## Why this file is a canary

The facts above are **elaborator behaviour**, not theorems. They are true of Lean
4.32.0 and may change. L4YAML's scanner-inversion proofs — every
`unfold scanNextToken_dispatch* at h; split at h` walk — depend on them, so a
silent change would show up as a wide, confusing proof breakage far from its
cause.

§4 therefore pins the elaborated terms with `#guard_msgs in #print`, and §3 pins
the *tactic* behaviour with `fail_if_success`. On a toolchain bump, a diff here
localises the change immediately: §4 says the desugaring moved, §3 says `split`'s
reach moved. Both are load-bearing for the proof technique, so both are worth a
build failure rather than a surprise.

L4YAML instance (DOCS item 9c, 2026-08-07): the indexed block-scalar arm already
had two early-exit guards. Adding item 9c's `inFlow` rejection as a third made
`split at h` in `Proofs/Scanner/IndexedDispatch.lean` fail with the step limit;
rewriting the arm as an `else do` chain moved the failure rather than removing
it. Folding 9c's check into the existing header check as `blockScalarPreErrIx`
kept the arm at its original guard count and needed **zero** proof edits in that
file.

`lake build Tests.Reflections.DoEarlyExitDuplicatesContinuation`
-/

namespace DoEarlyExitDuplicatesContinuation

/-- Two rejection reasons, standing for L4YAML's `blockScalarInFlow` (the guard
    being *added*) and `expectedNewline` (the guard already there). -/
inductive Err where
  | guardA
  | guardB
  deriving DecidableEq, Repr, BEq

structure St where
  a : Bool
  b : Bool
  n : Nat
  deriving DecidableEq, Repr, BEq

/-- Stands for the arm's body — whatever the guards protect. In the real
    dispatcher this is the whole block-scalar recogniser, which is why
    duplicating it is expensive. -/
def body (s : St) : Except Err St :=
  if s.n = 0 then .error .guardA else .ok { s with n := s.n - 1 }

/-! ## §1  A baseline, three spellings of one function, and a growth probe

`oneGuard` is the BEFORE picture: the arm as it stood, carrying one rejection.
Adding a second rejection to it can be spelled three ways — `twoGuards`,
`elseDo`, `merged` — and §2 proves those three are the same function.
`threeGuards` is not one of the spellings; it exists only to show that the
layer count tracks the guard count (§4). -/

/-- **Baseline** — one guard, one rejection: the arm before anything is added. -/
def oneGuard (s : St) : Except Err St := do
  if s.b then throw .guardB
  body s

/-- **Spelling 1 of 3** — add the rejection as a second consecutive early-exit
    guard. The obvious way, and the one that costs a layer. -/
def twoGuards (s : St) : Except Err St := do
  if s.a then throw .guardA
  if s.b then throw .guardB
  body s

/-- **Spelling 2 of 3** — the "convert to an `else` chain" fix. It removes the
    OUTER layer but re-shapes the arm, so scripts written against `oneGuard`
    still break: the failure moves rather than going away. -/
def elseDo (s : St) : Except Err St :=
  if s.a then throw .guardA
  else do
    if s.b then throw .guardB
    body s

/-! ### ★ THE RECOMMENDED IDIOM — `preErr` + `merged` + `invert_merged`

This is the one to copy. Adding a rejection to a `do`-block arm that proofs
case-split on has two parts, and a third that is deliberately empty:

1. **`preErr`** — the new rejection and the existing one, in precedence order,
   as ONE `Option Err`-valued helper. Precedence becomes explicit and reviewable,
   which is also where you make a new error agree with a sibling implementation's.
2. **`merged`** — check it with `if let some e := … then throw e`, in the exact
   position the old guard occupied. The arm's `if` count is unchanged, so its
   elaborated shape is unchanged.
3. **`invert_merged`** — *nothing to do*. The inversion script is `invert_one`'s,
   verbatim. That is the property being bought.

Prefer it over **`twoGuards`** (costs a layer; every walker of this arm must be
rewritten) and over **`elseDo`** (removes the outer layer but re-shapes the arm,
so the breakage moves rather than going away). -/

/-- **★ Recommended, part 1** — both rejections in precedence order, as data.
    This is what lets `merged` keep the arm's guard count at one. -/
def preErr (s : St) : Option Err :=
  if s.a then some .guardA
  else if s.b then some .guardB
  else none

/-- **★ Recommended, part 2 — spelling 3 of 3.** One guard, both rejections.
    The arm's shape, and so its interface to every proof that walks it, is
    unchanged from `oneGuard`. -/
def merged (s : St) : Except Err St := do
  if let some e := preErr s then throw e
  body s

/-- **Not a spelling** — a THIRD rejection, so this is a different function.
    It is here only to show the layers nesting one per guard (§4). -/
def threeGuards (s : St) : Except Err St := do
  if s.a then throw .guardA
  if s.b then throw .guardB
  if s.n = 7 then throw .guardA
  body s

/-! ## §2  The three spellings agree on every input

`twoGuards`, `elseDo` and `merged` are one function written three ways: there is
no behavioural reason to prefer any of them, which is exactly why the shape cost
is easy to miss. The two guarded rows below say what is NOT claimed —
`oneGuard` lacks the new rejection and `threeGuards` carries an extra one, so
each agrees only away from the input its own guard decides.

Not a full pairwise matrix, deliberately: `same` is an equivalence, so pinning
the class once against `twoGuards` gives every remaining pair by transitivity
(`threeGuards ≡ elseDo` off `n = 7`, say, follows from rows 2 and 4). Extra rows
would pass without adding coverage. -/

private def sweep : List St :=
  [false, true].flatMap fun a =>
    [false, true].flatMap fun b =>
      [0, 1, 7].map fun n => ⟨a, b, n⟩

private def same : Except Err St → Except Err St → Bool
  | .error e₁, .error e₂ => e₁ == e₂
  | .ok s₁,    .ok s₂    => s₁ == s₂
  | _,         _         => false

-- The three spellings, unconditionally.
#guard sweep.all fun s => same (twoGuards s) (merged s)
#guard sweep.all fun s => same (twoGuards s) (elseDo s)
-- The baseline agrees only where the ADDED rejection does not fire.
#guard sweep.all fun s => s.a || same (twoGuards s) (oneGuard s)
-- `threeGuards` agrees only where its EXTRA rejection does not fire.
#guard sweep.all fun s => s.n == 7 || same (threeGuards s) (twoGuards s)
#guard sweep.all fun s => s.n == 7 || same (threeGuards s) (elseDo s)

/-! ## §3  The proof-technique canary

The script under test is the ordinary two-arm inversion every scanner proof
uses: split the guard, kill the `throw` branch, keep the body branch. -/

/-- Works on one layer. -/
theorem invert_one {s s' : St} (h : oneGuard s = .ok s') : body s = .ok s' := by
  unfold oneGuard at h
  split at h
  · exact absurd h (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw])
  · exact h

/-- **★ Recommended, part 3 — the part that is deliberately empty.** Byte-for-byte
    `invert_one`'s script: `unfold`, `split at h`, kill the throw arm, `exact h`.
    Nothing was rewritten to accommodate the new rejection, which is the whole
    point of routing it through `preErr`. -/
theorem invert_merged {s s' : St} (h : merged s = .ok s') : body s = .ok s' := by
  unfold merged at h
  split at h
  · exact absurd h (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw])
  · exact h

/-- Two layers are still invertible — but **not by that script**, and the middle
    of this proof is the canary that says so.

    `fail_if_success` pins the failure: on the two-layer shape `split at h`
    descends into the join point, splits `s.b` rather than `s.a`, and leaves `h`
    textually unchanged, so the `exact h` arm has nothing to fire on. If a future
    toolchain makes the one-layer script succeed here, this errors — and that
    error is the signal, not a defect: `split`'s reach into `do` join points has
    changed and L4YAML's dispatcher inversions should be re-audited.

    What does work is enumerating the guards with `by_cases` instead of walking
    the term — the robust form when an arm's guard count is not under your
    control. It is also strictly more code per guard, which is the running cost
    the merge in `merged` avoids. -/
theorem invert_two {s s' : St} (h : twoGuards s = .ok s') : body s = .ok s' := by
  unfold twoGuards at h
  fail_if_success (
    split at h
    · exact absurd h (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw])
    · exact h)
  by_cases ha : s.a = true
  · simp [ha, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · by_cases hb : s.b = true
    · simp [ha, hb, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    · simpa [ha, hb] using h

/-! ## §4  The elaboration canary

One `have __do_jp := …` layer per early-exit guard, nested outermost-last. The
`merged` shape has exactly as many layers as `oneGuard`; `twoGuards` has two and
`threeGuards` three. A toolchain that changes `do`-desugaring will diff here. -/

/--
info: @[expose] def DoEarlyExitDuplicatesContinuation.oneGuard : St → Except Err St :=
fun s =>
  have __do_jp := fun __r => body s;
  if s.b = true then do
    let __r ← throw Err.guardB
    __do_jp __r
  else __do_jp ()
-/
#guard_msgs in
#print oneGuard

/--
info: @[expose] def DoEarlyExitDuplicatesContinuation.merged : St → Except Err St :=
fun s =>
  have __do_jp := fun __r => body s;
  match preErr s with
  | some e => do
    let __r ← throw e
    __do_jp __r
  | x => __do_jp ()
-/
#guard_msgs in
#print merged

/--
info: @[expose] def DoEarlyExitDuplicatesContinuation.twoGuards : St → Except Err St :=
fun s =>
  have __do_jp := fun __r =>
    have __do_jp := fun __r => body s;
    if s.b = true then do
      let __r ← throw Err.guardB
      __do_jp __r
    else __do_jp ();
  if s.a = true then do
    let __r ← throw Err.guardA
    __do_jp __r
  else __do_jp ()
-/
#guard_msgs in
#print twoGuards

/-! Three guards, three nested layers: the nesting is linear in the guard count,
but the `simp` expansion of those layers is 2^layers. -/

/--
info: @[expose] def DoEarlyExitDuplicatesContinuation.threeGuards : St → Except Err St :=
fun s =>
  have __do_jp := fun __r =>
    have __do_jp := fun __r =>
      have __do_jp := fun __r => body s;
      if s.n = 7 then do
        let __r ← throw Err.guardA
        __do_jp __r
      else __do_jp ();
    if s.b = true then do
      let __r ← throw Err.guardB
      __do_jp __r
    else __do_jp ();
  if s.a = true then do
    let __r ← throw Err.guardA
    __do_jp __r
  else __do_jp ()
-/
#guard_msgs in
#print threeGuards

/--
info: @[expose] def DoEarlyExitDuplicatesContinuation.elseDo : St → Except Err St :=
fun s =>
  if s.a = true then throw Err.guardA
  else
    have __do_jp := fun __r => body s;
    if s.b = true then do
      let __r ← throw Err.guardB
      __do_jp __r
    else __do_jp ()
-/
#guard_msgs in
#print elseDo

/-! ## §5  Axiom audit

Judge by axiom profile, not by the absence of `sorry` warnings. -/

/-- info: 'DoEarlyExitDuplicatesContinuation.invert_one' depends on axioms: [propext] -/
#guard_msgs in
#print axioms invert_one

/-- info: 'DoEarlyExitDuplicatesContinuation.invert_merged' depends on axioms: [propext] -/
#guard_msgs in
#print axioms invert_merged

/-- info: 'DoEarlyExitDuplicatesContinuation.invert_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms invert_two

end DoEarlyExitDuplicatesContinuation

end Blanket
