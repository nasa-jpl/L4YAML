/-!
# Convergent reduction — runnable demonstration

A self-contained (core Lean, no `L4YAML` import) illustration of the **convergence corollary** of the
reduction-by-import principle, documented in `Blueprint/08-initiative-4-intrinsic-foundations.md`,
Reflection 227 (sibling of `ReductionByImport.lean`, which illustrates the base principle / Reflection 225).

**Base principle (Reflection 225, `ReductionByImport.lean`).** Wiring in a verified bridge does not shrink
the `sorry` count; it changes a `sorry`'s *type* from an *execution* obligation to a *structural* one.

**Convergence corollary (Reflection 227, this file).** When the verified bridge has the shape
`Structure → (A ∧ B)` and you have *two* open goals `A` and `B`, reduce **both** through it — even though the
second reduction looks like mere repetition of the first. The payoff is not the second retype; it is the
*convergence*: both residuals become the **identical** type `Structure`, so the single producer of `Structure`
closes both at once. Where the residuals *diverge* (one already `Structure`, the other still operational), a
producer aimed at the first leaves the second untouched — two jobs, run serially.

The real instance: `flow_parser_ok_of_structure : FlowSubrangesOk → ParseNodeFlowSeqOk ∧ ParseEntryFlowMapOk`.
The **seq** structure sorry was reduced to the structural `FlowSubrangesOk tokens` (Reflection 225); the **map**
sorry was still the operational `ParseEntryFlowMapOk`. Wiring the dispatcher's `.map` half (Reflection 227,
commit `656b5fbd`) flipped it to the *same* `FlowSubrangesOk tokens`, so both `NonemptyStructure.lean` structure
sorries (725 seq / 966 map) became **one** residual, closable by one Phase-J producer of `FlowSubrangesOk`.

This toy mirrors that exactly:

* **Structure** (`Dyck`): declarative well-bracketing — total balance 0, every prefix ≥ 0. `decide`-able.
* **Execution A** (`ExecF`): a *fuel-bounded* forward depth parser (`runFwd`).
* **Execution B** (`ExecS`): a *structural* forward depth recognizer (`runStruct`) — a distinct function with a
  distinct recursion principle (structural, no fuel), hence a distinct `Prop`. It stands in for the second
  grammar production (the seq/map split): a proof of `ExecF ts` is **not** a proof of `ExecS ts`.
* **The convergent bridge** (`dispatch2 : Dyck ts → ExecF ts ∧ ExecS ts`): the verified
  `Structure → (A ∧ B)` module in miniature.

The point is `divergent` vs `convergent` below: both conclude `ExecF ts ∧ ExecS ts`, but `divergent` consumes
**two** residuals of **two** types (`Dyck` for A, `ExecS` for B — A reduced, B not), while `convergent` consumes
**one** residual of type `Dyck` that discharges both. The single structural lemma `good_Dyck` feeds `convergent`
alone; `divergent` additionally demands the operational `good_ExecS`.

Run it: open in the IDE (the `#eval`s render in the infoview) or
`lake build Tests.Reflections.ConvergentReduction` (the `#guard`s fail the build if any expectation is wrong).
-/

namespace ConvergentReduction

/-- Toy tokens: opener `[`, closer `]`, atom `a`. -/
inductive Tok | opn | cls | atom
deriving DecidableEq, Repr

/-- Bracket delta: +1 open, −1 close, 0 atom. -/
def delta : Tok → Int
  | .opn => 1
  | .cls => -1
  | .atom => 0

/-- Prefix balance of the first `n` tokens. -/
def bal (ts : List Tok) (n : Nat) : Int :=
  ((ts.take n).map delta).foldl (· + ·) 0

/-! ## Structure (declarative) — the single shape both executions reduce to. -/

/-- **STRUCTURE.**  Declarative Dyck: total balance 0, and every prefix is at balance ≥ 0.  `abbrev`, not
    `def`, so `decide` synthesizes the bounded-∀ instance (`Nat.decidableBallLT`). -/
abbrev Dyck (ts : List Tok) : Prop :=
  bal ts ts.length = 0 ∧ ∀ i, i < ts.length + 1 → bal ts i ≥ 0

/-! ## Two distinct operational acceptors of the same language — the `A`/`B` the bridge spans. -/

/-- **EXECUTION A.**  A *fuel-bounded* left-to-right parser: running depth `d`, rejects on negative depth
    or out-of-fuel.  Acceptance is a statement about how the *fuel-driven* run proceeds. -/
def runFwd : List Tok → Int → Nat → Bool
  | [], d, _ => decide (d = 0)
  | _ :: _, _, 0 => false
  | t :: rest, d, fuel + 1 =>
      let d' := d + delta t
      if d' < 0 then false else runFwd rest d' fuel

/-- Execution-A obligation: the fuel-bounded parser accepts `ts`. -/
abbrev ExecF (ts : List Tok) : Prop := runFwd ts 0 ts.length = true

/-- **EXECUTION B.**  A *structural* left-to-right recognizer: the SAME depth check, but recursing on the
    list directly (no fuel — termination is structural).  A genuinely different function, hence a different
    `Prop`: `ExecF` and `ExecS` stand in for the two grammar productions (seq-acc / map-acc) the real bridge
    concludes.  A proof of `ExecF ts` says nothing about `ExecS ts`. -/
def runStruct : List Tok → Int → Bool
  | [], d => decide (d = 0)
  | t :: rest, d =>
      let d' := d + delta t
      if d' < 0 then false else runStruct rest d'

/-- Execution-B obligation: the structural recognizer accepts `ts`. -/
abbrev ExecS (ts : List Tok) : Prop := runStruct ts 0 = true

/-! ## The shared algebra — one-step `bal` recurrence both inductions ride. -/

/-- `foldl (·+·)` shifts its initial accumulator out. -/
theorem foldl_shift (l : List Int) (c : Int) :
    l.foldl (· + ·) c = c + l.foldl (· + ·) 0 := by
  induction l generalizing c with
  | nil => simp
  | cons a t ih => simp only [List.foldl_cons]; rw [ih (c + a), ih (0 + a)]; omega

/-- One-step recurrence: the balance of `t :: rest` over `i+1` tokens is `delta t` plus the balance of
    `rest` over `i` tokens. -/
theorem bal_cons (t : Tok) (rest : List Tok) (i : Nat) :
    bal (t :: rest) (i + 1) = delta t + bal rest i := by
  simp only [bal, List.take_succ_cons, List.map_cons, List.foldl_cons]
  rw [foldl_shift ((rest.take i).map delta) (0 + delta t)]
  omega

/-! ## The two bridges `Dyck → ExecF` and `Dyck → ExecS`, then their product `Dyck → (ExecF ∧ ExecS)`. -/

/-- Fuel-driven induction: from any starting depth `d` with enough fuel, a run whose every prefix (offset by
    `d`) stays ≥ 0 and ends at 0 accepts. -/
theorem runFwd_aux : ∀ (ts : List Tok) (d : Int) (fuel : Nat),
    ts.length ≤ fuel →
    (∀ i, i < ts.length + 1 → d + bal ts i ≥ 0) →
    d + bal ts ts.length = 0 →
    runFwd ts d fuel = true := by
  intro ts
  induction ts with
  | nil =>
    intro d _ _ _ hend
    simp only [bal, List.take_nil, List.map_nil, List.foldl_nil, List.length_nil] at hend
    have hd : d = 0 := by omega
    simp only [runFwd, hd]; decide
  | cons t rest ih =>
    intro d fuel hlen hpre hend
    cases fuel with
    | zero => exfalso; simp only [List.length_cons] at hlen; omega
    | succ f =>
      have hstep1 := hpre 1 (by simp only [List.length_cons]; omega)
      have hbal1 : bal (t :: rest) 1 = delta t := by rw [bal_cons t rest 0]; simp [bal]
      have hd' : ¬ (d + delta t < 0) := by rw [hbal1] at hstep1; omega
      simp only [runFwd]
      rw [if_neg hd']
      apply ih (d + delta t) f
      · simp only [List.length_cons] at hlen; omega
      · intro i hi
        have hpre' := hpre (i + 1) (by simp only [List.length_cons]; omega)
        rw [bal_cons t rest i] at hpre'
        omega
      · have hlen_eq : (t :: rest).length = rest.length + 1 := by simp [List.length_cons]
        rw [hlen_eq, bal_cons t rest rest.length] at hend
        omega

/-- Structural induction (no fuel): the same conclusion for `runStruct`.  A DISTINCT proof of a DISTINCT
    predicate — there is no shortcut from `runFwd`'s acceptance to this one. -/
theorem runStruct_aux : ∀ (ts : List Tok) (d : Int),
    (∀ i, i < ts.length + 1 → d + bal ts i ≥ 0) →
    d + bal ts ts.length = 0 →
    runStruct ts d = true := by
  intro ts
  induction ts with
  | nil =>
    intro d _ hend
    simp only [bal, List.take_nil, List.map_nil, List.foldl_nil, List.length_nil] at hend
    have hd : d = 0 := by omega
    simp only [runStruct, hd]; decide
  | cons t rest ih =>
    intro d hpre hend
    have hstep1 := hpre 1 (by simp only [List.length_cons]; omega)
    have hbal1 : bal (t :: rest) 1 = delta t := by rw [bal_cons t rest 0]; simp [bal]
    have hd' : ¬ (d + delta t < 0) := by rw [hbal1] at hstep1; omega
    simp only [runStruct]
    rw [if_neg hd']
    apply ih (d + delta t)
    · intro i hi
      have hpre' := hpre (i + 1) (by simp only [List.length_cons]; omega)
      rw [bal_cons t rest i] at hpre'
      omega
    · have hlen_eq : (t :: rest).length = rest.length + 1 := by simp [List.length_cons]
      rw [hlen_eq, bal_cons t rest rest.length] at hend
      omega

/-- Bridge A: structure ⟹ execution A. -/
theorem dispatchF (ts : List Tok) (h : Dyck ts) : ExecF ts := by
  obtain ⟨hend, hpre⟩ := h
  exact runFwd_aux ts 0 ts.length (Nat.le_refl _)
    (by intro i hi; have := hpre i hi; simpa using this) (by simpa using hend)

/-- Bridge B: structure ⟹ execution B. -/
theorem dispatchS (ts : List Tok) (h : Dyck ts) : ExecS ts := by
  obtain ⟨hend, hpre⟩ := h
  exact runStruct_aux ts 0
    (by intro i hi; have := hpre i hi; simpa using this) (by simpa using hend)

/-- **The convergent bridge** `Structure → (A ∧ B)` — the miniature of
    `flow_parser_ok_of_structure : FlowSubrangesOk → ParseNodeFlowSeqOk ∧ ParseEntryFlowMapOk`.  One theorem
    proving BOTH conclusions from the one structure. -/
theorem dispatch2 (ts : List Tok) (h : Dyck ts) : ExecF ts ∧ ExecS ts :=
  ⟨dispatchF ts h, dispatchS ts h⟩

/-! ## The corollary: DIVERGENT vs CONVERGENT residuals.

Both conclude `ExecF ts ∧ ExecS ts`.  `divergent` reduces only A through the bridge (residual `Dyck`) and
leaves B operational (residual `ExecS`): **two residuals, two types**.  `convergent` reduces BOTH (single
residual `Dyck`): **one residual, closing both**.  This is the seq/map story — before wiring the `.map` half,
the residual pair was `(FlowSubrangesOk, ParseEntryFlowMapOk)`; after, `(FlowSubrangesOk, FlowSubrangesOk)`. -/

/-- DIVERGENT.  A is reduced to the structural `Dyck` (closed via the bridge); B is still the operational
    `ExecS` — supplied separately.  Residual pair = (`Dyck`, `ExecS`): two types, two producers needed. -/
theorem divergent {ts : List Tok} (h_struct : Dyck ts) (h_execS : ExecS ts) :
    ExecF ts ∧ ExecS ts :=
  ⟨dispatchF ts h_struct, h_execS⟩

/-- CONVERGENT.  Both reduced through the bridge: a single `Dyck`-typed residual discharges both.  Residual =
    (`Dyck`): one type, one producer closes both. -/
theorem convergent {ts : List Tok} (h_struct : Dyck ts) : ExecF ts ∧ ExecS ts :=
  dispatch2 ts h_struct

/-! ## Two streams.  `good` is Dyck (both executions accept); `bad` is balance-0-but-mis-nested (both reject). -/

/-- `[ a ]` — Dyck; both the fuel and structural recognizers accept. -/
def good : List Tok := [.opn, .atom, .cls]

/-- `] [` — total balance 0 but the first prefix dips to −1: NOT Dyck.  Both recognizers reject. -/
def bad : List Tok := [.cls, .opn]

/-! ## `#guard` — structure decides; both executions run; the bridge ties all three. -/

-- Structure is `decide`-able; both parsers run; the discriminating witness `bad` is balance-0 yet mis-nested.
#guard decide (Dyck good)              -- true
#guard runFwd good 0 good.length       -- true  : ExecF good
#guard runStruct good 0                -- true  : ExecS good
#guard !decide (Dyck bad)              -- false : prefix dips negative
#guard !(runFwd bad 0 bad.length)      -- the fuel parser rejects bad
#guard !(runStruct bad 0)              -- the structural recognizer also rejects bad

/-! ## `#eval` — the per-prefix structure both executions consume. -/

/-- One row of the diagnostic table for prefix length `i` of `ts`. -/
def report (ts : List Tok) (i : Nat) : String :=
  s!"i={i}  bal(i)={bal ts i}  prefix≥0={decide (bal ts i ≥ 0)}"

-- `good`: every prefix balance ≥ 0 and ends at 0 — Dyck, so both executions accept.
/-- info: ["i=0  bal(i)=0  prefix≥0=true", "i=1  bal(i)=1  prefix≥0=true", "i=2  bal(i)=1  prefix≥0=true",
 "i=3  bal(i)=0  prefix≥0=true"] -/
#guard_msgs in
#eval (List.range (good.length + 1)).map (report good)

-- `bad`: prefix at i=1 dips to −1 — NOT Dyck; both executions reject there even though bal(2)=0.
/-- info: ["i=0  bal(i)=0  prefix≥0=true", "i=1  bal(i)=-1  prefix≥0=false", "i=2  bal(i)=0  prefix≥0=true"] -/
#guard_msgs in
#eval (List.range (bad.length + 1)).map (report bad)

/-! ## The corollary at work — one structural lemma closes both goals. -/

/-- The single structural residual, discharged by `decide` (no run). -/
theorem good_Dyck : Dyck good := by decide

/-- The leftover operational residual the DIVERGENT route still demands separately. -/
theorem good_ExecS : ExecS good := by decide

/-- **CONVERGENT**: ONE structural input `good_Dyck` discharges BOTH conclusions. -/
theorem good_both_convergent : ExecF good ∧ ExecS good := convergent good_Dyck

/-- **DIVERGENT**: the same conclusion needs the structural input `good_Dyck` AND the separate operational
    input `good_ExecS` — two residuals, because B was not reduced through the bridge. -/
theorem good_both_divergent : ExecF good ∧ ExecS good := divergent good_Dyck good_ExecS

end ConvergentReduction
