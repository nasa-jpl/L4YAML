/-!
# Reduction-by-import — runnable demonstration

A self-contained (core Lean, no `L4YAML` import) illustration of the proof-engineering principle
documented in `Blueprint/08-initiative-4-intrinsic-foundations.md`, Reflection 225: **wiring in a
verified-but-unconsumed module is "reduction by import"** — it does *not* shrink the `sorry` count, it
changes a `sorry`'s **type** from an *execution* obligation to a *structural* one, and that retype is
the real progress.

The real instance: `flow_parser_ok_of_structure` (`FlowParserAcceptance.lean`) had been built,
axiom-clean, and imported by nothing — a verified leaf hanging off the build graph. Importing it and
applying it once reduced the seq frontier goal from `ParseNodeFlowSeqOk …` (how the *parser executes*:
fuel, positions, loop bundles) to `FlowSubrangesOk tokens` (a pure *structural* statement). Same goal,
same `sorry` count (held at 4) — but the residual's **type** flipped to the structural shape that the
emitter-characterization + typed-locator infrastructure can actually attack.

This toy mirrors that exactly:

* **Structure** (`Dyck`): a *declarative* well-bracketing — total balance 0 and every prefix ≥ 0.
  Mentions no fuel, no run state. `decide`-able.
* **Execution** (`Execution = runFrom … = true`): a *fuel-bounded left-to-right parser* maintaining a
  running depth, rejecting on negative depth or out-of-fuel. Its acceptance is a statement about *how
  the run proceeds*.
* **The dispatcher** (`dispatcher : Dyck ts → Execution ts`): the "≈900-line verified module" in
  miniature — the fuel/accumulator induction bridging the declarative spec to the operational run.

The point is `unreduced` vs `reduced` below: both conclude `Execution ts` and both leave exactly **one**
obligation, but its **type** differs — `Execution` (the run) before wiring, `Dyck` (structure) after.
The structural residual is the `decide`-able / generically-attackable one.

Run it: open in the IDE (the `#eval`s render in the infoview) or
`lake build Tests.Reflections.ReductionByImport` (the `#guard`s fail the build if any expectation is wrong).
-/

namespace ReductionByImport

/-- Toy tokens: opener `[`, closer `]`, atom `a`. -/
inductive Tok | opn | cls | atom
deriving DecidableEq, Repr

/-- Bracket delta: +1 open, −1 close, 0 atom. -/
def delta : Tok → Int
  | .opn => 1
  | .cls => -1
  | .atom => 0

/-- Prefix balance of the first `n` tokens (`foldl`, as in the sibling demos). -/
def bal (ts : List Tok) (n : Nat) : Int :=
  ((ts.take n).map delta).foldl (· + ·) 0

/-! ## Structure (declarative) vs Execution (operational) — the two shapes the dispatcher bridges. -/

/-- **STRUCTURE.**  Declarative Dyck: total balance 0, and every prefix is at balance ≥ 0.  Mentions no
    fuel and no run state — it is a fact about the token list's *shape*.  `abbrev`, not `def`, so
    `decide` synthesizes the bounded-∀ instance (`Nat.decidableBallLT`). -/
abbrev Dyck (ts : List Tok) : Prop :=
  bal ts ts.length = 0 ∧ ∀ i, i < ts.length + 1 → bal ts i ≥ 0

/-- **EXECUTION.**  A fuel-bounded left-to-right parser: maintains a running depth `d`, rejects on
    negative depth or on running out of fuel, accepts iff it reaches the end at depth 0.  Acceptance is
    a statement about HOW THE RUN PROCEEDS (the fuel, the depth accumulator), not directly about shape. -/
def runFrom : List Tok → Int → Nat → Bool
  | [], d, _ => decide (d = 0)
  | _ :: _, _, 0 => false
  | t :: rest, d, fuel + 1 =>
      let d' := d + delta t
      if d' < 0 then false else runFrom rest d' fuel

/-- The execution obligation: the parser accepts `ts` (length-many fuel suffices). -/
abbrev Execution (ts : List Tok) : Prop := runFrom ts 0 ts.length = true

/-! ## The dispatcher — the "verified module": `Dyck → Execution`, by the fuel/accumulator induction.

The algebra bridging the *declarative* prefix balances to the *operational* running depth is a one-step
recurrence for `bal` (below); the dispatcher itself is a strong-enough induction that threads a starting
depth `d` and fuel through the run.  This is the miniature of the dispatcher the real proof imports. -/

/-- `foldl (·+·)` shifts its initial accumulator out. -/
theorem foldl_shift (l : List Int) (c : Int) :
    l.foldl (· + ·) c = c + l.foldl (· + ·) 0 := by
  induction l generalizing c with
  | nil => simp
  | cons a t ih => simp only [List.foldl_cons]; rw [ih (c + a), ih (0 + a)]; omega

/-- One-step recurrence: the balance of `t :: rest` over `i+1` tokens is `delta t` plus the balance of
    `rest` over `i` tokens.  This is what lets the running depth (operational) track the prefix balance
    (declarative). -/
theorem bal_cons (t : Tok) (rest : List Tok) (i : Nat) :
    bal (t :: rest) (i + 1) = delta t + bal rest i := by
  simp only [bal, List.take_succ_cons, List.map_cons, List.foldl_cons]
  rw [foldl_shift ((rest.take i).map delta) (0 + delta t)]
  omega

/-- The dispatcher's strengthened induction: from any starting depth `d` with enough fuel, a run whose
    every prefix (offset by `d`) stays ≥ 0 and ends at 0 accepts. -/
theorem dispatcher_aux : ∀ (ts : List Tok) (d : Int) (fuel : Nat),
    ts.length ≤ fuel →
    (∀ i, i < ts.length + 1 → d + bal ts i ≥ 0) →
    d + bal ts ts.length = 0 →
    runFrom ts d fuel = true := by
  intro ts
  induction ts with
  | nil =>
    intro d _ _ _ hend
    simp only [bal, List.take_nil, List.map_nil, List.foldl_nil, List.length_nil] at hend
    have hd : d = 0 := by omega
    simp only [runFrom, hd]
    decide
  | cons t rest ih =>
    intro d fuel hlen hpre hend
    cases fuel with
    | zero => exfalso; simp only [List.length_cons] at hlen; omega
    | succ f =>
      have hstep1 := hpre 1 (by simp only [List.length_cons]; omega)
      have hbal1 : bal (t :: rest) 1 = delta t := by
        rw [bal_cons t rest 0]; simp [bal]
      have hd' : ¬ (d + delta t < 0) := by rw [hbal1] at hstep1; omega
      simp only [runFrom]
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

/-- **The dispatcher.**  Structure (`Dyck`) implies Execution (the parser accepts) — the whole
    fuel/run reasoning lives here, once. -/
theorem dispatcher (ts : List Tok) (h : Dyck ts) : Execution ts := by
  obtain ⟨hend, hpre⟩ := h
  exact dispatcher_aux ts 0 ts.length (Nat.le_refl _)
    (by intro i hi; have := hpre i hi; simpa using this)
    (by simpa using hend)

/-! ## The principle: same conclusion, residual of a DIFFERENT TYPE.

`unreduced` and `reduced` both conclude `Execution ts` and both leave exactly **one** obligation (count
unchanged) — but its *type* is `Execution` (the run) before wiring the dispatcher, and `Dyck` (structure)
after.  The retype is the progress: the structural residual is the `decide`-able one. -/

/-- BEFORE wiring: the only handle on `Execution ts` is an `Execution`-typed fact — you must supply the
    run itself.  Residual type = the execution predicate. -/
theorem unreduced {ts : List Tok} (h_exec : Execution ts) : Execution ts := h_exec

/-- AFTER wiring (`dispatcher`): the run/fuel reasoning is absorbed, so the residual you must supply is
    `Dyck ts` — a STRUCTURAL fact of a *different type*.  Same conclusion, same count, different shape. -/
theorem reduced {ts : List Tok} (h_struct : Dyck ts) : Execution ts := dispatcher ts h_struct

/-! ## Two streams.  `good` is Dyck and runs; `bad` is balance-0-but-mis-nested — not Dyck, rejected. -/

/-- `[ a ]` — opn, atom, cls.  Dyck (balanced, every prefix ≥ 0); the parser accepts. -/
def good : List Tok := [.opn, .atom, .cls]

/-- `] [` — cls, opn.  Total balance 0, but the first prefix dips to −1: NOT Dyck.  The parser rejects
    on negative depth.  The discriminating case "balance-0 but mis-nested" — exactly why the *structural*
    spec is prefix-nonneg, not merely total-balance-0. -/
def bad : List Tok := [.cls, .opn]

/-! ## `#eval` — see the structure per prefix.  Per index `i`: `bal(i)` and whether the prefix is ≥ 0. -/

/-- One row of the diagnostic table for prefix length `i` of `ts`. -/
def report (ts : List Tok) (i : Nat) : String :=
  s!"i={i}  bal(i)={bal ts i}  prefix≥0={decide (bal ts i ≥ 0)}"

-- `good`: every prefix balance is ≥ 0 and ends at 0 — Dyck, so the parser accepts.
/-- info: ["i=0  bal(i)=0  prefix≥0=true", "i=1  bal(i)=1  prefix≥0=true", "i=2  bal(i)=1  prefix≥0=true",
 "i=3  bal(i)=0  prefix≥0=true"] -/
#guard_msgs in
#eval (List.range (good.length + 1)).map (report good)

-- `bad`: prefix at i=1 dips to −1 — NOT Dyck, and the parser rejects there even though bal(2)=0.
/-- info: ["i=0  bal(i)=0  prefix≥0=true", "i=1  bal(i)=-1  prefix≥0=false", "i=2  bal(i)=0  prefix≥0=true"] -/
#guard_msgs in
#eval (List.range (bad.length + 1)).map (report bad)

/-! ## `#guard` — structure decides, execution runs, and the dispatcher ties them. -/

-- Structure is `decide`-able; the parser is run.
#guard decide (Dyck good)            -- true
#guard runFrom good 0 good.length    -- true  : Execution good (the parser accepts)
#guard !decide (Dyck bad)            -- false : prefix dips negative
#guard !(runFrom bad 0 bad.length)   -- the parser rejects bad (negative depth)

/-! ## The theorems at work — the reduction in action. -/

/-- The structural residual, discharged by `decide` (no run, no fuel). -/
theorem good_Dyck : Dyck good := by decide

/-- `reduced` turns the structural fact into the execution conclusion via the dispatcher — one line, no
    re-derivation of the run. -/
theorem good_Execution : Execution good := reduced good_Dyck

/-- `bad` is not Dyck — structurally refuted by `decide`. -/
theorem bad_not_Dyck : ¬ Dyck bad := by decide

/-- And the parser genuinely rejects `bad`: `Execution bad` is false. -/
theorem bad_not_Execution : ¬ Execution bad := by decide

end ReductionByImport
