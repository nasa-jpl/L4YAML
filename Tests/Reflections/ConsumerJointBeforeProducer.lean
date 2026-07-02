/-!
# Consumer-joint-before-producer — runnable demonstration

A self-contained (core Lean, no `L4YAML` import) illustration of the proof-engineering principle
documented in `Blueprint/08-initiative-4-intrinsic-foundations.md`, **Reflection 231** (and its
continuations **232 / 237 / 241**): when a frontier has converged on a single large *producer* (a
recursion that won't land green in one session), the productive self-contained brick is often NOT a
slice of the producer — it is the **consumer** of the producer's not-yet-existing output.  Write one
lemma that takes the recursion's eventual *deliverable* as bare hypotheses and produces the
downstream target.

**Why it is the right move:** it costs nothing now (the assembler/plumbing already exists from prior
bricks), it can't regress (fully proven), and it **collapses the residual's SHAPE** — from a
*scatter* ("produce primitives P₁…Pₙ AND assemble them") into *exactly one typed boundary* ("produce
the single deliverable `D`; feed it to the joint").  The `sorry` count is unchanged; the residual's
**type** flips, and that retype is the progress ([[ref-reduction-by-import]]).

The real instance: `seqBodyProps_of_windowed_safebody` (`NonemptyStructure.lean`) takes the seq
producer's eventual deliverable — a windowed `SafeBody` + the balanced-subrange facts — and produces
the full `SeqBodyProps`.  The producer no longer has to "match the assembler"; it only has to deliver
the one structured witness.

This toy mirrors all the moving parts on a bracket language:

* **The assembler** (`assemble`, [[ref-parametric-assembler-extraction]]) bundles three primitive
  conjuncts into the consumer goal `Goal` (toy `SeqBodyProps`).  It already exists.
* **The deliverable** (`Dyck`, the recursion's eventual structured output) is a SINGLE witness from
  which all three conjuncts follow — and it even **recovers `HeadNonneg` for free** (the toy of
  Reflection 237's "recover content-start from the located body"), so the deliverable need not carry
  it separately.
* **The consumer joint** (`joint : Dyck ts → Goal ts`) is fully proven today — the brick built
  *before* the producer.
* `residual_scattered` vs `residual_one_shape` below are the principle in action: both conclude
  `Goal ts`, but the residual is THREE obligations before the joint and ONE typed boundary after.

And the **faithful-mirror caveat** (Reflections 232 / 241): a shared abstraction discharges exactly
the obligations at ITS granularity; an obligation that lives BELOW that granularity (`NoAtomB` — the
deliverable `Dyck` is blind to atom flavours) the joint genuinely *cannot* supply, so the honest
mirror joint carries it as an explicit pass-through input rather than pretending to discharge it.

Run it: open in the IDE (the `#eval`s render in the infoview) or
`lake build Tests.Reflections.ConsumerJointBeforeProducer` (the `#guard`s fail the build if any
expectation is wrong).
-/

namespace ConsumerJointBeforeProducer

/-- Toy tokens: opener `[`, closer `]`, and two atom flavours `a`/`b`.  The two flavours are
    invisible to the bracket structure (`delta` agrees on them) — they are the payload below the
    deliverable's granularity (used for the asymmetry caveat). -/
inductive Tok | opn | cls | atomA | atomB
  deriving DecidableEq, Repr

/-- Bracket delta: `+1` open, `−1` close, `0` for either atom flavour. -/
def delta : Tok → Int
  | .opn => 1
  | .cls => -1
  | _    => 0

/-- Total bracket balance of a token list (toy `pbalance`). -/
def tot (e : List Tok) : Int := (e.map delta).sum

/-- Running balance of the first `n` tokens. -/
def bal (e : List Tok) (n : Nat) : Int := tot (e.take n)

/-! ## The consumer goal and its assembler — both already exist (prior bricks).

`Goal` (toy `SeqBodyProps`) is a conjunction of three primitive facts the downstream stage wants.
`assemble` ([[ref-parametric-assembler-extraction]]) bundles the three primitives into it — the
*assemble* half is done; what's missing is *producing* the primitives.  `abbrev`, not `def`, so
`decide` can synthesize the bounded-∀ `Decidable` instances. -/

/-- Primitive 1 (toy): the body is balanced overall. -/
abbrev Balanced (ts : List Tok) : Prop := tot ts = 0

/-- Primitive 2 (toy): no prefix underflows — every prefix balance is `≥ 0` (Dyck prefix law). -/
abbrev PrefixNonneg (ts : List Tok) : Prop := ∀ i, i < ts.length + 1 → bal ts i ≥ 0

/-- Primitive 3 (toy): the body does not start with a closer — `bal ts 1 ≥ 0`.  Stand-in for the
    "content-start head" the real joint must supply. -/
abbrev HeadNonneg (ts : List Tok) : Prop := bal ts 1 ≥ 0

/-- The consumer goal (toy `SeqBodyProps`): all three primitives at once. -/
abbrev Goal (ts : List Tok) : Prop := Balanced ts ∧ PrefixNonneg ts ∧ HeadNonneg ts

/-- **The assembler** (toy `seqBodyProps_assemble`).  Bundles the three primitives into `Goal`.  It
    already exists — the residual before the joint is *producing* its three inputs. -/
theorem assemble {ts : List Tok}
    (h1 : Balanced ts) (h2 : PrefixNonneg ts) (h3 : HeadNonneg ts) : Goal ts :=
  ⟨h1, h2, h3⟩

/-! ## The deliverable — the recursion's eventual single output.

`Dyck` is the *structured body witness* the not-yet-built producer (the large recursion) will
eventually hand back: balanced AND prefix-nonneg.  Crucially it does NOT carry `HeadNonneg`
separately — the joint recovers that for free (Reflection 237). -/

/-- The producer's eventual deliverable (toy `SafeBody`/windowed structured witness): one fact. -/
abbrev Dyck (ts : List Tok) : Prop := Balanced ts ∧ PrefixNonneg ts

/-! ## The CONSUMER JOINT — built before the producer, fully proven today. -/

/-- `HeadNonneg` is RECOVERED from `PrefixNonneg` (at prefix `1`), so the deliverable need not carry
    it — the toy of Reflection 237's "recover the back half's one missing input, content-start, for
    free from the located body". -/
theorem HeadNonneg_of_PrefixNonneg {ts : List Tok} (hp : PrefixNonneg ts) : HeadNonneg ts := by
  cases ts with
  | nil => decide
  | cons t rest => exact hp 1 (by simp only [List.length_cons]; omega)

/-- **The consumer joint** (toy `seqBodyProps_of_windowed_safebody`).  Takes the recursion's eventual
    deliverable `Dyck ts` as a bare hypothesis and produces the consumer goal `Goal ts` — by deriving
    the three primitives from the one deliverable and feeding the existing `assemble`.  Fully proven,
    no `sorry`: the brick built *before* the producer. -/
theorem joint {ts : List Tok} (h : Dyck ts) : Goal ts := by
  obtain ⟨hb, hp⟩ := h
  exact assemble hb hp (HeadNonneg_of_PrefixNonneg hp)

/-! ## The principle in action — same conclusion, residual of a DIFFERENT SHAPE.

`residual_scattered` and `residual_one_shape` both conclude `Goal ts`.  Before the joint, the
residual is a *scatter*: THREE primitive obligations to produce (one of them — `HeadNonneg` —
redundant).  After the joint, it is *one typed boundary*: produce the single `Dyck` deliverable.
Same goal, retyped residual — the retype is the progress. -/

/-- BEFORE the joint: the residual is a SCATTER — you must produce all three primitives, then
    assemble.  Three inputs, three things the producer must "match". -/
theorem residual_scattered {ts : List Tok}
    (h1 : Balanced ts) (h2 : PrefixNonneg ts) (h3 : HeadNonneg ts) : Goal ts :=
  assemble h1 h2 h3

/-- AFTER the joint: the residual is ONE shape — produce the single `Dyck` deliverable; the joint
    does the rest (and recovers `HeadNonneg` for free).  The producer now has exactly one contract:
    deliver `Dyck`. -/
theorem residual_one_shape {ts : List Tok} (h : Dyck ts) : Goal ts := joint h

/-! ## The faithful-mirror caveat (Reflections 232 / 241) — name what the abstraction can't reach.

A shared abstraction discharges exactly the obligations at ITS granularity.  `Dyck` constrains only
the bracket structure (`delta` is blind to atom flavours), so an obligation about the atom *payload*
lives BELOW its granularity — the joint cannot supply it.  The honest mirror carries it as an
explicit input rather than pretending to discharge it. -/

/-- A payload obligation BELOW the deliverable's granularity: the body contains no `atomB`.  `Dyck`
    is blind to it (`delta atomA = delta atomB = 0`). -/
abbrev NoAtomB (ts : List Tok) : Prop := ∀ t ∈ ts, t ≠ Tok.atomB

/-- The richer consumer goal also wants the below-granularity fact. -/
abbrev GoalPlus (ts : List Tok) : Prop := Goal ts ∧ NoAtomB ts

/-- **The faithful mirror joint.**  It collapses the three `Dyck`-derived primitives into the single
    `Dyck` input (the mirror move), but CARRIES `NoAtomB` as an explicit pass-through input — the
    grammar-forced residual the shared abstraction can't reach.  Honest: the signature names exactly
    what the joint cannot discharge. -/
theorem jointFaithful {ts : List Tok} (h : Dyck ts) (h_below : NoAtomB ts) : GoalPlus ts :=
  ⟨joint h, h_below⟩

/-! ## Witnesses. -/

/-- A well-formed body `[ a ]` — balanced, prefix-nonneg, no `atomB`. -/
def good : List Tok := [Tok.opn, Tok.atomA, Tok.cls]

/-- A balanced-but-mis-nested body `] [` — total balance 0, but the first prefix dips to `−1`, so the
    producer cannot even deliver `Dyck`.  The discriminating "balance-0 but not prefix-nonneg" case. -/
def bad : List Tok := [Tok.cls, Tok.opn]

/-- A `Dyck` body that nonetheless contains `atomB` — the witness that `Dyck` does NOT entail the
    below-granularity fact `NoAtomB`. -/
def mixed : List Tok := [Tok.opn, Tok.atomB, Tok.cls]

/-! ### `#eval` — per-prefix balance, the structure the deliverable records. -/

/-- One diagnostic row for prefix length `i` of `ts`. -/
def report (ts : List Tok) (i : Nat) : String :=
  s!"i={i}  bal(i)={bal ts i}  prefix≥0={decide (bal ts i ≥ 0)}"

-- `good`: every prefix ≥ 0 and ends at 0 — the producer's `Dyck` deliverable holds.
/-- info: ["i=0  bal(i)=0  prefix≥0=true", "i=1  bal(i)=1  prefix≥0=true", "i=2  bal(i)=1  prefix≥0=true",
 "i=3  bal(i)=0  prefix≥0=true"] -/
#guard_msgs in
#eval (List.range (good.length + 1)).map (report good)

-- `bad`: prefix at i=1 dips to −1 — NOT `Dyck`; the producer cannot deliver, even though bal(2)=0.
/-- info: ["i=0  bal(i)=0  prefix≥0=true", "i=1  bal(i)=-1  prefix≥0=false", "i=2  bal(i)=0  prefix≥0=true"] -/
#guard_msgs in
#eval (List.range (bad.length + 1)).map (report bad)

-- The residual SHAPE, made visible: a scatter of three vs one typed boundary.
/-- info: "before joint: 3 obligations (Balanced, PrefixNonneg, HeadNonneg) — a scatter" -/
#guard_msgs in
#eval s!"before joint: {3} obligations (Balanced, PrefixNonneg, HeadNonneg) — a scatter"

/-- info: "after joint:  1 obligation  (Dyck) — one typed boundary; HeadNonneg recovered for free" -/
#guard_msgs in
#eval s!"after joint:  {1} obligation  (Dyck) — one typed boundary; HeadNonneg recovered for free"

/-! ### `#guard` — the deliverable decides, the joint fires, the caveat bites. -/

#guard  decide (Dyck good)        -- the producer's deliverable holds for `good`
#guard !decide (Dyck bad)         -- `bad` is balance-0 but prefix-negative — not deliverable
#guard  decide (Dyck mixed)       -- `mixed` IS Dyck …
#guard !decide (NoAtomB mixed)    -- … yet violates the below-granularity fact: Dyck ↛ NoAtomB
#guard  decide (NoAtomB good)     -- `good` has no atomB

/-! ## The theorems at work. -/

/-- The producer's deliverable, here discharged by `decide` (in the real proof, by the recursion). -/
theorem good_Dyck : Dyck good := by decide

/-- End-to-end: the joint turns the one deliverable into the full consumer goal — one line, no
    re-derivation of the three primitives. -/
theorem good_Goal : Goal good := joint good_Dyck

/-- The same via the residual-shape framing: one `Dyck` input suffices. -/
theorem good_one_shape : Goal good := residual_one_shape good_Dyck

/-- `bad` cannot even be delivered: it is not `Dyck` (prefix dips negative). -/
theorem bad_not_Dyck : ¬ Dyck bad := by decide

/-- **The asymmetry, concretely.**  `Dyck` does NOT entail `NoAtomB`: `mixed` is a `Dyck` body that
    violates it.  So the joint genuinely cannot supply `NoAtomB` — it must be an explicit input. -/
theorem Dyck_not_entail_NoAtomB : ∃ ts, Dyck ts ∧ ¬ NoAtomB ts :=
  ⟨mixed, by decide, by decide⟩

/-- The faithful mirror needs both inputs; with both, it delivers the richer goal. -/
theorem good_GoalPlus : GoalPlus good := jointFaithful good_Dyck (by decide)

end ConsumerJointBeforeProducer
