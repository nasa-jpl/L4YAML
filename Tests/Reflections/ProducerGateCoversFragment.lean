/-! # Reflection 507 — a landed producer's gate may cover only a FRAGMENT of the consumer's domain

R506 ([[LocatedContainerRead]]) landed the navigator's terminal READ (located entry ⟹ content). R507
CONSUMES it: it feeds the already-landed navigator `nestedSeq_recseqentry_locate` into that read,
yielding a per-window `FlowBodyContent` carrier-free — retyping R506's residual from execution to
structural ([[ReductionByImport]] / `ref-reduction-by-import`).

But wiring the consumer surfaced the decisive architectural finding of the turn — TWO corrections:

1. **The producer the plan said to BUILD already EXISTS.** The blueprint Next step said "build the
   spine-walk recursion wrapper." Reading the code, that wrapper was already assembled several
   reflections earlier (under a different name, in a different file, from a parallel family of step
   lemmas). So the turn CONSUMES it, not builds it. Lesson: before building a producer a plan calls
   for, check whether it already exists — a stale Next step can name a built artifact.

2. **The landed producer's GATE is STRICTLY STRONGER than the consumer's domain, so it covers only a
   FRAGMENT.** The navigator carries `SeqPathAllSeq tokens (a-1)` (EVERY enclosing frame `[`-typed),
   but the frontier consumer `h_seq_rec` fires on EVERY balanced seq window — including a map-nested
   seq `[{a: [b]}]`'s inner `[b]`, where `SeqPathAllSeq` is FALSE (a `false` from the `{` sits below
   the top) yet `SeqEnclosed` (the TOP frame) still holds. So the navigator serves only the all-seq-path
   FRAGMENT — it is one ARM of a gate-dispatch, and the weak-gate (path-free) remainder is the genuine
   residual, served by a DIFFERENT architecture (the recursion route gated on the weak `SeqEnclosed`,
   which threads descent through its own IH and never reads the global spine).

This is the DUAL of [[ProbeProviderHeadBlindGate]] (`ref-probe-provider-head-blind-gate`): there the
gate was too WEAK (admitted spurious windows the deliverable can't inhabit); here the gate is too STRONG
(excludes valid windows the consumer genuinely needs). Both are found by COMPARING the producer's gate
against the consumer's domain — but in opposite directions.

This demo models a weak consumer gate `Enclosed` (the whole domain), a strictly stronger producer gate
`AllSeqPath` (`AllSeqPath ⟹ Enclosed`, not conversely), the landed navigator gated on the strong one,
a CONCRETE witness in the weak-minus-strong gap (the map-nested seq), and the full producer as a
DISPATCH: the navigator discharges the strong arm; the residual is the weak-only arm.
-/

namespace ProducerGateCoversFragment

/-- The deliverable the consumer wants at every window (models `RecSeqBody` / `FlowBodyContent`). The
    content is irrelevant to the finding — what matters is the GATE that admits each window. -/
def Deliverable (_n : Nat) : Prop := True

/-- The WEAK consumer gate — holds across the whole consumer domain (models `SeqEnclosed`: the TOP
    stack frame is `[`, true for every balanced seq window, map-nested or not). -/
def Enclosed (n : Nat) : Prop := n % 2 = 0

/-- The STRONG producer gate — the navigator's input precondition (models `SeqPathAllSeq`: EVERY stack
    frame is `[`). Strictly stronger than `Enclosed`. -/
def AllSeqPath (n : Nat) : Prop := n % 4 = 0

instance instDecAllSeqPath (n : Nat) : Decidable (AllSeqPath n) :=
  inferInstanceAs (Decidable (n % 4 = 0))

/-- **Strong ⟹ weak** — the producer's gate DOMINATES the consumer's, so the navigator's windows are a
    SUBSET of the consumer's domain (`SeqPathAllSeq` dominates `SeqEnclosed`, the top frame). -/
theorem allseq_imp_enclosed {n : Nat} (h : AllSeqPath n) : Enclosed n := by
  show n % 2 = 0
  calc n % 2 = n % 4 % 2 := (Nat.mod_mod_of_dvd n (by decide)).symm
    _ = 0 % 2 := by rw [show n % 4 = 0 from h]
    _ = 0 := Nat.zero_mod 2

/-- **The landed navigator** — the producer the plan said to BUILD but which already EXISTS, gated on
    the STRONG precondition (models `nestedSeq_recseqentry_locate` + the R506 read). -/
theorem navigator {n : Nat} (_h : AllSeqPath n) : Deliverable n := trivial

/-- **The fragment is STRICT** — a concrete window the WEAK gate admits but the STRONG gate EXCLUDES:
    `Enclosed 2` holds (`2 % 2 = 0`) yet `AllSeqPath 2` fails (`2 % 4 ≠ 0`). This is the map-nested seq
    `[{a: [b]}]`'s `[b]` — `SeqEnclosed` but not `SeqPathAllSeq` — the navigator provably cannot reach. -/
theorem fragment_is_strict : Enclosed 2 ∧ ¬ AllSeqPath 2 :=
  ⟨by show 2 % 2 = 0; decide, by show ¬ (2 % 4 = 0); decide⟩

/-- **The navigator is ONE ARM** — it discharges the consumer's obligation only on the strong-gate
    windows. (The R507 brick `nestedSeq_flowBodyContent_of_locator` is exactly this arm.) -/
theorem navigator_arm : ∀ n, AllSeqPath n → Deliverable n := fun _ h => navigator h

/-- **The residual** — the deliverable on the weak-gate windows the STRONG gate excludes. This is the
    genuine open obligation, served by the path-FREE recursion route, NOT the navigator. -/
def residual : Prop := ∀ n, Enclosed n → ¬ AllSeqPath n → Deliverable n

/-- **The full producer is a DISPATCH** — the navigator (strong arm, LANDED) plus the residual
    (weak-only arm, OWED) together cover the whole consumer domain. The navigator alone does NOT; the
    fragment finding (`fragment_is_strict`) is exactly why the residual arm is non-vacuous. -/
theorem dispatch (h_res : residual) : ∀ n, Enclosed n → Deliverable n :=
  fun n h_enc => if h : AllSeqPath n then navigator h else h_res n h_enc h

/-- The demo deliverable: the landed producer covers a STRICT FRAGMENT (`navigator_arm` +
    `fragment_is_strict`), so it is one dispatch arm; the full obligation closes only with the
    weak-only residual (`dispatch`). The lesson: a stale "build the producer" Next step can name a
    built artifact whose gate covers only part of the consumer's domain. -/
theorem demo :
    (∀ n, AllSeqPath n → Deliverable n)
    ∧ (Enclosed 2 ∧ ¬ AllSeqPath 2)
    ∧ (residual → ∀ n, Enclosed n → Deliverable n) :=
  ⟨navigator_arm, fragment_is_strict, dispatch⟩

end ProducerGateCoversFragment
