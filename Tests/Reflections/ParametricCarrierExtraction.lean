/-! # Reflection 505 — lift a recursion's sole carrier use into an abstract provider hypothesis

R504 ([[ContentSurfacingLocatorTwin]]) isolated, by reading `seqWindowRecSeqBody_seq_general` against
`seqChild_safeBodyUnit_seq`, that the carrier `SeqInteriorSeparators` is consumed in EXACTLY ONE place —
sourcing the CURRENT window's `FlowBodyContent`; the descend (off the content-free width IH) and the
advance (its `≠ .key` premise paid from the content guard's own separator fact) are already carrier-free.

R505 acts on that finding: `seqWindowRecSeqBody_seq_of_provider` is the recursion with that one carrier
use lifted into an abstract per-window content PROVIDER hypothesis. ANY provider that supplies each
window's content from its guard drives the recursion; the carrier is one such provider. This is
[[ref-parametric-assembler-extraction]] at the recursion level: it does not produce the carrier-free
provider (the hard fixpoint), it NAMES it as the single remaining obligation and proves the rest of the
recursion needs nothing else.

This demo models the extraction with `Body`/`Content`/`Guard`, and — the honest crux — makes the
top-down obstruction concrete: the guard does NOT entail content (`guard_does_not_entail_content`), so the
provider is a genuine extra hypothesis, not eliminable by a guard-only route. The CHILDREN's provider is
free off the body (`childProvider`, R502); only the CURRENT window's content is the top-down seed.
-/

namespace ParametricCarrierExtraction

/-- The depth-`0` separator-successor fact — the one content fact with NO descend-stable, guard-derivable
    form (models `FlowBodyContent.bodySucc`). Opaque to the guard: a real window always satisfies it, but
    it is not readable off the guard's window/deep/enc fields. Modelled by a predicate the guard cannot
    see. -/
def BodySucc (n : Nat) : Prop := n ≠ 7

/-- The content-free window guard (models `FlowBodyWindow ∧ FlowBodyContentDeepSeq ∧ SeqEnclosed`): it
    pins non-emptiness but NOT `BodySucc`. -/
def Guard (n : Nat) : Prop := 0 < n

/-- The per-window content the dispatch consumes (models `FlowBodyContent`): non-emptiness AND the
    body-successor fact the guard lacks. -/
def Content (n : Nat) : Prop := 0 < n ∧ BodySucc n

/-- The window deliverable (models `RecSeqBody`): it CARRIES `BodySucc`, so its content projects back off
    it for free (R502). -/
def Body (n : Nat) : Prop := 0 < n ∧ BodySucc n

/-- The dispatch+assemble core (models `recseqentry_window_dispatch_seq` + `recseqbody_window_assemble`):
    it CONSUMES the current window's content — the guard alone is not enough, because `BodySucc` is
    top-down and unreadable from the guard. -/
def dispatch (n : Nat) (_g : Guard n) (c : Content n) : Body n := c

/-- **The carrier-PARAMETRIC recursion** (models `seqWindowRecSeqBody_seq_of_provider`): driven by an
    abstract per-window content PROVIDER `prov`, the carrier lifted to one hypothesis. The recursion uses
    the provider in EXACTLY one place (to get the current window's content), then runs the dispatch. -/
def recBodyOfProvider (prov : ∀ n, Guard n → Content n) (n : Nat) (g : Guard n) : Body n :=
  dispatch n g (prov n g)

/-- The CARRIER (models `SeqInteriorSeparators`): a global oracle supplying every (valid) window's content. -/
def Carrier : Prop := ∀ n, Guard n → Content n

/-- The carrier provider: read each window's content straight off the carrier — the SOLE carrier use. -/
def carrierProvider (cr : Carrier) : ∀ n, Guard n → Content n := cr

/-- **The carrier recursion is ONE instance of the parametric one** (models
    `seqWindowRecSeqBody_seq_general` as the carrier instance of `seqWindowRecSeqBody_seq_of_provider`). -/
def recBodyOfCarrier (cr : Carrier) (n : Nat) (g : Guard n) : Body n :=
  recBodyOfProvider (carrierProvider cr) n g

/-- The carrier recursion is DEFINITIONALLY the parametric one fed the carrier provider — the abstraction
    is faithful, the carrier loses nothing. -/
theorem carrier_is_an_instance (cr : Carrier) (n : Nat) (g : Guard n) :
    recBodyOfCarrier cr n g = recBodyOfProvider (carrierProvider cr) n g := rfl

/-! The honest scope: the provider for the CHILDREN is FREE (R502); the CURRENT window's is top-down. -/

/-- **R502 — the CHILD's content is a FREE projection of the child's own body.** So the provider,
    RESTRICTED to children (downstream of the IH's produced body), needs no carrier: read it off the body. -/
theorem childProvider {n : Nat} (b : Body n) : Content n := b

/-- **The current window's content is NOT derivable from its own guard** — the structural crux. `Guard 7`
    holds (`0 < 7`) yet `Content 7` fails (`BodySucc 7 = 7 ≠ 7` is `False`): the guard cannot project the
    body-successor fact. So `recBodyOfProvider`'s `prov` is a genuine extra hypothesis, not eliminable by
    any guard-only `∀ n, Guard n → Content n` — exactly the carrier's irreducible job, and exactly why its
    root seed is the open obligation. -/
theorem guard_does_not_entail_content : Guard 7 ∧ ¬ Content 7 :=
  ⟨by unfold Guard; decide, by unfold Content BodySucc; decide⟩

/-- The parametric recursion needs EXACTLY the provider and nothing else carrier-shaped: feeding it ANY
    provider (carrier-derived, or a hypothetical carrier-free one) drives the whole recursion. The
    carrier-free goal is therefore reduced to producing one provider. -/
theorem recursion_needs_only_provider (prov : ∀ n, Guard n → Content n) (n : Nat) (g : Guard n) :
    Body n := recBodyOfProvider prov n g

/-- Non-vacuity: the body is genuine — a leaf at `n = 0` has no body, so the provider only fires where the
    recursion produced a real window. -/
theorem body_needs_nonempty : ¬ Body 0 := by unfold Body BodySucc; decide

/-- The demo deliverable: the parametric recursion exists for any provider, and the carrier is one
    instance — the carrier-free obligation is now the single hypothesis `∀ n, Guard n → Content n`. -/
theorem demo : ((∀ n, Guard n → Content n) → ∀ (n : Nat), Guard n → Body n)
    ∧ (Carrier → ∀ (n : Nat), Guard n → Body n) :=
  ⟨fun prov n g => recBodyOfProvider prov n g, fun cr n g => recBodyOfCarrier cr n g⟩

end ParametricCarrierExtraction
