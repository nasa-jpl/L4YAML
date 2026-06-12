/-!
# Reflection 396 — dual-bracket a global contract: the produce-side joint reduces it to
boundary-from-sibling + one interior field, whose shape confirms the substrate.

Self-contained core-Lean toy of L4YAML R396, the increment after R395 named the redirected GLOBAL
producer's contract (`GlobalFlowSeqOpenerAdj`) and landed its CONSUME-side restriction
(`global → window field`, toward the frontier consumer). R396 lands the DUAL PRODUCE-side joint:
reduce the global contract to (i) the BOUNDARY facts an existing SIBLING whole-structure lemma already
delivers + (ii) ONE flat INTERIOR field over the body window.

The two duals BRACKET the global contract and MEET at the same window-field shape (`WindowField l 2
(len-2)`): the consume side reads the window field OUT of the global contract; the produce side reads
the global contract BACK from (boundary + window field). Two payoffs of the produce side:

1. **Isolates the residual.** Every outer/boundary case (`k=0` stream head, `k=1` outer opener whose
   successor is the body head, `k=size-2` outer close) discharges HERE from the sibling's facts, so the
   producer's true residual collapses to exactly the interior field over `[2, size-2)`.
2. **Confirms the substrate.** The interior field's SHAPE = `WindowField l 2 (len-2)` = the recursive
   BODY producer's per-window deliverable — the residual-shape NAMES the producer's home.

POSITIVE: `windowField_of_global` (consume side — global → any window) and `globalAdj_of_structure`
(produce side — boundary + interior window field → global) are DUALS meeting at `WindowField`;
`globalAdj_goodStructure` (the contract is satisfiable on a real nested structure).
NEGATIVE: `windowField_insufficient` — the interior field ALONE does NOT entail the global contract
(`badStructure` has a vacuous interior window yet its OUTER opener `k=1` has a non-content successor),
so the sibling's boundary/head facts are LOAD-BEARING, not derivable from the interior.

Mapping to L4YAML: `GlobalAdj` ~ `GlobalFlowSeqOpenerAdj`; `windowField_of_global` ~
`flowSeqOpenerAdj_window_of_global` (R395 consume side); `globalAdj_of_structure` ~
`globalFlowSeqOpenerAdj_of_structure` (R396 produce side); the `h_t0`/`h_close`/`h_head` boundary facts
~ the four boundary facts `scanFiltered_emitSeq_nonempty_structure` already delivers; the residual
`WindowField l 2 (len-2)` ~ the body opener field threadable through
`emitList_body_filtered_characterization`.
-/

namespace Tests.Reflections.ProduceJointBracketsGlobalContract

set_option autoImplicit false

inductive Tok | sstart | send | opn | cls | content
  deriving DecidableEq, Repr, BEq, Inhabited

/-- A content-start token (= `isFlowContentStart`): content, or a sequence opener. -/
def isContentStart (t : Tok) : Prop := t = .content ∨ t = .opn

/-- The GLOBAL contract (= `GlobalFlowSeqOpenerAdj`): over the WHOLE list, every `opn` with a
    non-`cls` successor is followed by a content-start. `List.range`-bounded so it is `decide`-able. -/
def GlobalAdj (l : List Tok) : Prop :=
  ∀ i ∈ List.range l.length, i + 1 < l.length →
    l[i]! = .opn → l[i+1]! ≠ .cls → isContentStart l[i+1]!

/-- The window-relative INTERIOR field (= `FlowBodyContentDeepSeq.openerContentStart`'s shape over
    `[lo, hi)` = the recursive BODY producer's per-window deliverable). -/
def WindowField (l : List Tok) (lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i → i + 1 < hi → l[i]! = .opn → l[i+1]! ≠ .cls → isContentStart l[i+1]!

/-- **CONSUME side (R395 dual)** (= `flowSeqOpenerAdj_window_of_global`): the global contract restricts
    to any window field by ONE `omega` bound step. -/
theorem windowField_of_global {l : List Tok} {lo hi : Nat}
    (h : GlobalAdj l) (h_hi : hi ≤ l.length) : WindowField l lo hi := by
  intro i _ hihi ho hne
  exact h i (List.mem_range.mpr (by omega)) (by omega) ho hne

/-- **PRODUCE side (R396)** (= `globalFlowSeqOpenerAdj_of_structure`): the global contract is
    REBUILT from the sibling's four boundary facts + ONE interior window field over `[2, len-2)`.
    A `getElem!` case split on `k`: `k=0` contra (`sstart ≠ opn`); `k=1` is `h_head`; `2 ≤ k` interior
    is `h_body`; `k+1 = len-2` contra the `≠ cls` premise via `h_close`; `k = len-2` contra
    (`cls ≠ opn`). Every boundary discharges from a sibling fact ⇒ the producer's residual = `h_body`. -/
theorem globalAdj_of_structure {l : List Tok}
    (h_sz : 5 ≤ l.length)
    (h_t0 : l[0]! = .sstart)
    (h_close : l[l.length - 2]! = .cls)
    (h_head : isContentStart l[2]!)
    (h_body : WindowField l 2 (l.length - 2)) :
    GlobalAdj l := by
  intro k _ hk1 hopen hne
  by_cases h0 : k = 0
  · subst h0; rw [h_t0] at hopen; exact absurd hopen (by decide)
  by_cases h1 : k = 1
  · subst h1; exact h_head
  have hk2 : 2 ≤ k := by omega
  by_cases hb : k + 1 < l.length - 2
  · exact h_body k hk2 hb hopen hne
  by_cases hb2 : k + 1 = l.length - 2
  · rw [hb2] at hne; exact absurd h_close hne
  have hk_eq : k = l.length - 2 := by omega
  rw [hk_eq] at hopen; rw [h_close] at hopen; exact absurd hopen (by decide)

/-- A real nested structure `[sstart, opn, opn, content, cls, cls, send]` — an outer seq enclosing an
    inner seq (openers at positions 1 and 2). The contract holds GLOBALLY. -/
def goodStructure : List Tok :=
  [.sstart, .opn, .opn, .content, .cls, .cls, .send]

/-- **POSITIVE — the contract is satisfiable** on the nested structure (both openers `k=1`/`k=2`
    fire non-vacuously: successors `opn` and `content`, both content-starts). -/
theorem globalAdj_goodStructure : GlobalAdj goodStructure := by
  unfold GlobalAdj isContentStart goodStructure; decide

/-- Same boundary facts the produce-side joint consumes, here checked directly on `goodStructure`
    (in L4YAML these come free from the sibling `scanFiltered_emitSeq_nonempty_structure`). -/
theorem goodStructure_boundary :
    goodStructure[0]! = Tok.sstart ∧
    goodStructure[goodStructure.length - 2]! = Tok.cls ∧
    isContentStart goodStructure[2]! := by
  refine ⟨by decide, by decide, ?_⟩
  unfold isContentStart goodStructure; decide

/-- A structure whose INTERIOR window `[2, len-2) = [2, 2)` is EMPTY (so `WindowField` holds
    vacuously), but whose OUTER opener at `k=1` has successor `send` — NOT a content-start. -/
def badStructure : List Tok := [.sstart, .opn, .send, .cls]

theorem windowField_badStructure : WindowField badStructure 2 (badStructure.length - 2) := by
  intro i hlo hhi
  exfalso
  have hlen : badStructure.length = 4 := by decide
  omega

theorem globalAdj_badStructure_false : ¬ GlobalAdj badStructure := by
  unfold GlobalAdj isContentStart badStructure; decide

/-- **NEGATIVE — the interior field ALONE does not entail the global contract.**  `badStructure`
    satisfies `WindowField _ 2 (len-2)` (its interior window is empty) yet `GlobalAdj badStructure` is
    FALSE (the OUTER opener `k=1` has a non-content successor `send`).  So the sibling's boundary/head
    facts (`h_head` here) are LOAD-BEARING — the produce-side joint must CITE the sibling, not fold the
    boundaries into the interior field. -/
theorem windowField_insufficient :
    ¬ ∀ l, WindowField l 2 (l.length - 2) → GlobalAdj l := fun h =>
  globalAdj_badStructure_false (h badStructure windowField_badStructure)

#guard goodStructure.length == 7
#guard goodStructure[1]! == Tok.opn        -- outer opener
#guard goodStructure[2]! == Tok.opn        -- inner opener (interior)
#guard badStructure.length == 4
#guard badStructure[1]! == Tok.opn         -- outer opener ...
#guard badStructure[2]! == Tok.send        -- ... successor not content-start (and ≠ cls): violated

end Tests.Reflections.ProduceJointBracketsGlobalContract
