/-!
# Reflection 488 — a width-parametric carrier lemma is VACUOUS at the recursion's ROOT SEED when its
keying guard is provably false there: the root and the interior satisfy DIFFERENT guards.

Self-contained (core Lean, no `L4YAML` import) toy recording the de-risk that step γ surfaced: the
"instantiate the carrier chain at the root to seed the recursion" plan is a VACUITY dead-end, because
the chain is keyed on a guard that is provably FALSE at the outermost window.

**The setup.**  The seq carrier chain R485→R486→R487 (`seqEnclosingLocate_of_seqOpener_nested`,
`seqWidthEnc_of_recIH`, `seqLocalCarrier_of_recIH`) is window-PARAMETRIC: each lemma takes a window
`[lo, hi)` and is keyed on `FlowBodyContentDeep tokens lo hi`.  The last seq residual is the ROOT
carrier `SeqInteriorSeparators tokens 2 (size-2)`, and the obvious move is to instantiate the chain at
the root span `[2, size-2)` to seed it.

**The trap.**  `flowBodyContentDeep_root_seed_false` machine-checks
`¬ FlowBodyContentDeep tokens 2 (size-2)` (on `[[]]`): the deep guard is a `∀`-over-all-depths the
producer cannot establish at the top-level body, and `recseqentry_window_dispatch` even RELIES on its
falsity-causing field (`openerContentStart`) to exclude the empty-bracket leaf — a case that is REAL.
So instantiating the `FlowBodyContentDeep`-keyed chain at the root is VACUOUS: its `h_deep` hypothesis
is unprovable there.  The chain is TRUE and useful at every DESCENDED (nested) window — where
`FlowBodyContentDeep` holds — but not at the outermost one.  "Window-parametric" ≠ "usable at the
boundary instance."

**The fix.**  The root seed needs the root-TRUE parallel family: `FlowBodyContentDeepSeq` (R393's
re-scoped guard, true at the root, coinciding with `FlowBodyContentDeep` at nested seq-context
positions).  The codebase already carries `_seq` twins (`seqWindow_flowBodyContent_seq`,
`seqWindowRecSeqBody_seq`, `seqRec_of_carrier_and_windowFacts_seq`) for exactly this; the OPEN brick is
the `_seq` re-thread of the R485→R486 enclosing-locate so the root carrier's `h_widthEnc` is non-vacuous.

**The transferable rule.**  Before SEEDING a width/window recursion at its ROOT (outermost) instance
with a window-parametric lemma, check the lemma's keying GUARD is not provably FALSE there.  The root
and the interior windows can satisfy DIFFERENT guards (an interior-only `∀`-over-depths guard collapses
at the top level), so the interior lemma — correct and useful everywhere inside — is vacuous at the
seed.  Seed with the boundary-TRUE parallel family, not the interior lemma.  This is the consume-side
companion to root-seed-first (`ref-universal-producer-root-seed-first`): the root seed is the first
brick, but it needs the right GUARD, and the interior guard is the wrong one.

This toy models windows as `Nat` (0 = root/outermost, ≥1 = nested), the interior guard `Deep` (false at
0), the root-true guard `DeepSeq` (the re-scoped twin), and shows the interior carrier lemma cannot seed
the root while the `_seq` twin can.
-/

namespace RootSeedNeedsRootTrueGuard

set_option autoImplicit false

/-- A window index: `0` is the ROOT (outermost body), `≥ 1` is a NESTED seq window. -/
abbrev Win := Nat

/-- **The interior guard** — the toy `FlowBodyContentDeep tokens lo hi`: a `∀`-over-depths fact that
    holds at every NESTED window but COLLAPSES at the root (the empty-bracket leaf the dispatch relies
    on excluding is real at the top level).  Modeled: false at `0`, true at `≥ 1`. -/
def Deep (w : Win) : Prop := 1 ≤ w

/-- **The root-true guard** — the toy `FlowBodyContentDeepSeq` (R393's re-scoped twin): holds
    everywhere, including the root.  Coincides with `Deep` at nested windows; differs at the root. -/
def DeepSeq (_w : Win) : Prop := True

/-- The carrier the chain builds — modeled as the root-true guard itself (so building it at the root is
    a genuine obligation, and the interior guard `Deep` is the wrong key for it). -/
def Carrier (w : Win) : Prop := DeepSeq w

/-! ### The root is where the interior guard is FALSE — `flowBodyContentDeep_root_seed_false` in toy. -/

/-- The interior guard is PROVABLY FALSE at the root seed (toy `flowBodyContentDeep_root_seed_false`). -/
theorem deep_false_at_root : ¬ Deep 0 := by intro h; exact Nat.not_succ_le_zero 0 h

/-- The root-true guard HOLDS at the root seed — the reason the `_seq` family can seed where `Deep`
    cannot. -/
theorem deepSeq_true_at_root : DeepSeq 0 := trivial

/-- At every NESTED window the interior guard holds — so the interior lemma is genuinely useful there;
    its vacuity is localized to the boundary, which is exactly the seed. -/
theorem deep_at_nested (w : Win) (h : 1 ≤ w) : Deep w := h

/-- Off the root the two families coincide: the interior guard implies the root-true one everywhere
    (the re-scope only ADDS the root, it does not weaken the interior). -/
theorem deepSeq_of_deep {w : Win} (_h : Deep w) : DeepSeq w := trivial

/-! ### The two carrier lemmas — same conclusion, different key.

`widthEnc_of_deep` is the toy R486/R487 chain (keyed on `Deep`); `widthEnc_of_deepSeq` is its `_seq`
twin (keyed on `DeepSeq`).  Both build `Carrier w`; only the second can seed the root. -/

/-- **The interior carrier lemma** (toy R486/R487): builds the carrier from the interior guard `Deep`.
    Correct and useful at every nested window. -/
theorem widthEnc_of_deep (w : Win) (h : Deep w) : Carrier w := deepSeq_of_deep h

/-- **The `_seq` twin** (the OPEN brick): builds the carrier from the root-true guard `DeepSeq`. -/
theorem widthEnc_of_deepSeq (w : Win) (h : DeepSeq w) : Carrier w := h

/-! ### The seed: only the `_seq` twin closes the root. -/

/-- **The root carrier from the `_seq` twin** — the seed succeeds because `DeepSeq` is root-true. -/
theorem rootCarrier_via_seq : Carrier 0 := widthEnc_of_deepSeq 0 deepSeq_true_at_root

/-- **The interior chain CANNOT seed the root.**  Any attempt to seed the root via `widthEnc_of_deep`
    must discharge `Deep 0`, which is false — so the only way to obtain `Carrier 0` through the
    interior lemma is from an impossible hypothesis.  Formally: feeding the interior lemma a (false)
    `Deep 0` would prove anything, witnessing the vacuity. -/
theorem interiorChain_at_root_is_vacuous (h : Deep 0) : Carrier 0 :=
  -- reachable ONLY under the false hypothesis `Deep 0` (`deep_false_at_root`) — never dischargeable.
  widthEnc_of_deep 0 h

/-- Sanity: the interior lemma is NOT useless — at a nested window it builds the carrier fine. -/
theorem interiorChain_at_nested : Carrier 3 := widthEnc_of_deep 3 (deep_at_nested 3 (by decide))

end RootSeedNeedsRootTrueGuard
