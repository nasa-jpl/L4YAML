/-!
# Reflection 388 — locate which consumer a refined-GATE producer actually serves by comparing gate
STRENGTH against each candidate consumer's window-guard in BOTH directions, not by deliverable-shape
resemblance.

Self-contained core-Lean toy of L4YAML R388.  Wiring the forward emission locator
(`nestedSeq_recseqentry_locate`, R386 / `nestedSeq_safeBodyUnit_of_locator`, R387) toward the seq
frontier, the CONSUME plan said it "feeds `seqRoot_seqInteriorSeparators`'s `desc` hypothesis".  The
de-risk found that to be a MISATTRIBUTION: `desc` quantifies over a GENERAL gated window
(`SeqTypedInterior`, where `tokens[a-1]` may be a `.flowEntry` separator) and is served by the BACKWARD
`seqEnclosingOpener_of_gate` scan; the forward locator's window is STRICTLY NARROWER
(`h_opener : balance (a-1) a = 1` forces `tokens[a-1]` to BE the opener ⇒ a complete nested-seq
interior).  Its genuine downstream is `h_seq_rec`, whose guard is WEAKER (bracket facts only), so a
gate-strengthening bridge is owed before it plugs in.

The transferable rule: given ONE producer `P` (deliverable `D` under a refined gate `GP`) and SEVERAL
candidate consumers, locate `P` by comparing `GP` against each consumer's window-guard in BOTH
directions — too-NARROW vs a broader consumer ⇒ that consumer needs a DIFFERENT producer; too-STRONG vs
a weaker consumer ⇒ a gate-strengthening BRIDGE is owed; only a MATCH is a drop-in.  The diagnostic is a
boundary-token membership test: the conjunct `GP` FORCES that the broad window leaves FREE.

Mapping to L4YAML: `GP` ~ the locator's `SeqTypedInterior` + `SeqPathAllSeq` + `h_opener` gate (narrow);
`D` ~ `RecSeqBody ((take b).drop a)`; `GdescWide` ~ `desc`'s general `SeqTypedInterior` window (broader);
`Grec` ~ `h_seq_rec`'s bracket-only guard (weaker, different conjunct); `bridge` ~ the owed
gate-strengthening (`h_seq_rec` guards + global well-typedness ⇒ the locator's gate).

POSITIVE: `dropIn` — when the consumer's gate matches `GP`, the producer fits directly;
`weakSlot_via_bridge` — with the gate-strengthening bridge, `P` serves the weak slot.
NEGATIVE: `tooNarrow_for_broad` — `GdescWide` admits witnesses `GP` excludes, so `P` cannot serve the
broad consumer; `tooStrong_vs_weak` — the naive bridge `Grec → GP` is false, so a bridge is owed;
`discriminator` — the boundary conjunct `GP` forces that the broad window leaves free.

Sharpens [[ref-conjunctive-consumer-gates-on-orthogonal-axis]] (decompose a consumer by conjunct vs
locate a producer by gate strength).
-/

namespace Tests.Reflections.LocateConsumerByGateStrength

set_option autoImplicit false

/-- The producer's REFINED gate (narrow): divisible by 6. -/
def GP (n : Nat) : Prop := n % 6 = 0
/-- The deliverable the producer makes under its gate. -/
def D (n : Nat) : Prop := n % 2 = 0 ∧ n % 3 = 0
/-- A BROAD consumer's quantified window (weaker than `GP`): even. -/
def GdescWide (n : Nat) : Prop := n % 2 = 0
/-- A WEAK consumer slot's guard (weaker than `GP`, a different conjunct): divisible by 3. -/
def Grec (n : Nat) : Prop := n % 3 = 0

/-- The producer: delivers `D` under its refined gate `GP`. -/
theorem producer (n : Nat) (h : GP n) : D n := by
  unfold GP at h; exact ⟨by omega, by omega⟩

/-- **POSITIVE (drop-in).** When the consumer's gate MATCHES `GP`, the producer fits directly. -/
theorem dropIn (n : Nat) (h : GP n) : D n := producer n h

/-- **NEGATIVE — too NARROW for the broad consumer.**  `GdescWide` admits witnesses `GP` excludes,
    so the producer cannot serve `∀ n, GdescWide n → D n`; that consumer needs a DIFFERENT producer
    (in L4YAML: `desc`, served by the backward enclosing-opener scan). -/
theorem tooNarrow_for_broad : ∃ n, GdescWide n ∧ ¬ GP n := by
  refine ⟨2, ?_, ?_⟩ <;> simp [GdescWide, GP]

/-- **NEGATIVE — too STRONG vs the weak consumer slot.**  `Grec` is weaker than `GP`, so the naive
    bridge `Grec → GP` is FALSE; a gate-strengthening bridge is owed before the producer plugs in. -/
theorem tooStrong_vs_weak : ∃ n, Grec n ∧ ¬ GP n := by
  refine ⟨3, ?_, ?_⟩ <;> simp [Grec, GP]

/-- The GATE-STRENGTHENING BRIDGE: the weak guard PLUS a global fact (even) recovers `GP`. -/
theorem bridge (n : Nat) (h_rec : Grec n) (h_global : n % 2 = 0) : GP n := by
  unfold Grec at h_rec; unfold GP; omega

/-- **POSITIVE (via bridge).** With the bridge, the producer serves the weak consumer slot. -/
theorem weakSlot_via_bridge (n : Nat) (h_rec : Grec n) (h_global : n % 2 = 0) : D n :=
  producer n (bridge n h_rec h_global)

/-- **The DIAGNOSTIC discriminator** — the conjunct `GP` FORCES (`n % 3 = 0`) that the broad window
    leaves FREE: an even `n` need not be divisible by 3.  That single forced-vs-free fact proves the
    producer's domain is a strict subset of the broad consumer's, read off — not surveyed. -/
theorem discriminator : ∃ n, GdescWide n ∧ ¬ (n % 3 = 0) := by
  refine ⟨2, ?_, ?_⟩ <;> simp [GdescWide]

#guard 6 % 6 == 0        -- the producer's gate holds on a div-6 witness
#guard !(2 % 6 == 0)     -- but fails on an even-but-not-div-6 witness (too narrow for "even")
#guard !(3 % 6 == 0)     -- and on a div-3-but-not-div-6 witness (too strong for "div-3")

end Tests.Reflections.LocateConsumerByGateStrength
