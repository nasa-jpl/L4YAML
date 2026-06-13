/-!
# Reflection 415 — a de-risked guard-re-scope migration costs ONE clone-with-one-line per consumer; restoring the suppressed arm and supplying the guard's new debt are the SAME case-split

Self-contained (core Lean, no `L4YAML` import) toy model of the (R2) seq-rec producer migration,
the IMPLEMENTATION that landed R414's de-risk.

R414 found the empty-bracket arm was already built in the classify, so the migration onto the
re-scoped guard is a `by_cases`, not new infra ([[ref-restored-arm-already-in-classify]]). R415 is the
COST STRUCTURE of that migration once de-risked:

* When a guard is re-scoped from "DERIVES fact `X` internally" to "takes `X` as a PREMISE" — because
  `X` was the very thing the old field unsoundly over-asserted — `X` RELOCATES from a derived `have`
  inside each consumer to a supplied hypothesis on that consumer's signature. Each consumer migrates by
  a CLONE with exactly ONE line changed: the `have hX := <old guard>.field …` becomes a hypothesis
  `hX`. The additive-parallel clone leaves the old guard and consumers intact, so the increment lands
  green and verified-but-unconsumed with zero risk to the existing chain.

* The case-split that RESTORES the suppressed arm and the supply point for the re-scoped guard's NEW
  premise are ONE AND THE SAME `by_cases`. Re-scoping added the non-degeneracy condition
  (`b ≠ cl`) to the opener field; the suppressed arm is precisely the degenerate case (`b = cl`); so
  `by_cases b = cl` splits them at once — TRUE is the restored arm, FALSE hands the cloned producer its
  `b ≠ cl` premise verbatim.

Mirrors L4YAML R414 → R415:
* `OldGuard.openerContent`  — the all-depth opener field (`FlowBodyContentDeep.openerContentStart`),
  which demands content after EVERY `op`, hence is FALSE at an empty `[ ]` and lets a producer DERIVE
  `b ≠ cl` for free.
* `NewGuard.openerContent`  — the re-scoped field (`FlowBodyContentDeepSeq.openerContentStart`), GUARDED
  by `b ≠ cl`; it cannot self-derive that, so it HOLDS (vacuously) at the empty window.
* `oldProducer` / `newProducer` — the consumer before/after migration; the ONLY difference is the
  derive-vs-supply line for `hne : b ≠ cl` (`recseqentry_seqbracket_oracle` → `…_seq`).
* `migrationCallSite` — the dispatch's `by_cases tokens[lo+1] = .flowSequenceEnd`: ONE split, TRUE
  routes the empty arm, FALSE supplies the cloned producer its premise.
-/

namespace Tests.Reflections.DeriskedMigrationOneClonePerConsumer

set_option autoImplicit false

/-- A toy token kind: an opener `[`, a closer `]`, a content `scalar`, and an entry separator `,`. -/
inductive Tok where
  | op | cl | scal | sep
  deriving DecidableEq, BEq

/-- A content start: a scalar or an opener (mirrors `isFlowContentStart`). -/
def isContent : Tok → Bool
  | .scal | .op => true
  | _ => false

/-- The deliverable, built COMPLETE — one constructor per real shape, INCLUDING the empty bracket
    `emptyE` (the arm a false producer guard would suppress).  `nestedE` carries the interior
    non-emptiness `x ≠ cl` (the head-is-content fact) — the datum the producers source differently. -/
inductive Entry : List Tok → Prop where
  | scalarE : Entry [Tok.scal]
  | emptyE  : Entry [Tok.op, Tok.cl]
  | nestedE (x : Tok) (rest : List Tok) (hne : x ≠ Tok.cl) : Entry (Tok.op :: x :: rest ++ [Tok.cl])

/-- **OLD guard** — the all-depth opener field: after an `op` head, content (mirrors
    `FlowBodyContentDeep.openerContentStart`).  Keyed only on `a = op`; FALSE at an empty `[ ]`. -/
structure OldGuard (a b : Tok) : Prop where
  openerContent : a = Tok.op → isContent b = true

/-- **RE-SCOPED guard** — the opener field GUARDED by non-emptiness `b ≠ cl` (mirrors
    `FlowBodyContentDeepSeq.openerContentStart`).  It can no longer self-derive `b ≠ cl`. -/
structure NewGuard (a b : Tok) : Prop where
  openerContent : a = Tok.op → b ≠ Tok.cl → isContent b = true

/-! ## NEGATIVE — the OLD guard cannot even EXIST at the empty window; the re-scoped guard HOLDS there -/

/-- The old guard is FALSE at the empty bracket (`b = cl`): it would force `isContent cl = true`. -/
theorem oldGuard_false_at_cl : ¬ OldGuard Tok.op Tok.cl := by
  intro g
  have h := g.openerContent rfl
  simp [isContent] at h

/-- The re-scoped guard HOLDS (vacuously) at the empty bracket — its `b ≠ cl` premise is unmet, so the
    opener clause never fires.  This is WHY the empty case must be handled by routing, not the guard. -/
def newGuard_holds_at_cl : NewGuard Tok.op Tok.cl := ⟨fun _ hb => absurd rfl hb⟩

/-! ## The relocation — the OLD guard DERIVES `b ≠ cl`; the re-scoped guard makes it a SUPPLIED premise -/

/-- The OLD guard lets a consumer DERIVE interior non-emptiness for free (the over-strong field at
    work).  This derivation is exactly what the re-scope removes. -/
theorem oldGuard_derives_nonEmpty (b : Tok) (g : OldGuard Tok.op b) : b ≠ Tok.cl := by
  intro hb
  have h := g.openerContent rfl
  rw [hb] at h
  simp [isContent] at h

/-- **OLD producer** — DERIVES `hne` internally from the over-strong guard (the line the migration
    deletes).  Models `recseqentry_seqbracket_oracle`. -/
theorem oldProducer (b : Tok) (rest : List Tok) (g : OldGuard Tok.op b) :
    Entry (Tok.op :: b :: rest ++ [Tok.cl]) :=
  Entry.nestedE b rest (oldGuard_derives_nonEmpty b g)      -- DERIVE line

/-- **NEW producer** — the CLONE with exactly ONE line changed: `hne` is now a SUPPLIED premise, not
    derived; the re-scoped guard `_g` rides along unused for non-emptiness (it carries the recursion,
    elided here).  Models `recseqentry_seqbracket_oracle_seq`. -/
theorem newProducer (b : Tok) (rest : List Tok) (_g : NewGuard Tok.op b) (hne : b ≠ Tok.cl) :
    Entry (Tok.op :: b :: rest ++ [Tok.cl]) :=
  Entry.nestedE b rest hne                                  -- SUPPLY line (the only delta)

/-! ## The dual-role case-split — ONE `by_cases` routes the restored arm AND supplies the producer -/

/-- **The migration's call site.**  A SINGLE `by_cases b = cl` discharges BOTH obligations: the TRUE
    branch is the restored empty arm `Entry.emptyE` (the degenerate discriminator), the FALSE branch
    hands `newProducer` its relocated `b ≠ cl` premise STRAIGHT from the same split.  Models
    `recseqentry_window_dispatch_seq`'s `[`-branch `by_cases tokens[lo+1] = .flowSequenceEnd`. -/
theorem migrationCallSite (b : Tok) (g : NewGuard Tok.op b) :
    Entry (if b = Tok.cl then [Tok.op, Tok.cl] else Tok.op :: b :: ([] : List Tok) ++ [Tok.cl]) := by
  by_cases hb : b = Tok.cl
  · -- TRUE: the restored arm — the constructor the classify already exposes.
    rw [if_pos hb]; exact Entry.emptyE
  · -- FALSE: the SAME `hb : b ≠ cl` is exactly `newProducer`'s supplied premise.
    rw [if_neg hb]; exact newProducer b [] g hb

/-! ## Probes — the discriminator is the negation of the re-scoped guard's added premise -/

-- the old guard's content field is false at `cl` (empty), so the producer's derivation is unavailable …
#guard isContent Tok.cl == false
-- … while it fires at content heads (where the non-empty producer applies) …
#guard isContent Tok.scal == true
#guard isContent Tok.op == true
-- … and the by_cases discriminator `b = cl` is decidable both ways (the one split that does both jobs).
#guard (decide (Tok.cl = Tok.cl)) == true
#guard (decide (Tok.scal = Tok.cl)) == false

end Tests.Reflections.DeriskedMigrationOneClonePerConsumer
