/-!
# Reflection 424 — an invariant-NEUTRAL sibling token needs an extra hypothesis to mirror an
invariant-derived edge-token lemma (the separator is invisible to bracket-balance, so the mirror
that is free for the opener is not free for the separator)

Self-contained (core Lean, no `L4YAML` import) toy of the R424 finding.  Threading the field-(i)
`lastNonSep` (`block`'s last `≠ .flowEntry`, the separator-tail mirror of `lastNonOpener`) needed a
coercion to supply the new field via `EntryUnit`.  The existing `lastNonOpener_of_entryUnit` derives
`last ≠ .flowSequenceStart` from `EntryUnit` ALONE — so I expected `lastNonSep_of_entryUnit` to be a
verbatim token-swap.  It is NOT, and the reason is the token's DELTA SIGNATURE under the
bracket-balance invariant:

* The opener `.flowSequenceStart` has bracket-delta `+1` — VISIBLE to the balance invariant.  A lone
  opener has balance `+1 ≠ 0`, so it is not a unit at all; `EntryUnit` alone excludes an opener-last
  at every length.  The mirror is free.
* The separator `.flowEntry` has bracket-delta `0` — NEUTRAL.  A lone separator has balance `0` and
  no proper nonempty prefix, so it IS a unit; `EntryUnit` is blind to it.  `last ≠ sep` does NOT
  follow from `EntryUnit` alone — the singleton needs the content-start head as an extra hypothesis
  (head = last, and a content start is never a separator).  For length `≥ 2` the prefix-`≥ 1`
  condition still works.

The toy makes the delta-signature asymmetry literal.

This is a THIRD way a sibling-token mirror is not free, alongside `SourceGateCollapseBlocksMirror`
(R422, gate-collapse) and `TriggerCoincidenceRelocatesObligation` (R421, relocation).
-/

namespace Tests.Reflections.InvariantNeutralSiblingNeedsHead

set_option autoImplicit false

/-- Toy tokens: a content start, a bracket `opener`/`closer`, and a `sep` separator. -/
inductive Tok | content | opener | closer | sep
  deriving DecidableEq

/-- Bracket-balance delta (toy of `flowBracketDelta`): opener `+1`, closer `-1`; `content` and the
    **separator** `sep` are `0` — the separator is INVISIBLE to the balance invariant. -/
def delta : Tok → Int
  | .opener => 1
  | .closer => -1
  | _ => 0

/-- Running balance (toy of `pbalance`). -/
def bal : List Tok → Int
  | [] => 0
  | t :: ts => delta t + bal ts

/-- A *unit entry* (toy of `EntryUnit`): total balance `0`, every proper nonempty prefix `≥ 1`. -/
def Unit (e : List Tok) : Prop :=
  bal e = 0 ∧ ∀ i, 0 < i → i < e.length → bal (e.take i) ≥ 1

/-- Content predicate (toy of `ContentStartTok`). -/
def isContent : Tok → Bool
  | .content => true
  | _ => false

/-! ## The opener is VISIBLE to the invariant — the lemma is free. -/

/-- A lone `opener` is NOT a unit: its balance is `+1 ≠ 0`.  So `Unit` ALONE excludes an
    `opener`-last even for singletons — `lastNonOpener_of_entryUnit` needs no head hypothesis. -/
theorem unit_excludes_lone_opener : ¬ Unit [Tok.opener] := by
  intro h
  exact absurd h.1 (by decide)

/-! ## The separator is NEUTRAL to the invariant — the mirror is NOT free. -/

/-- A lone `sep` IS a unit: its balance is `0` (the separator is invisible to balance).  The
    invariant cannot exclude it — this is the singleton the mirror lemma cannot cover. -/
theorem unit_admits_lone_sep : Unit [Tok.sep] := by
  refine ⟨by decide, ?_⟩
  intro i hi0 hilt
  simp at hilt
  omega

/-- **NEGATIVE** — "last ≠ sep" does NOT follow from `Unit` alone: refuted by `[sep]` (a unit whose
    last token IS a separator).  So the mirror genuinely needs an extra hypothesis. -/
theorem not_lastNonSep_from_unit :
    ¬ (∀ e, Unit e → ∀ (h : e ≠ []), e.getLast h ≠ Tok.sep) := by
  intro hall
  exact hall [Tok.sep] unit_admits_lone_sep (by simp) (by simp)

/-! ## The content-start head supplies the missing strength. -/

/-- **POSITIVE** — the head-content hypothesis EXCLUDES the bad `[sep]` witness: its head is `sep`,
    not content.  So `Unit e ∧ (head is content)` recovers `last ≠ sep` at the singleton (head =
    last), exactly as `lastNonSep_of_entryUnit_contentHead` does. -/
theorem head_content_rules_out_lone_sep :
    isContent (([Tok.sep]).head (List.cons_ne_nil _ _)) = false := by decide

#guard delta Tok.opener == 1     -- opener: VISIBLE to balance (excluded by the invariant alone)
#guard delta Tok.sep == 0        -- separator: NEUTRAL (admits the singleton — needs the head)

end Tests.Reflections.InvariantNeutralSiblingNeedsHead
