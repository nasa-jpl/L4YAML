import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Nested-`FlowBodyContent` EMISSION-seed availability probe — `(i'-b-B2c-nested-fbc-emission-seed)`

The PROBE the blueprint queued after R348.  R348 settled that the per-window `FlowBodyContent` the
seq `desc` producer needs CANNOT be threaded as a `G`-conjunct (the descend edge re-enters its own
window; the projection runs UP the strength order), combined (relocates the same-window cycle into
the step), or read off the window's own `RecSeqBody` (the R347/R348 cycle).  The ONLY break is an
**EMISSION** source of `FlowBodyContent` per nested sub-value, independent of `RecSeqBody`.

`seqRoot_flowBodyContent` (`SeqInteriorSeparators.lean:1563`) already supplies the TOP window
`[2, size-2)` this way, through `seqRoot_safeBodyUnit = (seqRoot_recseqbody …).toSafeBodyUnit` —
the flat root `RecSeqBody` built straight from emission (`emitList_body_recseqbody`), NEVER from the
`seqWindowRecSeqBody` recursion.  The probe asks: is the SAME emission source available at an
arbitrary NESTED seq sub-value occupying window `[a, b)` — i.e. WITHOUT re-entering the body
recursion (`ref-probe-provider-satisfiable-before-assembler`)?

THE DECISIVE FINDINGS (both `#guard`-backed below, on `[[1,2],9]` and `[1,[2,3]]`):

1. **The nested interior is STORED in the flat root `RecSeqBody`, position-exact.**  Every
   `RecSeqEntry` / `RecSeqBody` / `SafeBodyUnit` / `ContentStartTok` constraint is `.val`-only
   (position-BLIND — see their constructors).  So the nested seq's interior `RecSeqBody`, stored in
   `seqRoot_recseqbody`'s `RecSeqEntry.seq.h_rec` field, sits over the EXACT outer-array slice
   `(tokens.toList.take b).drop a` with the right `.pos`s — no position reconciliation.  The
   ASSEMBLE side is therefore fully LANDABLE now from an emission `RecSeqEntry`: the theorem
   `nestedSeq_safeBodyUnit_of_entry` below produces the windowed `SafeBodyUnit` using ONLY the landed
   `recseqentry_seq_extract` + `interior_window_eq` + `RecSeqBody.toSafeBodyUnit` — NO
   `seqWindowRecSeqBody`, NO carrier.

2. **A standalone RE-SCAN is the WRONG array (the offset gap is real).**  Scanning the inner value
   `[1, 2]` standalone yields the same `.val` sequence but `.pos` OFFSETS shifted by the outer `[`
   (nested-in-context `2,5,7` vs standalone `1,4,6`).  So one canNOT source the nested seed by
   re-applying `seqRoot_safeBodyUnit` to the inner value — its `SafeBodyUnit` is stated over a list
   with the wrong positions.  Extraction from the OUTER `seqRoot_recseqbody` (same array) is the only
   position-correct route.

THE RESIDUAL (`ref-from-located-assembler-direction`, BOTTOM-UP).  The assembler consumes the
enclosing entry's `RecSeqEntry` and a window identity locating it at `[a-1, b]`.  Supplying those at
an arbitrary nested all-seq-path window is the SPINE-WALK that descends `seqRoot_recseqbody`'s stored
`seq.h_rec` fields to the located entry, offset-rebased — exactly the R330–R337 four-arm navigator.
That navigator was DESCOPED ("an ALTERNATIVE driver, not a necessity", `rec_seq_body_nested_project`
docstring) BECAUSE the carrier route (`seqWindowRecSeqBody`) already served the whole domain.  But the
carrier route is precisely what the emission seed exists to ELIMINATE — so eliminating it
UN-DESCOPES the navigator.  The landed `rec_seq_body_nested_project` (`SeqInteriorSeparators.lean:1700`)
is the carrier SHORTCUT (it is `seqWindowRecSeqBody` + `SeqEnclosed`-from-path; it needs
`h_root_carrier` and re-enters the recursion) — so it canNOT serve as the emission seed.  R330's
`SeqNestedProjectProbe` already `#guard`-confirmed the navigator's measure (`body.length` decreases)
and per-descend offset re-basing on these same witnesses — its hard part is already de-risked.

So the answer is the blueprint's NO branch, sharpened: the ASSEMBLE is landed (below); the residual is
the emission-spine-walk LOCATOR — a producer descoped as redundant that becomes necessary again once
the route that subsumed it is the one being removed.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqNestedEmissionSeedProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)

/-! ## The ASSEMBLE side — LANDED, sorry-free, emission-only

Given the enclosing item's emission `RecSeqEntry e` for a nested seq block `e = op :: (interior ++ [cl])`
located at absolute positions `[lo, hi]` (op at `lo`, cl at `hi`), produce the windowed
`SafeBodyUnit ContentStartTok ((take hi).drop (lo+1))` — the nested interior's flat seed, the input
`seqRoot_flowBodyContent` feeds to `seqSeparatorFacts_of_windowed_safebodyunit ▸ flowBodyContent_of_deep`.
Uses ONLY landed lemmas; `seqWindowRecSeqBody` and the carrier never appear. -/
theorem nestedSeq_safeBodyUnit_of_entry
    (tokens : Array (Positioned YamlToken)) (lo hi : Nat)
    (op cl : Positioned YamlToken) (interior : List (Positioned YamlToken))
    (h_lo_hi : lo + 1 ≤ hi) (h_hi_sz : hi < tokens.size)
    (h_entry : RecSeqEntry (op :: (interior ++ [cl])))
    (h_open : op.val = .flowSequenceStart) (h_int_ne : interior ≠ [])
    (h_window : (tokens.toList.take (hi + 1)).drop lo = op :: (interior ++ [cl])) :
    SafeBodyUnit ContentStartTok ((tokens.toList.take hi).drop (lo + 1)) := by
  -- Peel the brackets: the stored interior `RecSeqBody` (EMISSION, not the recursion).
  have h_rec : RecSeqBody interior :=
    recseqentry_seq_extract h_entry op cl interior rfl h_open h_int_ne
  -- Drop the opener to re-base the window onto the interior `[lo+1, hi]`.
  have h_win' : (tokens.toList.take (hi + 1)).drop (lo + 1) = interior ++ [cl] := by
    rw [← List.tail_drop, h_window]
    rfl
  -- The slice identity `interior = (take hi).drop (lo+1)` re-bases the stored body to the window.
  have h_eq : interior = (tokens.toList.take hi).drop (lo + 1) :=
    interior_window_eq tokens (lo + 1) hi interior cl h_lo_hi h_hi_sz h_win'
  -- Project `RecSeqBody → SafeBodyUnit` (the seq `.toSafeBodyUnit` flat coercion).
  exact h_eq ▸ h_rec.toSafeBodyUnit

/-! ## The LOCATOR residual, lifted as a hypothesis (`ref-probe-provider-satisfiable-before-assembler`)

The only thing `nestedSeq_safeBodyUnit_of_entry` does not produce is the located emission `RecSeqEntry`
+ its window identity.  Lifted as an existential `locator`, the whole nested seed assembles in one line
— isolating the spine-walk navigator as the single residual.  `locator`'s satisfiability is structurally
witnessed by `seqRoot_recseqbody`'s stored `seq.h_rec` fields (the `#guard`s below confirm the window
identity holds at the located entry on each witness). -/
theorem nestedSeq_safeBodyUnit_of_locator
    (tokens : Array (Positioned YamlToken)) (a b : Nat)
    (h_b_sz : b < tokens.size)
    (locator : ∃ lo op cl interior,
        lo + 1 = a ∧ a ≤ b ∧                      -- a = lo+1, b = hi: the interior window is [a, b]
        RecSeqEntry (op :: (interior ++ [cl])) ∧
        op.val = .flowSequenceStart ∧ interior ≠ [] ∧
        (tokens.toList.take (b + 1)).drop lo = op :: (interior ++ [cl])) :
    SafeBodyUnit ContentStartTok ((tokens.toList.take b).drop a) := by
  obtain ⟨lo, op, cl, interior, h_a, h_ab, h_entry, h_open, h_int_ne, h_window⟩ := locator
  subst h_a
  exact nestedSeq_safeBodyUnit_of_entry tokens lo b op cl interior (by omega) h_b_sz
    h_entry h_open h_int_ne h_window

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

-- ════════════ Witness N := `[[1, 2], 9]` — nested seq `[1,2]` at interior window [3, 6) ════════════
def nestVal : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"], sc "9"]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit nestVal) with | .ok ts => ts | .error _ => #[]
-- standalone re-scan of the inner value (the WRONG array — positions shifted)
def Ninner : Array (Positioned YamlToken) :=
  match scanFiltered (emit (.sequence .flow #[sc "1", sc "2"])) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:[ 3:"1" 4:, 5:"2" 6:] 7:, 8:"9" 9:] 10:SE  (R330's SeqNestedProjectProbe)
-- located inner-seq entry: op = 2, cl = 6; interior window [3, 6); assembler lo = 2, hi = 6.
#guard N.size == 11
#guard N[2]!.val == .flowSequenceStart        -- op (entry opener)
#guard N[6]!.val == .flowSequenceEnd          -- cl (entry close)
-- the located entry `(take 7).drop 2` IS `op :: (interior ++ [cl])` (the window-identity hypothesis):
#guard ((N.toList.take 7).drop 2).map (·.val)
        == [.flowSequenceStart, .scalar "1" .doubleQuoted, .flowEntry,
            .scalar "2" .doubleQuoted, .flowSequenceEnd]
-- interior is nonempty and re-bases to the nested window [3, 6):
#guard ((N.toList.take 6).drop 3).length == 3
#guard ((N.toList.take 6).drop 3).map (·.val)
        == [.scalar "1" .doubleQuoted, .flowEntry, .scalar "2" .doubleQuoted]

-- FINDING 2 — the offset gap: re-scan VALS match but POS OFFSETS differ (shifted by the outer `[`),
-- so the two positioned lists are NOT equal — a standalone re-scan is the WRONG array.
#guard (((N.toList.take 6).drop 3).map (·.val))
        == (((Ninner.toList.take (Ninner.size - 2)).drop 2).map (·.val))      -- vals agree
#guard (((N.toList.take 6).drop 3).map (·.pos.offset)) == [2, 5, 7]           -- in-context offsets
#guard (((Ninner.toList.take (Ninner.size - 2)).drop 2).map (·.pos.offset)) == [1, 4, 6]  -- standalone
#guard (((N.toList.take 6).drop 3).map (·.pos.offset))
        != (((Ninner.toList.take (Ninner.size - 2)).drop 2).map (·.pos.offset)) -- positions DIFFER

-- ════════════ Witness T := `[1, [2, 3]]` — nested seq `[2,3]` at interior window [5, 8) ════════════
def advVal : YamlValue := .sequence .flow #[sc "1", .sequence .flow #[sc "2", sc "3"]]
def T : Array (Positioned YamlToken) :=
  match scanFiltered (emit advVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:"1" 3:, 4:[ 5:"2" 6:, 7:"3" 8:] 9:] 10:SE
-- located inner-seq entry: op = 4, cl = 8; interior window [5, 8); assembler lo = 4, hi = 8.
#guard T.size == 11
#guard T[4]!.val == .flowSequenceStart        -- op
#guard T[8]!.val == .flowSequenceEnd          -- cl
#guard ((T.toList.take 9).drop 4).map (·.val)
        == [.flowSequenceStart, .scalar "2" .doubleQuoted, .flowEntry,
            .scalar "3" .doubleQuoted, .flowSequenceEnd]
#guard ((T.toList.take 8).drop 5).length == 3
#guard ((T.toList.take 8).drop 5).map (·.val)
        == [.scalar "2" .doubleQuoted, .flowEntry, .scalar "3" .doubleQuoted]

end L4YAML.Proofs.EmitterScannability.SeqNestedEmissionSeedProbe
