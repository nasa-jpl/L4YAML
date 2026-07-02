import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Emission-spine-walk LOCATOR single-step probe — `(i'-b-B2c-nested-fbc-emission-locator)`

The PROBE the blueprint queued after R349.  R349 (`SeqNestedEmissionSeedProbe.lean`) settled that the
nested `FlowBodyContent` emission seed's ASSEMBLE is LANDED (`nestedSeq_safeBodyUnit_of_entry` /
`nestedSeq_safeBodyUnit_of_locator`): given the enclosing emission `RecSeqEntry` and a window identity
`(take (b+1)).drop lo = op :: (interior ++ [cl])`, the windowed `SafeBodyUnit` falls out with NO carrier.
The single residual is the **LOCATOR**: at an all-seq-path interior window `[a, b)`, produce that
enclosing `RecSeqEntry` (stored in the flat root `seqRoot_recseqbody`) + its window identity.

This probe settles the locator's **single-step shape** BEFORE authoring (`ref-from-located-assembler-
direction`, bottom-up).  The blueprint's two candidates:

* **(a)** a SINGLE structural (well-founded on `body.length`) recursion over the flat root `RecSeqBody`,
  offset-tracked — descend `seq.h_rec`, advance past `cons` entries, leaf when the window's enclosing
  entry IS the head entry;
* **(b)** a SEPARATE balance-locate front end (find the opener `p` by `flowBracketBalance_backward_
  open_locate`) THEN walk to the stored entry.

THE DECISIVE FINDING — **option (a): the move decision is pure LENGTH ARITHMETIC, no balance front end.**
Walking `RecSeqBody body` with the absolute base offset `off` of `body` (root: `off = 2`), the head
entry `e` occupies `[off, off + e.length - 1]`, so its interior window is `[off+1, off + e.length - 1)`.
The target interior window start `a` selects the move by comparing `a` against `off + 1` and
`off + e.length` ALONE (`move_trichotomy`, pure `omega`):

* `a = off + 1`            → **LEAF** (`e` is the enclosing entry; read it off);
* `off+1 < a < off+e.length` → **DESCEND** into `e`'s stored interior (`seq.h_rec`), new `off' = off+1`;
* `off+e.length < a`        → **ADVANCE** to `rest`, new `off' = off + e.length + 1`.
(`a = off + e.length` is the close/separator position — never a valid interior start, so the trichotomy
is exhaustive on valid windows.)  R330's `SeqNestedProjectProbe` selected the entry by `flowBracketBalance
= 0` from the active base; this BOTTOM-UP locator, keyed on the window `[a,b)`, needs no such balance call
inside the recursion — balance enters only the correctness side (which entry the slice equals), via the
all-seq-path/`WellTyped` hypotheses, never the decision procedure.  So (a): one `body.length` recursion,
offset by length arithmetic; NO balance-locate front end.

The three R330 moves, each exercised by a witness and `#guard`-confirmed below to classify by length
arithmetic and bottom out at a LEAF whose entry satisfies the window identity
`(take (b+1)).drop lo = op :: (interior ++ [cl])`:

* `[[1,2],9]`  — **direct head**: `a = 3 = off+1` at the root → LEAF immediately, lo = 2;
* `[1,[2,3]]`  — **advance-then-head**: `a = 5 > off+e₀.length = 3` → ADVANCE (off' = 4), then `a = off'+1`
  → LEAF, lo = 4;
* `[[[1,2]]]`  — **descend-into-interior**: `off+1 = 3 < a = 4 < off+e.length = 9` → DESCEND (off' = 3),
  then `a = off'+1` → LEAF, lo = 3.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqNestedEntryLocateProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)

/-! ## The decision is length arithmetic (the (a) finding), sorry-free real code -/

/-- **The move trichotomy is decided by LENGTH ARITHMETIC alone** — `a` against `off+1` and
    `off+L` (`L = e.length`), never by balance.  For any valid interior-window start `a ≥ off+1`
    that is not the impossible close/separator position `off+L`, exactly one of leaf / descend /
    advance fires.  This is the (a)-vs-(b) decision: the recursion's branch selector is pure `omega`,
    so the locator is a single offset-tracked `body.length` recursion — no balance-locate front end. -/
theorem move_trichotomy (off L a : Nat) (h_pos : off + 1 ≤ a) (h_ne : a ≠ off + L) :
    (a = off + 1) ∨ (off + 1 < a ∧ a < off + L) ∨ (off + L < a) := by omega

/-- The three branches are mutually exclusive (no window classifies as two moves) — the recursion's
    dispatch is unambiguous, again by `omega` on the same length data. -/
theorem move_exclusive (off L a : Nat) (h_L : 1 ≤ L) :
    ¬ ((a = off + 1) ∧ (off + 1 < a ∧ a < off + L)) ∧
    ¬ ((a = off + 1) ∧ (off + L < a)) ∧
    ¬ ((off + 1 < a ∧ a < off + L) ∧ (off + L < a)) := by omega

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

-- ════════════ Witness N := `[[1,2],9]` — DIRECT HEAD (a = off+1 at the root) ════════════
def nestVal : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"], sc "9"]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit nestVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:[ 3:"1" 4:, 5:"2" 6:] 7:, 8:"9" 9:] 10:SE   (root body off = 2)
-- target interior window [a, b) = [3, 6); enclosing entry `[1,2]` at [lo, b] = [2, 6].
#guard N.size == 11
-- head entry of the root body = `[ "1" , "2" ]` = (root body).take 5, so L = 5.
#guard (((N.toList.take 9).drop 2).take 5).length == 5
-- MOVE: a = 3, off = 2, L = 5 → a == off+1 = 3 → LEAF (direct head), lo = off = 2.
#guard decide ((3 : Nat) == 2 + 1)                        -- leaf predicate fires
#guard decide (¬ (2 + 5 < (3 : Nat)))                     -- advance predicate does NOT fire
-- leaf window identity: `(take (b+1)).drop lo = op :: (interior ++ [cl])` at lo = 2, b = 6.
#guard ((N.toList.take 7).drop 2).map (·.val)
        == [.flowSequenceStart, .scalar "1" .doubleQuoted, .flowEntry,
            .scalar "2" .doubleQuoted, .flowSequenceEnd]

-- ════════════ Witness T := `[1,[2,3]]` — ADVANCE-THEN-HEAD (a > off+L₀) ════════════
def advVal : YamlValue := .sequence .flow #[sc "1", .sequence .flow #[sc "2", sc "3"]]
def T : Array (Positioned YamlToken) :=
  match scanFiltered (emit advVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:"1" 3:, 4:[ 5:"2" 6:, 7:"3" 8:] 9:] 10:SE   (root body off = 2)
-- target interior window [a, b) = [5, 8); enclosing entry `[2,3]` at [lo, b] = [4, 8].
#guard T.size == 11
-- head entry of the root body = scalar `"1"` = (root body).take 1, so L₀ = 1.
#guard (((T.toList.take 9).drop 2).take 1).length == 1
-- MOVE 1: a = 5, off = 2, L₀ = 1 → off+L₀ = 3 < a → ADVANCE, off' = off+L₀+1 = 4.
#guard decide ((2 + 1 < (5 : Nat)))                       -- advance predicate fires (off+L₀ < a)
#guard decide (¬ ((5 : Nat) == 2 + 1))                    -- leaf predicate does NOT fire at root
-- after advance off' = 4, body = `[ "2" , "3" ]` of length 5; MOVE 2: a = 5 == off'+1 = 5 → LEAF.
#guard (((T.toList.take 9).drop 4).take 5).length == 5
#guard decide ((5 : Nat) == 4 + 1)                        -- leaf predicate fires at off' = 4, lo = 4
-- leaf window identity at lo = 4, b = 8.
#guard ((T.toList.take 9).drop 4).map (·.val)
        == [.flowSequenceStart, .scalar "2" .doubleQuoted, .flowEntry,
            .scalar "3" .doubleQuoted, .flowSequenceEnd]

-- ════════════ Witness D := `[[[1,2]]]` — DESCEND-INTO-INTERIOR (off+1 < a < off+L) ════════════
def deepVal : YamlValue := .sequence .flow #[.sequence .flow #[.sequence .flow #[sc "1", sc "2"]]]
def D : Array (Positioned YamlToken) :=
  match scanFiltered (emit deepVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:[ 3:[ 4:"1" 5:, 6:"2" 7:] 8:] 9:] 10:SE   (root body off = 2)
-- target interior window [a, b) = [4, 7); enclosing entry `[1,2]` at [lo, b] = [3, 7].
#guard D.size == 11
-- head entry of the root body = whole body `[ [ "1" , "2" ] ]` = (root body).take 7, so L = 7.
#guard (((D.toList.take 9).drop 2).take 7).length == 7
-- MOVE 1: a = 4, off = 2, L = 7 → off+1 = 3 < a = 4 < off+L = 9 → DESCEND, off' = off+1 = 3.
#guard decide ((2 + 1 < (4 : Nat)) && ((4 : Nat) < 2 + 7))  -- descend predicate fires
#guard decide (¬ ((4 : Nat) == 2 + 1))                       -- leaf predicate does NOT fire at root
-- after descend off' = 3, body = head entry's interior `[ "1" , "2" ]` of length 5; MOVE 2: a = off'+1.
#guard (((D.toList.take 8).drop 3).take 5).length == 5
#guard decide ((4 : Nat) == 3 + 1)                           -- leaf predicate fires at off' = 3, lo = 3
-- leaf window identity at lo = 3, b = 7.
#guard ((D.toList.take 8).drop 3).map (·.val)
        == [.flowSequenceStart, .scalar "1" .doubleQuoted, .flowEntry,
            .scalar "2" .doubleQuoted, .flowSequenceEnd]

end L4YAML.Proofs.EmitterScannability.SeqNestedEntryLocateProbe
