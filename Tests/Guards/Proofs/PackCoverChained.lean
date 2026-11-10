module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The pack carries the cover, so the chain does (DOCS item 148)

Item 147 gave `pendingMapValue.h_frames` a cover and seeded it at the two root
`:`/`?` producers.  What it left was a field that is true and unspendable: every
cover on it was a root's `[k]`, and the two implicit producers —
`colon_open_map_implicit` and `colon_open_map_props` — paid `Or.inr trivial`,
because what they would inherit rides `ImplicitKeyPack`, which carried none.  A
cover that stops at the first nested key is a cover of one park.

This item makes the hop.  `ImplicitKeyPack` and `PropsKeyPack` carry the cover
beside their resume twins; the key dispatch's NESTED branch conses the landed
key's own level onto the caller's frames and hands both to the pack; and the `:`
that resolves the key pays them into the next park's two frame faces.  A cover
seeded at a root now reaches a park any number of implicit keys deep.

Two readings had to be corrected to make that work, and both are measured here.

**The bound.**  Item 147 bounded the floor by the park's own index (`lo ≤ n`).
The landing that SPENDS a cover stands below that index — that is what a dedent
is — so `preprocess_landing_mem_or_seq`'s `lo ≤ s_prep.col` is exactly what such
a bound cannot supply.  `IndentStackCover.Floor` states both halves: at or below
the level's own index, and at or below every width the frames name.  Dropping
the first half is vacuity where the frames are empty; dropping the second is
unspendability at every dedent.

**The list.**  The cover a pack carries is over `FrameLevel.map k :: ks` — the key's own level
included — not over `ks`.  The two branches that pay reach it from opposite
sides: a key NESTED below the park opens its level at the `:` still to come, so
its width is free (`Covered.cons`); a key that LANDED on an open level finds
that level already on the stack and cannot drop it.  One list serves both.

§1 is the bound.  §2 is the transport across the `:`.  §3 is the hop, composed.
§4 checks the transport's own premise against the scanner.  §5 is the price and
the one branch that still does not pay. -/

namespace L4YAML.Tests.Guards.PackCoverChained

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.IndentStackCover

/-! ## §1  The floor's bound

`Floor lo n ks` is two claims, and each answers a way the other fails. -/

/-- The bound, at its definition. -/
example (lo n : Nat) (ks : List FrameLevel) :
    Floor lo n ks ↔ (lo ≤ n ∧ ∀ fr ∈ ks, lo ≤ fr.width) := Iff.rfl

/-- **What the second half buys**: it drags the floor down to the OUTERMOST
    width the frames name.  `preprocess_landing_mem_or_seq` asks its caller for
    `lo ≤ s_prep.col` BEFORE the landing's membership is known — that is what
    the lemma derives — so the bound has to reach below the landing without
    naming it, and a bound that runs over the widths does. -/
example {lo n j : Nat} {ks : List FrameLevel} (h : Floor lo n ks) (hj : FrameLevel.map j ∈ ks) :
    lo ≤ j := h.le_of_mem hj

/-- …and in a chain rooted at column 0 that pins the floor AT 0, where the spend
    premise is free for every landing column whatever — which is the case the
    lemma's own docstring names ("at `lo = 0` the hypothesis is free"). -/
example {lo n : Nat} {ks : List FrameLevel} (h : Floor lo n ks) (h0 : FrameLevel.map 0 ∈ ks)
    (w : Nat) : lo ≤ w := Nat.le_trans (h.le_of_mem h0) (Nat.zero_le w)

/-- The second half is NOT derivable from the first: a floor at the park's own
    index clears every width at or right of it and no width below, which is
    precisely where a dedent lands. -/
example : ¬ (∀ (lo n : Nat) (ks : List FrameLevel), lo ≤ n → ∀ j, FrameLevel.map j ∈ ks → lo ≤ j) := by
  intro h
  exact absurd (h 2 2 [FrameLevel.map 1] (Nat.le_refl 2) 1 List.mem_cons_self) (by omega)

/-- **What the first half buys**: with no widths to bound it, a floor is free to
    climb, and past the stack's own top the cover weakens to nothing
    (`Covered.raise_floor`) — so the second half alone admits a vacuous witness.
    This is the same reading item 147's guard makes of an unbounded `∃ lo`. -/
example (s : ScannerState) (ks : List FrameLevel) (hs : ∀ e ∈ s.indents, e.column < 99) :
    (∀ fr ∈ ([] : List FrameLevel), 99 ≤ fr.width) ∧ Covered 99 ks s :=
  ⟨fun _ h => absurd h List.not_mem_nil,
   fun e he _ hlo => absurd (hs e he) (by omega)⟩

/-- The chain's own step on the bound: a level opened strictly deeper than an
    existing one inherits that level's floor, which is what the key dispatch's
    nested branch pays with. -/
example {lo n c : Nat} {ks : List FrameLevel} (h : Floor lo n ks) (hn : n < c) :
    Floor lo c (FrameLevel.map c :: ks) :=
  (h.mono_index (Nat.le_of_lt hn)).cons (Nat.le_of_lt (Nat.lt_of_le_of_lt h.1 hn))

/-! ## §2  The transport across the `:`

`scanValuePrepare_cover` reports the level a step opens with an existential,
which is all a step-generic caller can say.  A caller holding the live key holds
its column, and that is the difference between `FrameLevel.map c :: ks` for an unknown `c` and
the `FrameLevel.map k :: ks` the frames already name. -/

/-- The key clear leaves the prepare one of two readable states: the key at its
    own column, or no key and the `?` line that took it. -/
example {s : ScannerState} (h : s.simpleKey.possible = true) :
    ((scanValueClearKey s).simpleKey.possible = true ∧
        (scanValueClearKey s).simpleKey.pos.col = s.simpleKey.pos.col) ∨
      ((scanValueClearKey s).simpleKey.possible = false ∧
        (scanValueClearKey s).explicitKeyLine.isSome = true) :=
  scanValueClearKey_arm h

/-- The prepare, named: with a live key the push is at the KEY's column, and the
    two branches that do not push cost the cover nothing. -/
example {lo k : Nat} {ks : List FrameLevel} {s : ScannerState}
    (h_arm : s.simpleKey.possible = true ∨ s.explicitKeyLine.isSome = true)
    (h_col : s.simpleKey.possible = true → s.simpleKey.pos.col = k)
    (h : Covered lo ks s) :
    Covered lo (FrameLevel.map k :: ks) (scanValuePrepare s) :=
  scanValuePrepare_cover_key h_arm h_col h

/-- The `:`'s whole step. -/
example {lo k : Nat} {ks : List FrameLevel} {s s' : ScannerState}
    (hok : scanValue s = .ok s') (h_poss : s.simpleKey.possible = true)
    (h_col : s.simpleKey.pos.col = k) (h : Covered lo ks s) :
    Covered lo (FrameLevel.map k :: ks) s' :=
  scanValue_cover_key hok h_poss h_col h

/-- …and the shape the producers actually meet: the level the `:` opens is
    ALREADY one of the frames, because the pack's list carries it.  The step
    names it twice and `dedup_head` folds it back. -/
example {lo k : Nat} {ks : List FrameLevel} {s s' : ScannerState}
    (hok : scanValue s = .ok s') (h_poss : s.simpleKey.possible = true)
    (h_col : s.simpleKey.pos.col = k) (h : Covered lo (FrameLevel.map k :: ks) s) :
    Covered lo (FrameLevel.map k :: ks) s' :=
  (scanValue_cover_key hok h_poss h_col h).dedup_head

/-! ## §3  The hop, composed

The two steps between a park and the next park are a content dispatch (the key)
and a `:` dispatch (the value indicator), each with its own preprocessing.
Neither preprocessing pushes and the content dispatch writes no level, so the
whole of the carriage is the `:`. -/

/-- **The chain, end to end.**  A park's cover reaches the park its own key
    opens, over the widths that park's frames name. -/
example {lo k : Nat} {ks : List FrameLevel}
    {sc s_prep s_key s_prep2 s_val : ScannerState} {c : Char}
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_key : scanNextToken_dispatchContent s_prep c = .ok s_key)
    (h_pre2 : scanNextToken_preprocess s_key = .ok (some (s_prep2, ':')))
    (h_val : scanValue s_prep2 = .ok s_val)
    (h_poss : s_prep2.simpleKey.possible = true)
    (h_col : s_prep2.simpleKey.pos.col = k)
    (h : Covered lo ks sc) :
    Covered lo (FrameLevel.map k :: ks) s_val :=
  scanValue_cover_key h_val h_poss h_col
    (preprocess_cover h_pre2 (dispatchContent_cover h_key (preprocess_cover h_pre h)))

/-- The pack's field, at the type the producers pay and the consumers read. -/
-- 2026-11-10 (item 473, option (A)): the level constructors' bound and the park faces read `≤` (the root frame
-- stands under a column-0 opener's own level), `ResumeWidths` names the survivors positionally and `ResumeWidths.lt`
-- is `ResumeWidths.le`; the rows below restate the faces they mirror — a shape move, no obligation changed.
example {sc : ScannerState} {sp_start sp_scan : SurfPos}
    (h : ImplicitKeyPack sc sp_start sp_scan) :
    ∃ (k : Nat) (sp_key : SurfPos),
      ((∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width ≤ k) ∧
        ((∃ lo : Nat, Floor lo k (FrameLevel.map k :: ks) ∧ Covered lo (FrameLevel.map k :: ks) sc) ∨ True) ∧
        ∀ sp_v : SurfPos, SBlockMapEntry k sp_key sp_v →
        ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
        ResumeFrames (SLYamlStream sp_start) ks sp_e) ∨ True) := by
  obtain ⟨k, sp_key, _, _, _, _, _, _, h_resF, _⟩ := h
  exact ⟨k, sp_key, h_resF⟩

/-- `PropsKeyPack` carries the same field, so an anchored null key
    (`&p : 2`) is a hop like any other. -/
example {sc : ScannerState} {sp_start sp_p sp_scan : SurfPos}
    (h : PropsKeyPack sc sp_start sp_p sp_scan) :
    ∃ k : Nat,
      ((∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width ≤ k) ∧
        ((∃ lo : Nat, Floor lo k (FrameLevel.map k :: ks) ∧ Covered lo (FrameLevel.map k :: ks) sc) ∨ True) ∧
        ∀ sp_v : SurfPos, SBlockMapEntry k sp_p sp_v →
        ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
        ResumeFrames (SLYamlStream sp_start) ks sp_e) ∨ True) := by
  obtain ⟨⟨k, _, _, _, h_resF, _⟩, _⟩ := h
  exact ⟨k, h_resF⟩

/-! ## §4  The transport's premise, against the scanner

`scanValuePrepare_cover_key` rests on one reading of the machine: with a simple
key live, the level a `:` opens stands at the KEY's column and not at the
cursor's.  The walk below checks exactly that, at every `:` of every input, and
counts the states it saw so a future change to the prepare cannot make the check
vacuous by never reaching a push. -/

private def keyColumnPush (s : ScannerState) : Nat × Nat × Nat :=
  match scanNextToken_preprocess s with
  | .ok (some (s', ':')) =>
      match scanValue s' with
      | .ok s'' =>
          if s''.indents.size == s'.indents.size then (1, 0, 0)
          else
            let pushed := s''.indents[s''.indents.size - 1]!.column
            let want : Int :=
              if s'.simpleKey.possible then (s'.simpleKey.pos.col : Int) else (s'.col : Int)
            (1, 1, if pushed == want then 0 else 1)
      | _ => (0, 0, 0)
  | _ => (0, 0, 0)

/-- States seen; `:` steps the value scan accepted; pushes those made; and
    pushes at a column the live key does not name. -/
private def walkColons (s : ScannerState) : Nat → Nat × Nat × Nat × Nat →
    Nat × Nat × Nat × Nat
  | 0, acc => acc
  | fuel + 1, (seen, colons, pushes, bad) =>
    let (c, p, b) := keyColumnPush s
    let acc := (seen + 1, colons + c, pushes + p, bad + b)
    match scanNextToken s with
    | .ok (some s') => walkColons s' fuel acc
    | _ => acc

private def census (inputs : List String) : Nat × Nat × Nat × Nat :=
  inputs.foldl (fun acc i => walkColons (ScannerState.mk' i) 200 acc) (0, 0, 0, 0)

-- The same eighteen inputs items 146 and 147 walk, so the state count is a
-- cross-check as well: 121 states, 27 of them a step whose preprocessing hands
-- a `:` the value scan then accepts, 18 of those opening a level, and none of
-- the eighteen at a column the live key does not name.
#guard census
  ["a: 1\nb: 2\n", "k:\n  a: 1\n  b: 2\n", "- a\n- b\n", "k:\n  - a\n  - b\n",
   "? \"a\"\n: v\n", "k: [1, 2]\nb: 2\n", "k: |\n  x\nb: 2\n", "k:\n  a: 1\nb: 2\n",
   "k:\n  \"x\"\n  b: 2\n", "k:\n  \"a\"\n  [1, 2]\n", "k:\n  a\n  : v\n",
   "\"x\"\nb: 2\n", "a\n# c\nb: 2\n", "[1, 2]\nb: 2\n",
   "a:\n  b:\n    c: 1\nd: 2\n", "{a: 1, b: [2, 3]}\n", "k: >\n  folded\n",
   "---\na: 1\n...\n---\nb: 2\n"] == (121, 27, 18, 0)

-- The deepest chain in the set, read on its own — `a:⏎  b:⏎    c: 1⏎d: 2`,
-- three levels of nesting and a dedent back to the root: four `:` steps, three
-- of them opening a level, each at its key's own column.  The fourth is `d`'s,
-- which lands on the root level and opens nothing — the shape the pack's list
-- carries `k` for.
#guard walkColons (ScannerState.mk' "a:\n  b:\n    c: 1\nd: 2\n") 200 (0, 0, 0, 0)
  == (11, 4, 3, 0)

/-! ## §5  The price, and the one branch that does not pay

The field is stated at **14** places — the two packs, the park's two frame
faces, the two implicit producers' premises, the two key-dispatch lemmas'
`h_nodeF`, their two local build helpers, and the two relays' pair, twice.  The
transport is **5** `h_cov_step` helpers, one per lemma that crosses a dispatch,
and **8** new declarations in `IndentStackCover` — the `:`'s three
(`scanValueClearKey_arm`, `scanValuePrepare_cover_key`, `scanValue_cover_key`),
`Covered.dedup_head`, and `Floor` with its three.

What pays and what does not, named rather than counted:

* **The two root `:`/`?` producers** seed, as in item 147, now on both faces.
* **The NESTED branch** of both key-dispatch lemmas pays the pack: the landed
  key opens its level at the `:` still to come, so its width joins the frames
  for free and the floor stays strictly left of it (`n < w` on that branch).
* **Both implicit `:` producers** spend the pack into the next park's two
  faces.  The chain closes: a cover seeded at a root reaches a park any number
  of implicit keys deep, which is what the field was for.
* **The DEDENT branch** does not pay, and the reason is a real one rather than
  an unthreaded premise.  The level the landing popped TO is still on the
  scanner's stack, so the pack's cover there is over `FrameLevel.map w :: ks'` while the
  caller's is over the whole of `ks` — and `resumeAt` drops every width above
  `w`.  Reading the one as the other wants the stack's SHAPE (`Mono`, which the
  content lane does not carry), the landing's own floor, and `resumeAt`'s widths
  as a sublist of the ones they came from — **item 149 corrects the last**: the
  sublist is the half the FLOOR spends, and the COVER spends the opposite
  direction, completeness (see `DedentCoverSpent` §1).  None of the three is at
  that branch.
* **A fresh document's root**, a **sequence park**, and the **flow OPEN** carry
  no stack to inherit and pay `Or.inr trivial`.  The first two are honest: the
  chain is seeded at the `:`/`?` producers, which is where `Mono` rides.

So the residue is one branch and three readings, which is what the dedent spend
(`preprocess_landing_mem_or_seq` at `entryKeyPack_of_dispatch`'s dedent) needs
next, beside item 146's base residue there — **5** declarations, **10** sites. -/

end L4YAML.Tests.Guards.PackCoverChained

end Blanket
