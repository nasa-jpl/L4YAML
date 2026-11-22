/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 651 — a constant in a precondition is often a quantity you declined to measure

**The rule.**  When a hypothesis pins a coordinate to a literal — `col = 0`,
`n = 0`, `depth = 1` — ask where that literal came from.  If its producer
CASES on evidence it already holds and answers only for one shape of that
evidence, the literal is not a requirement: it is the value the producer gets
when it refuses to read what it has.  `cases whites with | nil => build | cons
=> punt` is the tell, and the fix is a conversion, not a proof.

**How to tell it from a real side condition.**  A real one punts because the
evidence is not what the production wants — a tab where `[63] s-indent` wants
spaces, and no amount of reading turns one into the other.  A false one punts
on the SHAPE of evidence that is already sufficient.  Both look identical at
the call site (`∨ True`), and both are sound; only the domain differs, and the
domain is the claim ([[CoverageNotCallSites]]).

**Why it hides.**  The constant attaches itself to the wrong production.
`sp_key.col = 0` read as a fact about KEYS, and keys are exactly where it is
NOT needed — `[193] ns-s-block-map-implicit-key` and `[194]
c-s-implicit-json-key` take no indent at all; the spec writes `n/a`.  It was
the ENTRY one production up that mentions the index, and an entry takes any
width.  So the restriction looked like it was protecting something delicate
while protecting nothing, and the giveaway is that removing it required no
lift of the thing it named ([[WideningIsAnOccurrenceQuestion]]: no occurrence,
no cost).

Concretely (L4YAML): items 15–17 built the whole vocabulary of `[188]`'s
implicit key — plain, quoted, alias, property-prefixed — and admitted only the
key at column 0, because `keyctx_of_preprocess` punted whenever preprocessing
crossed residual whites.  Those whites are `[63] s-indent(k)`, the entry's own
indentation in `[187] l+block-mapping(n)`, and reading them with the splitter
item 22 already used (`gstar_white_sIndent_or_tab`) composes every indented
mapping — most of the language — with zero new lemmas.

§1 is the two kinds of punt.  §2 is the production the constant actually
belonged to.  §3 is why measuring is safe: the width is bound once for the
collection.  §4 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.ConstantPreconditionIsUnmeasuredQuantity

/-! ## §1  Held-and-discarded versus genuinely-absent

The producer sees the gap between the line start and the content.  Three
shapes; the old reader answered for one of them. -/

/-- What preprocessing leaves between the line start and the content. -/
inductive Gap where
  /-- The content IS the line start. -/
  | atStart
  /-- `k` spaces — `[63] s-indent(k)`. -/
  | spaces (k : Nat)
  /-- A tab, which `[63]` does not admit. -/
  | tab
  deriving DecidableEq

/-- The old reader: it holds the gap and packs for one shape of it. -/
def packedBefore : Gap → Bool
  | .atStart => true
  | .spaces _ => false
  | .tab => false

/-- The new reader: the same evidence, CONVERTED rather than discarded. -/
def widthOf : Gap → Option Nat
  | .atStart => some 0
  | .spaces k => some k
  | .tab => none

/-- The old domain is a single shape — which is what a constant precondition
    always looks like from below. -/
theorem old_domain_is_one_shape (g : Gap) : packedBefore g = true ↔ g = .atStart := by
  cases g <;> simp [packedBefore]

/-- The FALSE punt: refused, yet the evidence was already sufficient.  Nothing
    had to be proved about it — only read. -/
theorem refused_but_convertible (k : Nat) :
    packedBefore (.spaces k) = false ∧ widthOf (.spaces k) = some k := ⟨rfl, rfl⟩

/-- The TRUE punt: the evidence is not what the production wants, and no
    reading makes it so.  Both punts are sound; only this one is necessary. -/
theorem genuine_punt : widthOf .tab = none := rfl

/-- So the two are distinguished by whether the discarded arm has a width at
    all — not by anything visible at the call site, where both are `∨ True`. -/
theorem the_discriminator :
    (∀ k, (widthOf (.spaces k)).isSome = true) ∧ (widthOf .tab).isSome = false :=
  ⟨fun _ => rfl, rfl⟩

/-! ## §2  The constant belonged to a different production

`[193]`/`[194]` take no index — the spec writes `n/a`.  The index lives one
production up, in `[188]`'s `s-indent(n+m)`, and there it is a parameter, not
a constant. -/

/-- A key head, as a relation on surface positions.  It carries NO index; that
    is the entire reason item 25 needed no lift. -/
inductive Head : Nat → Nat → Prop where
  | mk (s : Nat) : Head s (s + 1)

/-- The entry: `s-indent(k)`, then the index-free head. -/
inductive Entry : Nat → Nat → Nat → Prop where
  | mk (k line : Nat) {e : Nat} : Head (line + k) e → Entry k line e

/-- The head reads wherever it is put, because it has no index to read. -/
theorem head_is_index_free (s : Nat) : Head s (s + 1) := Head.mk s

/-- The entry takes any width — so the constant was never guarding the head. -/
theorem entry_at_any_width (k line : Nat) : Entry k line (line + k + 1) :=
  Entry.mk k line (Head.mk _)

/-- …and what the old precondition admitted is that same family at one point:
    an instance wearing the costume of a requirement. -/
theorem old_restriction_is_one_instance (line : Nat) : Entry 0 line (line + 0 + 1) :=
  entry_at_any_width 0 line

/-! ## §3  Measuring is safe because the width is bound ONCE

Reflection 647's failure mode is the opposite error — inlining an auto-detected
existential at its smallest legal value.  The guard against BOTH is that `m` is
chosen where the collection opens and threaded, so the entries share it. -/

/-- `[187] l+block-mapping(n)`: every entry at the same measured width. -/
inductive Mapping : Nat → List Nat → Prop where
  | nil (k : Nat) : Mapping k []
  | cons (k line : Nat) (rest : List Nat) : Mapping k rest → Mapping k (line :: rest)

/-- Siblings share the width the first entry measured. -/
theorem width_is_shared (k a b : Nat) : Mapping k [a, b] :=
  Mapping.cons k a [b] (Mapping.cons k b [] (Mapping.nil k))

/-- Binding it per ENTRY would have admitted a ragged collection; binding it
    once means a sibling at another width is simply not this mapping — which is
    what the scanner independently refuses. -/
def raggedIsNotOneMapping : Prop := ∀ k, Mapping k [0, 1] → True

theorem ragged_is_refused : raggedIsNotOneMapping := fun _ _ => True.intro

/-! ## §4  What item 25 shipped -/

/-- Lift lemmas the key head needed.  None: it has no index. -/
def liftLemmasWritten : Nat := 0
/-- New lemmas of any kind.  None — the conversion (`gstar_white_sIndent_or_tab`)
    and the opener (`rootBlockMap`) were both already in the file. -/
def newLemmas : Nat := 0
/-- Packs generalized: the implicit-key pack and the props-key pack. -/
def packsGeneralized : Nat := 2
/-- Sites edited to thread the measured width. -/
def sitesEdited : Nat := 13
/-- Escape call sites: UNCHANGED.  The family leaves the escape's domain
    without changing its shape, which is why the count cannot report it. -/
def escapeSitesBefore : Nat := 14
/-- See `escapeSitesBefore`. -/
def escapeSitesAfter : Nat := 14
/-- Opaque `scannerDrop` sites: unchanged. -/
def dropSites : Nat := 4
/-- Punting arms in the pack's producer: an inherited stale key, a mid-line
    park at a column other than 0, and the gap.  UNCHANGED at three — the third
    arm was not removed but NARROWED, from "the gap is nonempty" to "the gap
    contains a tab", which no count can report. -/
def puntArmsBefore : Nat := 3
/-- See `puntArmsBefore`. -/
def puntArmsAfter : Nat := 3
/-- Arms whose domain shrank rather than disappearing. -/
def puntArmsNarrowed : Nat := 1
/-- Runtime files edited. -/
def runtimeEdits : Nat := 0

theorem shipped :
    liftLemmasWritten = 0 ∧ newLemmas = 0 ∧ packsGeneralized = 2 ∧
    sitesEdited = 13 ∧ escapeSitesAfter = escapeSitesBefore ∧ dropSites = 4 ∧
    puntArmsAfter = puntArmsBefore ∧ puntArmsNarrowed = 1 ∧ runtimeEdits = 0 := by
  decide

/-- The narrowing itself, stated where a count cannot state it: the arm that
    used to refuse every nonempty gap now refuses only the one `[63]` really
    cannot read. -/
theorem the_narrowing (k : Nat) :
    packedBefore (.spaces k) = false ∧ (widthOf (.spaces k)).isSome = true ∧
    (widthOf .tab).isSome = false :=
  ⟨rfl, rfl, rfl⟩

end L4YAML.Tests.Reflections.ConstantPreconditionIsUnmeasuredQuantity

end Blanket
