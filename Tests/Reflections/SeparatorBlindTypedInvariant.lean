/-!
# Reflection 345 — a bracket-typed invariant is SEPARATOR-BLIND, so a separator-placement fact is provably not a projection of it; refute the de-front-by-reconstruction at the SUBSTRATE level

Self-contained (core Lean, no `L4YAML` import) toy model of the PROBE behind the dispatch de-front's
residual field (`(i'-b-B2c-bodySucc-first-entry)`), the move R344's audit handed forward.

R344 localized the entire `recseqentry_window_dispatch` de-front knot to a single field,
`FlowBodyContent.bodySucc`, instantiated at the FIRST entry's END (the dispatch needs only "after the
first entry comes a comma or the window-end").  The de-front works ONLY if that fact is reconstructible
*carrier-free* — i.e. derivable from the guards the recursion already carries (`FlowBodyWindow`, whose
`wellTyped` field is the typed-bracket invariant `WellTyped`, and `FlowBodyContentDeep`), with NO
emission/`SafeBodyUnit` input.

The PROBE (this reflection) REFUTES that at the substrate level.  The decisive observation is mechanical:
**the typed-bracket invariant `WellTyped` is SEPARATOR-BLIND.**  Its per-token step `btStep` matches the
separator token (`.flowEntry`) under the `_ => some s` *identity* catch-all — the SAME branch a plain
content scalar takes — so the fold is utterly insensitive to whether, or where, separators appear.  A
single MINIMAL PAIR settles it: two adjacent content units with NO separator between them, versus the
same two with a separator, have the SAME `WellTyped` value, yet differ on "is the first entry followed
by a separator-or-end."  Hence NO function `WellTyped l → bodySucc-at-first-entry l` can exist: a lemma
whose hypothesis is satisfied by both members of a pair on which the conclusion disagrees is impossible.

`FlowBodyContentDeep` adds nothing here — its fields constrain tokens AFTER openers / AFTER separators,
never the token after a *balanced entry* — so for a separator-free window (no openers, no separators) it
holds VACUOUSLY while `bodySucc` fails.  So the full carried-guard set
(`FlowBodyWindow ∧ FlowBodyContentDeep`) is satisfied by the unseparated minimal-pair member, and the
de-front-by-reconstruction is refuted: `bodySucc` genuinely needs the window's EMISSION structure
(`SafeBodyUnit`), exactly R296's obstruction sharpened — not just "no balance-free form" but "no
typed-bracket-free form," via the explicit separator-blindness of `btStep`.

The toy below abstracts the four token kinds, the separator-blind typed fold, and the
first-entry-successor property.

POSITIVE (`wt_blind`, `firstSucc_sep`): the two minimal-pair lists have EQUAL `WT` (both well-typed) —
the invariant cannot tell them apart — while the SEPARATED one satisfies the successor property.

NEGATIVE (`no_reconstruction`, `firstSucc_nosep`): the UNSEPARATED list is `WT` yet FAILS the successor
property, so there is no `∀ l, WT l → firstSucc l = true`.  That non-existence IS the substrate-level
refutation: the residual `bodySucc` cannot be reconstructed from the carried typed invariant; it must be
supplied from emission.
-/

namespace Tests.Reflections.SeparatorBlindTypedInvariant

set_option autoImplicit false

/-! ## The four token kinds and the separator-blind typed-bracket fold (toy `btStep`/`btFold`) -/

/-- Toy token kinds: a content scalar, a separator (comma, `.flowEntry`), and a bracket pair. -/
inductive Tok | content | sep | opn | cls
  deriving DecidableEq

/-- One step of the typed bracket stack (toy `btStep`).  The load-bearing line is the catch-all:
    BOTH `.content` AND `.sep` fall through to `_ => some s` — the step is **separator-blind**, it never
    reads the separator token differently from ordinary content. -/
def step (t : Tok) (s : List Bool) : Option (List Bool) :=
  match t with
  | .opn => some (true :: s)
  | .cls => match s with | true :: s' => some s' | _ => none
  | _    => some s            -- `.content` and `.sep` BOTH hit this — the separator-blindness

/-- Fold the typed stack across a token list (toy `btFold`). -/
def fold (s0 : Option (List Bool)) (l : List Tok) : Option (List Bool) :=
  l.foldl (fun acc t => acc.bind (step t)) s0

/-- A token list whose brackets are correctly typed and balanced (toy `WellTyped`). -/
def WT (l : List Tok) : Prop := fold (some []) l = some []

/-! ## The first-entry-successor property (toy `bodySucc`-at-first-entry-end)

For a body whose first entry is a single content scalar (at index `0`, a balanced depth-`0` prefix),
the property asserts: the token immediately after it is the window-end OR a separator.  This is exactly
the dispatch's lone residual use of `bodySucc`. -/

/-- `firstSucc l = true` iff the first entry (the head content token) is immediately followed by the
    list-end or a `.sep`.  The toy of `bodySucc` at `k = 0`. -/
def firstSucc (l : List Tok) : Bool :=
  match l with
  | _head :: rest =>
    match rest with
    | []     => true                  -- first entry then end-of-window
    | t :: _ => decide (t = Tok.sep)  -- first entry then a separator
  | [] => true

/-! ## The MINIMAL PAIR — equal under the separator-blind invariant, unequal under the successor fact -/

/-- The two minimal-pair members: two adjacent content units, WITHOUT and WITH a separator. -/
def noSep  : List Tok := [Tok.content, Tok.content]
def withSep : List Tok := [Tok.content, Tok.sep, Tok.content]

/-! ## POSITIVE — the invariant is blind to the separator; the separated member has the successor fact -/

/-- Both members are `WT`: the separator-blind fold returns `some []` either way.  The invariant
    CANNOT distinguish "comma present" from "comma absent." -/
theorem wt_blind : WT noSep ∧ WT withSep := ⟨rfl, rfl⟩

/-- The SEPARATED member satisfies the successor property — emission placed a comma after the entry. -/
theorem firstSucc_sep : firstSucc withSep = true := rfl

/-! ## NEGATIVE — the unseparated member is `WT` but FAILS the successor fact: no reconstruction exists -/

/-- The UNSEPARATED member FAILS the successor property: after the first content scalar comes another
    content scalar, neither end nor separator.  Yet it is `WT` (`wt_blind.1`) — so `WT` does not imply
    the successor fact. -/
theorem firstSucc_nosep : firstSucc noSep = false := rfl

/-- **The substrate-level refutation of de-front-by-reconstruction.**  There is no function
    `WT l → firstSucc l = true`: the separator-blind invariant `WT` holds on `noSep`, yet `firstSucc`
    fails there.  Since the recursion's carried guards include `WT` (and `FlowBodyContentDeep`, which is
    VACUOUS on a separator-free window), the dispatch's residual `bodySucc` cannot be reconstructed from
    them — it is genuine emission information. -/
theorem no_reconstruction : ¬ ∀ l, WT l → firstSucc l = true := by
  intro h
  have hcontra := h noSep wt_blind.1
  rw [firstSucc_nosep] at hcontra
  exact Bool.noConfusion hcontra

/-- The same refutation packaged as the minimal pair: two `WT` lists on which `firstSucc` disagrees —
    so no monotone reconstruction from `WT` can exist. -/
theorem minimal_pair :
    ∃ l1 l2, WT l1 ∧ WT l2 ∧ firstSucc l1 ≠ firstSucc l2 :=
  ⟨noSep, withSep, wt_blind.1, wt_blind.2, by decide⟩

#guard fold (some []) noSep = some []                 -- WT noSep: separator-blind fold accepts it
#guard fold (some []) withSep = some []               -- WT withSep: SAME value — blindness
#guard firstSucc noSep = false                        -- NEGATIVE: bodySucc fails on the unseparated body
#guard firstSucc withSep = true                       -- POSITIVE: bodySucc holds once emission adds a comma

end Tests.Reflections.SeparatorBlindTypedInvariant
