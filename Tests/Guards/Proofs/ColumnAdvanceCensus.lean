/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Surface.Surface
import L4YAML.Proofs.Foundation.SurfaceSpan

/-!
# The column law is false, and one arm refutes it (DOCS item 234)

Item 233 measured why nothing in the library refutes a `SepResidue`: the fact
that would refute one is a statement about a LINE, and neither `SurfPos` nor
`ScannerSurfCorr` carries a line.  A column is the only coordinate a surface
position has besides its characters, so the coordinate a refuter needs has to
be built out of column arithmetic, and item 233 named the law it would rest on:

> a column advances by the characters consumed, except across a break —
> `s'.col = s.col + |span s s'|` or `BreakBetween s s'`.

**That law is false.**  §1 refutes it against a derivation of a real
production, and §2 finds the single arm responsible out of 167.

## What the arm is, and why it is not a bug

`[202] l-document-prefix` consumes a byte-order mark and does NOT advance the
column, on purpose: the module docstring in `Surface/Document.lean` records
that carrying `col + 1` put the first line one column deeper than every other,
so that `﻿a: 1⏎b: 2` dedented below its own `[187] l+block-mapping` and `﻿---`
sat off column 0 where `[203] c-directives-end` cannot be read.  The BOM is a
character that occupies no column.  So the law is not repairable by fixing the
grammar; it is the law that is wrong.

## The corrected statement

    s'.col + (BOMs consumed) = s.col + |span s s'|   ∨   BreakBetween s s'

— a column advances by the characters consumed that are not byte-order marks,
except across a break.

## What survives for a refuter, and it is the half that matters

A consumer refutes `BreakBetween` from the OTHER direction:

    BreakBetween s s' → s'.col < |span s s'|

whose contrapositive — a column at least as large as the span means no break —
is the fact `[193] c-s-implicit-json-key` needs.  The BOM does not touch it: it
eats a character without a break, which only makes the span longer.  What that
induction needs at its leaves is exactly what §2 pins: **every arm that writes
column 0 eats a literal line break** (`reset=3`, all three `SBBreak`), and **no
arm advances the column over a line break** — 25 arms eat only literals and
none is a break, and the 11 that eat a variable character do so under a
predicate §3 shows admits neither `'\n'` nor `'\r'`.

The one arm that could advance over a break is `GConsumeAll.cons`, which eats
any character at all.  §4 shows nothing instantiates it.

## Reading the instrument

Two readings cost this census its first two answers, and both are recorded in
the code below.  The pretty-printer renders `'\r'` as `'\x0d'`, so a census
that compared rendered strings called `SBBreak.cr` a violation; and
`Expr.nat?` does not read a raw literal, which is what a `Char` literal
carries.  The third was structural: `forallTelescope` hands back the
CONCLUSION, and `SLDocumentPrefix.bom` relates its two positions in a PREMISE,
so a census that walked conclusions alone reported zero violations — the
well-behaved arms are precisely the ones whose evidence is in the conclusion.
-/

set_option autoImplicit false

namespace Tests.Guards.ColumnAdvanceCensus

open Lean Lean.Meta Lean.Elab
open L4YAML.Surface
open L4YAML.Proofs.SurfaceSpan
open L4YAML.CharPredicates
open L4YAML.Grammar

/-! ## §1 The refutation

The law, stated as item 233 stated it, and a derivation that falsifies it. -/

/-- The column law item 233's NEXT names. -/
def ColLaw (s s' : SurfPos) : Prop :=
  (∃ pre, Span s s' pre ∧ s'.col = s.col + pre.length) ∨ BreakBetween s s'

/-- The witness: a stream that is exactly one byte-order mark. -/
def bomIn : SurfPos := ⟨['﻿'], 0⟩

/-- Where `[202] l-document-prefix` leaves it: one character gone, same column. -/
def bomOut : SurfPos := ⟨[], 0⟩

/-- It is a derivation of a real production, not a hand-built pair. -/
lemma bom_derives : SLDocumentPrefix bomIn bomOut :=
  SLDocumentPrefix.bom [] 0 bomOut (GStar.nil _)

/-- The span between the two positions is one character. -/
lemma bom_span : Span bomIn bomOut ['﻿'] := rfl

/-- And that character is not a line break, so the break arm is unavailable. -/
lemma bom_not_break : ¬ BreakBetween bomIn bomOut := by
  rintro ⟨pre, hspan, ch, hmem, hbr⟩
  simp only [Span, bomIn, bomOut] at hspan
  have : pre = ['﻿'] := by simpa using hspan.symm
  subst this
  simp only [List.mem_singleton] at hmem
  subst hmem
  simp [isLineBreakProp, isLineFeedProp, isCarriageReturnProp] at hbr

/-- **The column law is false.** -/
lemma colLaw_refuted : ¬ ColLaw bomIn bomOut := by
  rintro (⟨pre, hspan, hcol⟩ | hbr)
  · simp only [Span, bomIn, bomOut] at hspan
    have : pre = ['﻿'] := by simpa using hspan.symm
    subst this
    simp [bomIn, bomOut] at hcol
  · exact bom_not_break hbr

/-! ## §2 The census

Every constructor arm of every `SurfPos`-relating inductive in
`L4YAML.Surface`, classified by what its column arithmetic does. -/

/-- Peel `c₁ :: … :: cₖ :: tail`: the depth, the heads, and the tail. -/
partial def consPeel (e : Expr) : Nat × Array Expr × Expr :=
  if e.isAppOfArity ``List.cons 3 then
    let (d, hs, t) := consPeel (e.getArg! 2)
    (d + 1, #[e.getArg! 1] ++ hs, t)
  else (0, #[], e)

/-- A `Char` literal's code point.  It carries a RAW natural literal, which
    `Expr.nat?` does not read — reading it wrong cost this census a run. -/
def charCode (e : Expr) : Option Nat :=
  if e.isAppOfArity ``Char.ofNat 1 then
    match (e.getArg! 0).rawNatLit? with
    | some n => some n
    | none => (e.getArg! 0).nat?
  else none

/-- A natural literal, raw or `OfNat`-wrapped.  Both occur. -/
def natOf (e : Expr) : Option Nat :=
  match e.rawNatLit? with
  | some n => some n
  | none => e.nat?

/-- A break character is LF or CR — exactly `isLineBreakProp`.  Read as a code
    point: the pretty-printer renders `'\r'` as `'\x0d'`, so a census that
    compares rendered strings misses it. -/
def isBreakChar (e : Expr) : Bool :=
  match charCode e with
  | some n => n == 10 || n == 13
  | none => false

/-- A column expression as `base + offset`; `none` when it is neither. -/
partial def colVal (e : Expr) : Option (Option FVarId × Nat) :=
  match natOf e with
  | some n => some (none, n)
  | none =>
    if e.isAppOfArity ``HAdd.hAdd 6 then
      match colVal (e.getArg! 4), natOf (e.getArg! 5) with
      | some (b, o), some n => some (b, o + n)
      | _, _ => none
    else match e with
      | .fvar id => some (some id, 0)
      | _ => none

/-- Every `SurfPos.mk` literal occurring in a term. -/
partial def positions (e : Expr) : Array (Expr × Expr) :=
  (if e.isAppOfArity ``SurfPos.mk 2 then #[(e.getArg! 0, e.getArg! 1)] else #[]) ++
  match e with
  | .app f a => positions f ++ positions a
  | .lam _ d b _ => positions d ++ positions b
  | .forallE _ d b _ => positions d ++ positions b
  | .letE _ t v b _ => positions t ++ positions v ++ positions b
  | .mdata _ b => positions b
  | .proj _ _ b => positions b
  | _ => #[]

/-- Does this inductive relate two `SurfPos`es?  `SCForbidden` does not — it
    asserts about ONE position, so it has no target column to violate. -/
def isSurfRel (t : Expr) : MetaM Bool :=
  forallTelescope t fun xs body => do
    unless body.isProp || body.isSort do return false
    if xs.size < 2 then return false
    let a ← inferType xs[xs.size - 2]!
    let b ← inferType xs[xs.size - 1]!
    return a.isConstOf ``SurfPos && b.isConstOf ``SurfPos

/-- The population and its split.  `advance` eats only non-break literals and
    adds exactly what it ate; `pred` eats a variable character (§3); `reset`
    writes column 0 and eats a literal break; `carried` holds no literal
    position at all and transports its premises' law. -/
-- 2026-10-23 ([162]): +2 types / +5 carried arms — `SCIndentationIndicator` (2) and `SCChompingIndicator` (3).
-- 2026-10-23 ([66]): `SSeparateInLine.startOfLine` carried → advance — it now names
-- column 0 at both ends (eats 0, col 0→0) instead of transporting a variable position.
-- 2026-10-24 (B3 [66] col-0 threading): the explicit JSON-key twins (`explicitJsonKeyAdjacentValue`,
-- `explicitPairJsonAdjacentValue`) add two flow arms.
-- 2026-10-26 (item 367, `[82]`): `SLDirective.yaml`/`.tag` advance by their literal names (`col + 5`, `col + 4`): arms 182 → 184, advance 25 → 27; violations unchanged.
def expectedSplit : String :=
  "types=81 arms=184 advance=27 pred=11 reset=3 carried=142 violations=1"
-- 2026-10-24 ([148]/[149] JSON-key adjacent value): `types` 79 → 81, `arms` 172 → 180, `carried` 133 → 141 —
-- `SCFlowJsonContent` (4 arms) + `SCFlowJsonNode` (2) + `jsonKeyAdjacentValue` + `pairJsonAdjacentValue`; all carry the column.

/-- What the census actually compared.  A census that reports no violations
    must say how much of the population it could see: `blind` counts arms
    holding two positions it could not relate, `skippedTypes` the productions
    that are not two-position relations. -/
-- 2026-10-24 (B3 [66] col-0 threading): the explicit JSON-key twins (`explicitJsonKeyAdjacentValue`,
-- `explicitPairJsonAdjacentValue`) add two flow arms.
-- 2026-10-26 (item 367, `[82]`): the `yaml`/`tag` arms add the literal prefixes `%YAML`/`%TAG` (`lits` 81 → 87, `pairs` 42 → 48).
def expectedCoverage : String := "lits=87 pairs=48 blind=0 skippedTypes=1"

/-- The arm, and it is the one §1 refutes the law with. -/
def expectedViolation : String :=
  "L4YAML.Surface.SLDocumentPrefix.bom eats 1 col 0→0 same base"

/-- Every column reset in the grammar, and each eats a literal line break. -/
def expectedResets : String :=
  "L4YAML.Surface.SBBreak.cr L4YAML.Surface.SBBreak.crLf L4YAML.Surface.SBBreak.lf"

run_cmd Command.liftTermElabM do
  let env ← getEnv
  let mut types := 0
  let mut arms := 0
  let mut advance := 0
  let mut predArms := 0
  let mut reset := 0
  let mut carried := 0
  let mut pairs := 0
  let mut lits := 0
  let mut blind := 0
  let mut skipped : Array String := #[]
  let mut violations : Array String := #[]
  let mut resets : Array String := #[]
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    let .inductInfo ind := ci | continue
    unless (`L4YAML.Surface).isPrefixOf nm do continue
    unless (← isSurfRel ind.type) do
      -- `.below` is recursor machinery and `SurfPos` is not a production.
      unless (`below).isSuffixOf nm || nm == ``SurfPos do
        skipped := skipped.push s!"{nm}"
      continue
    types := types + 1
    for c in ind.ctors do
      let some cci := env.find? c | throwError "{c} is gone from the environment"
      arms := arms + 1
      let (cls, msg, np, nl) ← forallTelescope cci.type fun xs body => do
        -- The conclusion is not enough: an arm can relate its two positions in
        -- a PREMISE, which is where `SLDocumentPrefix.bom` hides.
        let mut ps := positions body
        for x in xs do ps := ps ++ positions (← inferType x)
        let mut byTail : Array (String × Nat × Array Expr × Expr) := #[]
        for (cs, col) in ps do
          let (d, hs, t) := consPeel cs
          byTail := byTail.push (toString t, d, hs, col)
        let mut worst := ""
        let mut sawReset := false
        let mut ateLitBreak := false
        let mut ateVar := false
        let mut np := 0
        for i in [0:byTail.size] do
          for j in [0:byTail.size] do
            let (t1, d1, hs1, c1) := byTail[i]!
            let (t2, d2, _, c2) := byTail[j]!
            -- Equal depth is compared too, once: a zero-width arm that WROTE a
            -- column would otherwise be invisible.
            unless t1 == t2 && (d1 > d2 || (d1 == d2 && i < j)) do continue
            np := np + 1
            let eaten := d1 - d2
            for k in [0:eaten] do
              if k < hs1.size then
                if isBreakChar hs1[k]! then ateLitBreak := true
                else if (charCode hs1[k]!).isNone then ateVar := true
            match colVal c1, colVal c2 with
            | some (b1, o1), some (b2, o2) =>
              if b1 == b2 then
                if o2 == o1 + eaten then pure () else
                  worst := s!"{c} eats {eaten} col {o1}→{o2} same base"
              else if b2.isNone && o2 == 0 then
                if ateLitBreak then sawReset := true
                else worst := s!"{c} eats {eaten} writes col 0 with no break"
              else worst := s!"{c} eats {eaten} col base changes"
            | _, _ => worst := s!"{c} eats {eaten} col unreadable"
        if worst != "" then return (0, worst, np, byTail.size)
        else if sawReset then return (1, s!"{c}", np, byTail.size)
        else if ateLitBreak then
          return (0, s!"{c} ADVANCES over a literal break", np, byTail.size)
        else if byTail.size == 0 then return (2, "", np, byTail.size)
        else if ateVar then return (4, "", np, byTail.size)
        else return (3, "", np, byTail.size)
      pairs := pairs + np
      lits := lits + nl
      if nl ≥ 2 && np == 0 then blind := blind + 1
      if cls == 0 then violations := violations.push msg
      else if cls == 1 then reset := reset + 1; resets := resets.push s!"{c}"
      else if cls == 2 then carried := carried + 1
      else if cls == 4 then predArms := predArms + 1
      else advance := advance + 1
  let split := s!"types={types} arms={arms} advance={advance} pred={predArms} \
    reset={reset} carried={carried} violations={violations.size}"
  if split != expectedSplit then
    throwError "the column split moved.\nexpected: {expectedSplit}\ngot:      {split}\n\
      Every arm of the surface grammar is classified by what it does to the \
      column.  If `violations` rose, a new arm writes a column the characters \
      do not account for and DOCS item 234's corrected law no longer covers \
      the grammar.  If `reset` rose, a new arm writes column 0 and the \
      refuter's half of the law needs it re-checked."
  let cov := s!"lits={lits} pairs={pairs} blind={blind} skippedTypes={skipped.size}"
  if cov != expectedCoverage then
    throwError "the census's own coverage moved.\nexpected: {expectedCoverage}\n\
      got:      {cov}\nskipped: {skipped.qsort (· < ·)}\n\
      `blind` counts arms holding two positions this census could not relate; \
      it must stay 0 or the split above is a claim about less than it says."
  let vio := String.intercalate " | " violations.toList
  if vio != expectedViolation then
    throwError "the violating arm moved.\nexpected: {expectedViolation}\ngot:      {vio}"
  let res := String.intercalate " " (resets.qsort (· < ·)).toList
  if res != expectedResets then
    throwError "the resetting arms moved.\nexpected: {expectedResets}\ngot:      {res}"

/-! ## §3 No consumed character class admits a line break

The 11 arms that eat a variable character eat it under one of these
predicates.  Each fact below is FALSE if the predicate admits a break, and
their conjunction is what lets `BreakBetween → col < span` survive the 36
advancing arms. -/

lemma nbChar_not_lf : ¬ isNbChar '\n' := by simp [isNbChar, isLineBreakProp, isLineFeedProp]

lemma nbChar_not_cr : ¬ isNbChar '\r' := by
  simp [isNbChar, isLineBreakProp, isLineFeedProp, isCarriageReturnProp]

lemma nsChar_not_lf : ¬ isNsChar '\n' := by simp [isNsChar, isLineBreakProp, isLineFeedProp]

lemma nsChar_not_cr : ¬ isNsChar '\r' := by
  simp [isNsChar, isLineBreakProp, isLineFeedProp, isCarriageReturnProp]

lemma anchorChar_not_lf : ¬ isNsAnchorChar '\n' := by
  simp [isNsAnchorChar, isNsChar, isLineBreakProp, isLineFeedProp]

lemma anchorChar_not_cr : ¬ isNsAnchorChar '\r' := by
  simp [isNsAnchorChar, isNsChar, isLineBreakProp, isLineFeedProp, isCarriageReturnProp]

lemma commentChar_not_lf : ¬ isCommentTextChar '\n' := by
  simp [isCommentTextChar, isLineBreakProp, isLineFeedProp]

lemma commentChar_not_cr : ¬ isCommentTextChar '\r' := by
  simp [isCommentTextChar, isLineBreakProp, isLineFeedProp, isCarriageReturnProp]

lemma wordChar_not_lf : ¬ isWordCharProp '\n' := by decide
lemma wordChar_not_cr : ¬ isWordCharProp '\r' := by decide
lemma uriChar_not_lf : ¬ isUriCharProp '\n' := by decide
lemma uriChar_not_cr : ¬ isUriCharProp '\r' := by decide
lemma tagChar_not_lf : ¬ isTagCharProp '\n' := by decide
lemma tagChar_not_cr : ¬ isTagCharProp '\r' := by decide
lemma hexDigit_not_lf : ¬ isNsHexDigit '\n' := by simp [isNsHexDigit]
lemma hexDigit_not_cr : ¬ isNsHexDigit '\r' := by simp [isNsHexDigit]
lemma namedEscape_not_lf : ¬ isNamedEscapeChar '\n' := by decide
lemma namedEscape_not_cr : ¬ isNamedEscapeChar '\r' := by decide

lemma plainSafe_not_lf : ∀ c : L4YAML.YamlContext, ¬ isNsPlainSafe c '\n' := by
  intro c; cases c <;>
    simp [isNsPlainSafe, isNsChar, isLineBreakProp, isLineFeedProp, isCarriageReturnProp]

lemma plainSafe_not_cr : ∀ c : L4YAML.YamlContext, ¬ isNsPlainSafe c '\r' := by
  intro c; cases c <;>
    simp [isNsPlainSafe, isNsChar, isLineBreakProp, isLineFeedProp, isCarriageReturnProp]

/-! ## §4 The arm that could break it is uninstantiated

`GConsumeAll.cons` advances the column over ANY character, a line break
included, so it is the one arm in the grammar that would refute the refuter's
half outright.  Nothing applies it: the only constants that mention
`GConsumeAll` are its own recursor machinery. -/

/-- Applications of `GConsumeAll` outside its own generated machinery. -/
def expectedConsumeAllUsers : Nat := 0

run_cmd Command.liftTermElabM do
  let env ← getEnv
  let mut users : Array Name := #[]
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    unless (`L4YAML).isPrefixOf nm do continue
    if (``GConsumeAll).isPrefixOf nm then continue
    let mut hit := ci.type.getUsedConstants.contains ``GConsumeAll
    if let some v := ci.value? (allowOpaque := true) then
      if v.getUsedConstants.contains ``GConsumeAll then hit := true
    if hit then users := users.push nm
  if users.size != expectedConsumeAllUsers then
    throwError "`GConsumeAll` has acquired {users.size} consumers: \
      {users.qsort (·.toString < ·.toString)}.\n\
      It advances the column over any character at all, so a consumer makes \
      `BreakBetween s s' → s'.col < |span s s'|` false and DOCS item 234's \
      surviving half of the column law needs restating."

end Tests.Guards.ColumnAdvanceCensus
