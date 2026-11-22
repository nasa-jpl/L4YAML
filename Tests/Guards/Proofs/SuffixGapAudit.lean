/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Foundation.SurfaceSpanSupply

/-!
# One arm of one hundred and sixty-seven refutes, and the rest were gaps (DOCS item 236)

Item 235 found that `[211] l-yaml-stream` has no suffix lemma because the
statement is false, and left the number nothing held: **how many of the other
twenty-two productions without one are refutations rather than gaps?**  Its
own warning was that a census of what is missing prices it as DEBT until an
arm is opened.

The answer is **none**.  All twenty-two carry the law; fifteen of them now do
so in `L4YAML/Proofs/Foundation/SurfaceSpanSupply.lean`, and the other seven
are `abbrev`s that cite the aliased production's lemma unchanged.

The one that does not carry it costs more than a lemma.  §5 derives
`InYamlLanguage s` for EVERY string `s` from the same arm, so the top-level
surface predicate is true of everything and the acceptance-strictness theorems
that conclude it are vacuous until `scannerDrop` goes.

## What decides it, and why it is one reading rather than twenty-two

`scannerDrop` is not hard to prove — it is an arm whose PREMISES DO NOT
CONNECT the conclusion's source to its target.  `SLYamlStream s s₁` and
`SSLComments s₂ s'` leave `s₁` and `s₂` unrelated, so no chain of consumed
characters reaches `s'` from `s`, and a target that nothing connects to the
source can hold characters the source never had.  That property is decidable
from the constructor's type, so §1 reads it over all 167 arms at once instead
of opening 22 productions by hand.

The census is a filter, not a verdict.  A chain existing is not every link in
it carrying the law, and a broken chain is a CANDIDATE refutation rather than
a refutation — premises can force a connection the graph cannot see.  Both
directions were settled by compiling: the one flagged arm carries item 235's
derivation of `SLYamlStream ⟨"a", 0⟩ ⟨"bbb", 0⟩`, and the twenty-two carry
lemmas.  §4 opens each of the twenty-two with a derivation as well, which is
what keeps those lemmas from being vacuous truths about empty relations.
-/

set_option autoImplicit false

namespace Tests.Guards.SuffixGapAudit

open Lean Lean.Meta Lean.Elab
open L4YAML.Surface
open L4YAML.Proofs.SurfaceSpan
open L4YAML.CharPredicates

/-! ## §1 The arm-connectivity census

An arm is CONNECTED when the conclusion's target is reachable from the
conclusion's source through

- a premise that is itself a production between two positions, whether its
  head is a named production or a relation PARAMETER, and
- a literal step, where one position's characters are a syntactic `List.cons`
  prefix of another's.

The parameter clause is the half a first reading omits: without it the seven
arms of `GAlt`, `GOpt`, `GPlus`, `GSeq`, `GSeq3` and `GStar` read as broken,
because their premises are headed by a bound variable rather than a constant.
They are not broken — they are conditional, exactly as their lemmas are, and
`paramOnly` counts them. -/

/-- A `L4YAML.Surface` relation between two positions. -/
def isSurfRel (t : Expr) : MetaM Bool :=
  forallTelescope t fun xs body => do
    unless body.isProp || body.isSort do return false
    if xs.size < 2 then return false
    let a ← inferType xs[xs.size - 2]!
    let b ← inferType xs[xs.size - 1]!
    return a.isConstOf ``SurfPos && b.isConstOf ``SurfPos

/-- The two endpoints of a premise that is a production, with `true` when its
    head is a relation parameter rather than a named production. -/
def asEdge (t : Expr) : MetaM (Option (Expr × Expr × Bool)) := do
  let t ← whnfR t
  unless t.isApp do return none
  let args := t.getAppArgs
  if args.size < 2 then return none
  let u := args[args.size - 2]!
  let v := args[args.size - 1]!
  unless (← inferType u).isConstOf ``SurfPos && (← inferType v).isConstOf ``SurfPos do
    return none
  let fn := t.getAppFn
  match fn.constName? with
  | some h =>
      let some hci := (← getEnv).find? h | return none
      unless ← isSurfRel hci.type do return none
      return some (u, v, false)
  | none =>
      if fn.isFVar then
        unless ← isSurfRel (← inferType fn) do return none
        return some (u, v, true)
      else return none

/-- The `chars` field of an explicit `SurfPos.mk`. -/
def charsOf (e : Expr) : Option Expr :=
  if e.isAppOfArity ``SurfPos.mk 2 then some e.appFn!.appArg! else none

/-- `b` is a syntactic suffix of `a`: peel `List.cons` off `a`. -/
partial def peelsTo (a b : Expr) : Nat → Bool
  | 0 => a == b
  | fuel + 1 =>
    if a == b then true
    else if a.isAppOfArity ``List.cons 3 then peelsTo a.appArg! b fuel
    else false

-- 2026-10-23 ([162]): +2 types / +5 connected arms — `SCIndentationIndicator` and `SCChompingIndicator`.
-- 2026-10-24 ([148]/[149] JSON-key adjacent value): `types` 79 → 81, `arms` 172 → 180, `connected` 171 → 179 — the 8 new arms are suffix-connected.
-- 2026-10-26 (item 367, `[82]`): `SLDirective` 1 → 3 arms; all three connected (the `reserved` name is a `GStar (GChar isNsChar)` run, not a list variable): arms 182 → 184, connected 181 → 183.
def expectedChain : String := "types=81 arms=184 connected=183 broken=1 paramOnly=7"

/-- The one arm of the surface grammar that connects nothing to nothing. -/
def expectedBroken : List String := ["L4YAML.Surface.SLYamlStream.scannerDrop"]

run_cmd Command.liftTermElabM do
  let env ← getEnv
  let mut pop : Array Name := #[]
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    let .inductInfo ind := ci | continue
    unless (`L4YAML.Surface).isPrefixOf nm do continue
    unless (← isSurfRel ind.type) do continue
    let _ := ind
    pop := pop.push nm
  pop := pop.qsort (·.toString < ·.toString)
  let mut arms := 0
  let mut broken : Array Name := #[]
  let mut paramOnly := 0
  for p in pop do
    let some (.inductInfo ind) := env.find? p | continue
    for c in ind.ctors do
      let some ci := env.find? c | continue
      arms := arms + 1
      let (full, concrete) ← forallTelescope ci.type fun xs concl => do
        let cargs := concl.getAppArgs
        if cargs.size < 2 then return (true, true)
        let src := cargs[cargs.size - 2]!
        let tgt := cargs[cargs.size - 1]!
        let mut edges : Array (Expr × Expr × Bool) := #[]
        let mut nodes : Array Expr := #[src, tgt]
        for x in xs do
          if let some e ← asEdge (← inferType x) then
            edges := edges.push e
            nodes := nodes.push e.1
            nodes := nodes.push e.2.1
        for a in nodes do
          for b in nodes do
            if a == b then continue
            match charsOf a, charsOf b with
            | some ca, some cb => if peelsTo ca cb 64 then edges := edges.push (a, b, false)
            | _, _ => pure ()
        let reaches : Bool → Bool := fun allowParam => Id.run do
          let mut seen : Std.HashSet String := {}
          seen := seen.insert (toString src)
          let mut changed := true
          while changed do
            changed := false
            for (u, v, isParam) in edges do
              if isParam && !allowParam then continue
              if seen.contains (toString u) && !seen.contains (toString v) then
                seen := seen.insert (toString v); changed := true
          return seen.contains (toString tgt)
        return (reaches true, reaches false)
      unless full do broken := broken.push c
      if full && !concrete then paramOnly := paramOnly + 1
  let got := s!"types={pop.size} arms={arms} connected={arms - broken.size} \
broken={broken.size} paramOnly={paramOnly}"
  if got != expectedChain then
    throwError "the arm connectivity moved.\nexpected: {expectedChain}\n\
      got:      {got}\n  broken: {broken.toList.map (·.toString)}"
  let gotB := broken.toList.map (·.toString)
  if gotB != expectedBroken then
    throwError "the broken arm moved.\nexpected: {expectedBroken}\ngot:      {gotB}"

/-! ## §2 The eight the supply census still reports missing

`ColumnWalkPrice.lean` §5 reads a production as supplied when some theorem's
TYPE names both it and `List.IsSuffix`.  That test cannot see through an
`abbrev`, so seven productions read as missing while a walk cites them
without a statement of their own.  This checks the split rather than asserting
it: every name the supply census still reports is either an `abbrev` whose
value is another production, or the one production whose law is false. -/

def expectedSplit : String := "missing=8 aliases=7 refuted=1"

def refutedProduction : Name := (`L4YAML.Surface).str "SLYamlStream"

run_cmd Command.liftTermElabM do
  let env ← getEnv
  let mut prods : NameSet := {}
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    unless (`L4YAML.Surface).isPrefixOf nm do continue
    if (`noConfusionType).isSuffixOf nm || (`below).isSuffixOf nm ||
       (`rec).isSuffixOf nm || (`brecOn).isSuffixOf nm then continue
    match ci with
    | .inductInfo _ | .defnInfo _ => if ← isSurfRel ci.type then prods := prods.insert nm
    | _ => pure ()
  let mut covered : NameSet := {}
  for (_, ci) in env.constants.toList do
    match ci with | .thmInfo _ => pure () | _ => continue
    let us := ci.type.getUsedConstants
    unless us.contains ``List.IsSuffix do continue
    for u in us do if prods.contains u then covered := covered.insert u
  let missing := prods.toList.filter (!covered.contains ·)
  -- an alias: a `def`/`abbrev` whose unfolded value is headed by a production
  let mut aliases : Array Name := #[]
  for n in missing do
    let some ci := env.find? n | continue
    let some v := ci.value? (allowOpaque := true) | continue
    let head ← lambdaTelescope v fun _ b => pure b.getAppFn
    if let some h := head.constName? then
      if prods.contains h then aliases := aliases.push n
  let refuted := missing.filter (· == refutedProduction)
  let got := s!"missing={missing.length} aliases={aliases.size} refuted={refuted.length}"
  if got != expectedSplit then
    throwError "the supply split moved.\nexpected: {expectedSplit}\n\
      got:      {got}\n  missing: {missing.map (·.getString!)}\n  \
      aliases: {aliases.toList.map (·.getString!)}"
  -- and nothing else is left over
  let unexplained := missing.filter fun n => n != refutedProduction && !aliases.contains n
  unless unexplained.isEmpty do
    throwError "a missing production is neither an alias nor the refuted one: \
      {unexplained.map (·.getString!)}"

/-! ## §3 What the seven aliases cost

Nothing.  Each is the aliased production's own lemma, applied unchanged.  An
`example` is invisible to §2's census, which is why these are stated here
rather than in the library: they machine-check the claim without moving the
number that makes it. -/

example {a b : SurfPos} (h : SBAsLineFeed a b) : b.chars <:+ a.chars := sbBreak_suffix h
example {a b : SurfPos} (h : SBNonContent a b) : b.chars <:+ a.chars := sbBreak_suffix h
example {n : Nat} {a b : SurfPos} (h : SBlockLinePrefix n a b) : b.chars <:+ a.chars :=
  sIndent_suffix h
example {a b : SurfPos} (h : SCommentChar a b) : b.chars <:+ a.chars := gchar_suffix h
example {a b : SurfPos} (h : SNsChar a b) : b.chars <:+ a.chars := gchar_suffix h
example {a b : SurfPos} (h : SNbChar a b) : b.chars <:+ a.chars := gchar_suffix h
example {a b : SurfPos} (h : SENode a b) : b.chars <:+ a.chars := geps_suffix h

/-! ## §4 Every one of the twenty-two is inhabited

A suffix lemma over an empty relation is a vacuous truth, and a census cannot
tell the two apart.  Each production carries a derivation below, so each of
§3's citations and each of `SurfaceSpanSupply.lean`'s fifteen lemmas says
something about a derivation that exists. -/

lemma nb_a : isNbChar 'a' := by unfold isNbChar; decide
lemma ns_a : isNsChar 'a' := by unfold isNsChar; decide
lemma ct_a : isCommentTextChar 'a' := by unfold isCommentTextChar; decide

/-- The zero-width comment run at the start of a line. -/
lemma comments_refl (cs : List Char) : SSLComments ⟨cs, 0⟩ ⟨cs, 0⟩ :=
  SSLComments.startOfLine cs ⟨cs, 0⟩ (GStar.nil _)

/-- The zero-width comment run at end of input, at ANY column — `[77] b-comment`
    reads the end of the input as well as a break. -/
lemma comments_eof (col : Nat) : SSLComments ⟨[], col⟩ ⟨[], col⟩ :=
  SSLComments.withComment _ ⟨[], col⟩ _ (SSBComment.noSep _ _ (SBComment.eof col))
    (GStar.nil _)

example : GEps ⟨['a'], 0⟩ ⟨['a'], 0⟩ := GEps.mk _
example : GConsumeAll ⟨['a'], 0⟩ ⟨[], 1⟩ := GConsumeAll.cons 'a' [] 0 _ (GConsumeAll.nil 1)
example : GAlt GEps GEps ⟨['a'], 0⟩ ⟨['a'], 0⟩ := GAlt.left _ _ (GEps.mk _)
example : GSeq3 GEps GEps GEps ⟨['a'], 0⟩ ⟨['a'], 0⟩ :=
  GSeq3.mk _ _ _ _ (GEps.mk _) (GEps.mk _) (GEps.mk _)

example : SBAsLineFeed ⟨['\n', 'a'], 0⟩ ⟨['a'], 0⟩ := SBBreak.lf ['a'] 0
example : SBNonContent ⟨['\n', 'a'], 0⟩ ⟨['a'], 0⟩ := SBBreak.lf ['a'] 0
example : SBlockLinePrefix 0 ⟨['a'], 0⟩ ⟨['a'], 0⟩ := SIndent.zero _
example : SNbChar ⟨['a'], 0⟩ ⟨[], 1⟩ := GChar.mk 'a' [] 0 nb_a
example : SNsChar ⟨['a'], 0⟩ ⟨[], 1⟩ := GChar.mk 'a' [] 0 ns_a
example : SCommentChar ⟨['a'], 0⟩ ⟨[], 1⟩ := GChar.mk 'a' [] 0 ct_a
example : SENode ⟨['a'], 0⟩ ⟨['a'], 0⟩ := GEps.mk _

example : SLDirective ⟨['%'], 0⟩ ⟨[], 1⟩ :=
  SLDirective.reserved [] 0 ⟨[], 1⟩ ⟨[], 1⟩ ⟨[], 1⟩ (GStar.nil _) (fun _ h => by cases h)
    (by decide) (by decide) (GStar.nil _) (comments_eof 1)
example : SSNbFoldedText 0 ⟨['a'], 0⟩ ⟨[], 1⟩ :=
  SSNbFoldedText.mk 0 _ ⟨['a'], 0⟩ _ (SIndent.zero _)
    (GPlus.mk _ ⟨[], 1⟩ _ (GChar.mk 'a' [] 0 ns_a) (GStar.nil _))
example : SLNbFoldedLines 0 ⟨['a'], 0⟩ ⟨[], 1⟩ :=
  SLNbFoldedLines.mk 0 _ ⟨[], 1⟩ _
    (SSNbFoldedText.mk 0 _ ⟨['a'], 0⟩ _ (SIndent.zero _)
      (GPlus.mk _ ⟨[], 1⟩ _ (GChar.mk 'a' [] 0 ns_a) (GStar.nil _)))
    (GStar.nil _)

example : SCDirectivesEnd ⟨['-', '-', '-'], 0⟩ ⟨[], 3⟩ := SCDirectivesEnd.mk []
example : SCDocumentEnd ⟨['.', '.', '.'], 0⟩ ⟨[], 3⟩ := SCDocumentEnd.mk []
example : SLBareDocument ⟨['a'], 0⟩ ⟨['a'], 0⟩ :=
  SLBareDocument.mk _ _ (SBlockNode.emptyNode 0 .blockIn _ _ (comments_refl ['a']))
example : SLDocumentPrefix ⟨['a'], 0⟩ ⟨['a'], 0⟩ :=
  SLDocumentPrefix.comments _ _ (GStar.nil _)
example : SLDocumentSuffix ⟨['.', '.', '.'], 0⟩ ⟨[], 3⟩ :=
  SLDocumentSuffix.mk _ ⟨[], 3⟩ _ (SCDocumentEnd.mk []) (comments_eof 3)
example : SLExplicitDocument ⟨['-', '-', '-'], 0⟩ ⟨[], 3⟩ :=
  SLExplicitDocument.withContent _ ⟨[], 3⟩ _ (SCDirectivesEnd.mk [])
    (GAlt.left _ _ (SLBareDocument.mk _ _
      (SBlockNode.emptyNode 0 .blockIn ⟨[], 3⟩ ⟨[], 3⟩ (comments_eof 3))))
example : SLAnyDocument ⟨['a'], 0⟩ ⟨['a'], 0⟩ :=
  SLAnyDocument.bare _ _ (SLBareDocument.mk _ _
    (SBlockNode.emptyNode 0 .blockIn _ _ (comments_refl ['a'])))

/-- `%⏎---` — a directive, its break, and an empty explicit document. -/
example : SLDirectiveDocument ⟨['%', '\n', '-', '-', '-'], 0⟩ ⟨[], 3⟩ :=
  SLDirectiveDocument.mk _ ⟨['-', '-', '-'], 0⟩ _
    (GPlus.mk _ ⟨['-', '-', '-'], 0⟩ _
      (SLDirective.reserved ['\n', '-', '-', '-'] 0 ⟨['\n', '-', '-', '-'], 1⟩
        ⟨['\n', '-', '-', '-'], 1⟩ ⟨['-', '-', '-'], 0⟩ (GStar.nil _)
        (fun _ h => by cases h with
          | mk _ _ _ hp => exact hp.1 ((isLineBreak_iff '\n').mp rfl))
        (by decide) (by decide) (GStar.nil _)
        (SSLComments.withComment _ ⟨['-', '-', '-'], 0⟩ _
          (SSBComment.noSep _ _ (SBComment.break _ _ (SBBreak.lf _ 1))) (GStar.nil _)))
      (GStar.nil _))
    (SLExplicitDocument.withContent _ ⟨[], 3⟩ _ (SCDirectivesEnd.mk [])
      (GAlt.left _ _ (SLBareDocument.mk _ _
        (SBlockNode.emptyNode 0 .blockIn ⟨[], 3⟩ ⟨[], 3⟩ (comments_eof 3)))))

/-! ## §5 What the one broken arm costs at the top

`InYamlLanguage` is `∃ s', SLYamlStream ⟨s.toList, 0⟩ s' ∧ s'.chars = []`, and
item 235's `stream_anything` produces `SLYamlStream s ⟨chars, 0⟩` for ANY `s`
and any `chars`.  Take `chars = []` and both conjuncts are met, for every
string.

So the top-level surface predicate is not merely weaker than "parseable YAML";
it is true of everything, and `parse_strict`/`scan_strict` — acceptance implies
membership — say nothing while `scannerDrop` stands.  Row 12's β.5 is what
gives them content. -/

lemma stream_refl (s : SurfPos) : SLYamlStream s s :=
  SLYamlStream.single s s s s (GStar.nil _) (GOpt.none _) (GStar.nil _)

/-- The stream relates any position to any position opened at column 0. -/
lemma stream_anything (s : SurfPos) (chars : List Char) : SLYamlStream s ⟨chars, 0⟩ :=
  SLYamlStream.scannerDrop s s ⟨chars, 0⟩ ⟨chars, 0⟩ (stream_refl s) (comments_refl chars)

/-- **`InYamlLanguage` holds of every string.** -/
lemma inYamlLanguage_everything (s : String) : InYamlLanguage s :=
  ⟨⟨[], 0⟩, stream_anything ⟨s.toList, 0⟩ [], rfl⟩

/-- Neither printable nor well-formed, and in the language all the same. -/
example : InYamlLanguage "\x00\x00 [ } : *** ---" := inYamlLanguage_everything _

/-- `parse_strict`'s statement, discharged without its hypothesis. -/
example (input : String) (docs : Array L4YAML.YamlDocument)
    (_h : L4YAML.TokenParser.parseYaml input = .ok docs) : InYamlLanguage input :=
  inYamlLanguage_everything input

/-- `scan_strict`'s statement, discharged without its hypothesis. -/
example (input : String) (tokens : Array (L4YAML.Positioned L4YAML.YamlToken))
    (_h : L4YAML.Scanner.scan input = .ok tokens) : InYamlLanguage input :=
  inYamlLanguage_everything input

end Tests.Guards.SuffixGapAudit
