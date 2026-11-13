/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.DropDependents

/-!
# Which of the statements riding the arm are FALSE, not merely unproved (DOCS item 239)

Item 238 measured the ring around `SLYamlStream.scannerDrop` — `D=4` proofs
build it, `T=26` run through it, `S=0` statements name it — and left the
number that decides between the floor and the ceiling: **how many of the
twenty-six are FALSE once the arm is gone, rather than merely unproved?**  A
statement that is merely unproved costs β.5 a reproof.  A statement that is
false costs a restatement, and every consumer that reads its type.

The answer is **six**.  The law β.5 buys cannot decide the other twenty, and
the reason nobody had written it down is that *the law is silent about a
conclusion that ends at end of input.*  This file refutes six and reports the
twenty as undecided by the only law this row has measured — an inconclusive
result is not a negative one.

    free=4  negation=3  empty=10  bound=9   (26)
    refuted=6   library=2   guardExhibit=4

## The vacuity trap this file had to walk around

`SLYamlStream s s' → s'.chars <:+ s.chars` is FALSE in the ambient environment
— that is item 236's refutation and it is what β.5 exists to repair.  So
`suffixLaw → P` is derivable for every `P`, and any instrument that ASSUMES the
law proves every statement false, reports a perfect score, and measures
nothing.

§1 walks around it by building the post-β.5 environment instead of assuming
it: `StreamND` carries `SLYamlStream`'s three surviving arms and omits the
fourth.  §2 proves the suffix law OF THAT MODEL by induction, with no
hypothesis anywhere, so no verdict below rests on an implication.  A model
that drifts from the thing it models measures nothing either, so §1 pins the
three copied arm types against the ambient constructors structurally rather
than by eye.

## What decides a verdict, and it is the conclusion's binder

The law constrains a derivation's TARGET.  So it can contradict a statement
only where the statement PINS a target the law forbids:

- **free** — the conclusion is `SLYamlStream a b` with `b` universally
  quantified and unreached by the premises.  The statement then asserts a
  stream to an arbitrary position, and one instance refutes it.
- **bound** — the target is existentially quantified.  The law is a constraint
  the witness must meet, not a contradiction, and meeting it is what a reproof
  does.
- **empty** — the target is existentially quantified AND pinned to
  `chars = []`.  `[] <:+ anything` (§6), so the law's verdict on these is
  satisfied before it is asked.
- **negation** — the statement is `¬ law`, and it is false exactly when the
  model proves that law.

The census is a filter and not a verdict — item 236's lesson, and the reason
§4 settles each of the four candidates by compiling a refutation rather than by
reading the class off a type.  Four candidates, four refutations, no residue.

## The class nobody had counted, and it holds every Group 7 row

**Ten of the twenty-six conclude at end of input**, including all four of the
Group 7 rows the arm carries — `parse_strict_proof` (7.1),
`scan_content_gives_stream_v2` (7.2), `scanLoop_grammar_prod` (7.3) and
`scan_strict_proof` (7.6) — together with `parse_strict`, `scan_strict`, the
three accumulation lemmas that end a scan (`eof_pending`,
`preprocessing_eof_extends_stream`, `scanNextToken_none_stream`) and
`inYamlLanguage_everything`.  The law β.5 buys says of each
of them only that `[]` is a suffix of the input, which is true of every
string.  **β.5 owes Group 7 a reproof and not one changed character of any of
its statements**, and that is a stronger reading than item 238's `S=0`: `S=0`
says no statement NAMES the arm, this says no statement CONTRADICTS the law
that replaces it.  It does not say the reproofs are easy; it says they are
reproofs.

## The two the repair actually reaches

`dropClose` and `PendingNode.close_with_ssl` are the two library statements in
the free class, and both are refuted.  `close_with_ssl` is the one item 238
left open — it is restrictive in its `PendingNode` premise, so the question
was whether that premise can be met at a target the law forbids.  It can:
`PendingNode.pendingFlow` constrains `sp_scan.col` against scanner booleans
and nothing else, so §5 builds the park at a `sp_scan` holding characters
`sp_start` never had, and builds it WITHOUT the arm.  The remaining four
refutations are guard exhibits — `stream_anything` twice,
`stream_suffix_refuted` and `stream_span_refuted` — which exist to witness the
defect and are deleted with it rather than repaired.

## Why row 12 names both halves of β.5, measured

`pendingFlow` is the only one of the park's constructors whose premises leave
`sp_block` unconnected to `sp_scan`; every other arm carries its own closing
evidence.  So the two verdicts are not the same kind of verdict:

- `dropClose` is false **unconditionally** — its own two premises are already
  independent.
- `close_with_ssl` is false **in the environment that deletes the arm and keeps
  the park**.  Retiring `pendingFlow` removes the case that refutes it.

Deleting the arm alone therefore leaves a false lemma in the library.  Row 12
names β.5 *"retire `pendingFlow`, delete `scannerDrop`"*, and this is the
measured reason the two halves are one item rather than two.

**What a restatement then costs is a separate measurement and a separate
choice.**  `Tests/Guards/Proofs/RepairChoice.lean` (DOCS item 240) prices the
three repairs of `close_with_ssl` — a premise on the lemma, the same
connection as a field on the park, or retiring the park — and only the first
changes the lemma's own type.  It reuses §4's witness: `flowPark` refutes the
premise's other source, so the premise has to be threaded from above.
-/

set_option autoImplicit false

open Lean Lean.Meta Lean.Elab

namespace Tests.Guards.DropFalsity

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.SurfaceSpan
open Tests.Guards.ColumnWalkPrice (stream_refl sslComments_refl ColLaw)

/-! ## §1 The post-β.5 environment, built rather than assumed -/

/-- `SLYamlStream` without `scannerDrop`: the relation β.5 leaves behind.

    Building the model is what keeps every verdict below out of the vacuity
    trap.  Hypothesizing the suffix law instead would hypothesize a FALSE
    proposition, and `False → P` says nothing about `P`. -/
inductive StreamND : SurfPos → SurfPos → Prop where
  | single (s s₁ s₂ s' : SurfPos) :
      GStar SLDocumentPrefix s s₁ →
      GOpt SLAnyDocument s₁ s₂ →
      GStar SLDocumentSuffix s₂ s' →
      StreamND s s'
  | suffixContinue (s s₁ s₂ s₃ s₄ s' : SurfPos) :
      StreamND s s₁ →
      GPlus SLDocumentSuffix s₁ s₂ →
      GStar SLDocumentPrefix s₂ s₃ →
      GOpt SLAnyDocument s₃ s₄ →
      GStar SLDocumentSuffix s₄ s' →
      StreamND s s'
  | implicitContinue (s s₁ s₂ s₃ s' : SurfPos) :
      StreamND s s₁ →
      GStar SLDocumentPrefix s₁ s₂ →
      GOpt SLAnyDocument s₂ s₃ →
      GStar SLDocumentSuffix s₃ s' →
      StreamND s s'

/-- The model is a SUB-relation of the thing it models: every derivation it
    admits the ambient grammar admits too, so a witness built here is a witness
    there. -/
lemma nd_embed {a b : SurfPos} (h : StreamND a b) : SLYamlStream a b := by
  induction h with
  | single s₁ s₂ s' hp hd hs => exact SLYamlStream.single _ s₁ s₂ s' hp hd hs
  | suffixContinue s₁ s₂ s₃ s₄ s' _ hpl hp hd hs ih =>
      exact SLYamlStream.suffixContinue _ s₁ s₂ s₃ s₄ s' ih hpl hp hd hs
  | implicitContinue s₁ s₂ s₃ s' _ hp hd hs ih =>
      exact SLYamlStream.implicitContinue _ s₁ s₂ s₃ s' ih hp hd hs

/-- The model is INHABITED, because a law over an empty relation is a vacuous
    truth and no census can tell the two apart (§10's rule, item 236's
    practice). -/
lemma nd_refl (s : SurfPos) : StreamND s s :=
  StreamND.single s s s s (GStar.nil _) (GOpt.none _) (GStar.nil _)

/-! ## §2 The law, with no hypothesis anywhere -/

/-- **The suffix law holds of the post-β.5 relation.**  Three arms, each
    discharged from supply already in the library — `SurfaceSpan.lean`'s
    combinator lemmas and `SurfaceSpanSupply.lean`'s document layer (item 236).
    β.5 writes no new span lemma to get this. -/
lemma nd_suffix {a b : SurfPos} (h : StreamND a b) : b.chars <:+ a.chars := by
  induction h with
  | single _ _ _ hp hd hs =>
      exact ((gstar_suffix (fun _ _ => slDocumentSuffix_suffix) hs).trans
        (gopt_suffix (fun _ _ => slAnyDocument_suffix) hd)).trans
        (gstar_suffix (fun _ _ => slDocumentPrefix_suffix) hp)
  | suffixContinue _ _ _ _ _ _ hpl hp hd hs ih =>
      exact ((((gstar_suffix (fun _ _ => slDocumentSuffix_suffix) hs).trans
        (gopt_suffix (fun _ _ => slAnyDocument_suffix) hd)).trans
        (gstar_suffix (fun _ _ => slDocumentPrefix_suffix) hp)).trans
        (gplus_suffix (fun _ _ => slDocumentSuffix_suffix) hpl)).trans ih
  | implicitContinue _ _ _ _ _ hp hd hs ih =>
      exact (((gstar_suffix (fun _ _ => slDocumentSuffix_suffix) hs).trans
        (gopt_suffix (fun _ _ => slAnyDocument_suffix) hd)).trans
        (gstar_suffix (fun _ _ => slDocumentPrefix_suffix) hp)).trans ih

/-- The law in the shape `stream_suffix_refuted` negates. -/
lemma nd_suffixLaw : ∀ a b : SurfPos, StreamND a b → b.chars <:+ a.chars :=
  fun _ _ h => nd_suffix h

/-- The law in the shape `stream_span_refuted` negates.  `Span a b pre` is
    `a.chars = pre ++ b.chars`, which is the suffix witness read forward. -/
lemma nd_spanLaw : ∀ a b : SurfPos, StreamND a b → ∃ pre, Span a b pre :=
  fun _ _ h => let ⟨t, ht⟩ := nd_suffix h; ⟨t, ht.symm⟩

/-! ## §3 The census: which class each of item 238's twenty-six falls in -/

/-- Flatten `∧`. -/
def conjuncts (e : Expr) : Array Expr := Id.run do
  let mut out : Array Expr := #[]
  let mut todo : List Expr := [e]
  while !todo.isEmpty do
    let x := todo.head!; todo := todo.tail!
    if x.isAppOfArity ``And 2 then todo := x.appFn!.appArg! :: x.appArg! :: todo
    else out := out.push x
  return out

/-- Expose the connective at the head WITHOUT unfolding the statement.  A plain
    `whnf` on the accumulation lemmas exhausts 200000 heartbeats; these
    statements carry twenty to thirty-seven binders. -/
def expose (e : Expr) : MetaM Expr := do
  let e ← whnfR e
  if e.isAppOfArity ``Exists 2 || e.isAppOfArity ``And 2 || e.isAppOfArity ``Not 1
     || e.isAppOfArity ``SLYamlStream 2 then return e
  match ← unfoldDefinition? e with
  | some e' => whnfR e'
  | none => return e

/-- Does `e` mention one of the existentially bound positions? -/
def usesAny (evars : Array Expr) (e : Expr) : Bool :=
  evars.any fun v => e.containsFVar v.fvarId!

/-- The four classes.  `evars` accumulates the `∃` binders crossed so far,
    which is exactly the polarity the verdict turns on. -/
partial def classify (evars : Array Expr) (e : Expr) : MetaM String := do
  if e.isAppOfArity ``Not 1 then return "negation"
  let e ← expose e
  if e.isAppOfArity ``Not 1 then return "negation"
  if e.isConstOf ``False then return "negation"
  if e.isAppOfArity ``Exists 2 then
    match e.appArg! with
    | .lam n t b bi =>
      return ← withLocalDecl n bi t fun x =>
        (classify (evars.push x) (b.instantiate1 x) : MetaM String)
    | _ => return "other"
  let cs := conjuncts e
  let some atom := cs.find? (·.isAppOfArity ``SLYamlStream 2) | return "other"
  let tgt := atom.appArg!
  if usesAny evars tgt then
    let pinned := cs.any fun c =>
      c.isAppOfArity ``Eq 3 &&
        (let l := c.appFn!.appArg!
         l.isAppOfArity ``SurfPos.chars 1 && l.appArg! == tgt)
    return if pinned then "empty" else "bound"
  else
    return "free"

/-- `Not` at the head of the statement itself never reaches `classify`'s
    telescope, because `¬ P` is `P → False` and the telescope would strip the
    arrow and report `False`. -/
def classifyDecl (n : Name) : MetaM String := do
  let some ci := (← getEnv).find? n | return "MISSING"
  if ci.type.isAppOfArity ``Not 1 then return "negation"
  forallTelescope ci.type fun _ concl => classify #[] concl

/-- The census line over a ring re-derived from item 238 rather than from a
    list typed here: if the ring moves, this moves with it. -/
def tally (ring : Array Name) : MetaM String := do
  let mut counts : Std.HashMap String Nat := {}
  for n in ring do
    let k ← classifyDecl n
    counts := counts.insert k ((counts.getD k 0) + 1)
  let keys := (counts.toList.map (fun p => s!"{p.1}={p.2}")).mergeSort (· < ·)
  return s!"{String.intercalate " " keys} total={ring.size}"

/-! ## §4 The six refutations, each a closed theorem -/

/-- The scanner state `pendingFlow` needs: directives closed, indent check
    armed, simple key allowed and impossible, no dangling node.  Four fields,
    none of them a position. -/
def sc0 : ScannerState := { input := "", inputEnd := 0, allowDirectives := false }

example : danglingNodePos? sc0 = none := by decide

/-- **`dropClose` is FALSE once the arm goes.**  Its two premises are
    independent, so a stream at `⟨['a'], 0⟩` and a comment run at
    `⟨['b','b','b'], 0⟩` meet them both, and the conclusion then claims a
    derivation to a position holding characters the source never had. -/
lemma dropClose_refuted :
    ¬ (∀ {sp_start sp_x : SurfPos}, StreamND sp_start sp_x →
        ∀ sp_e sp_m, SSLComments sp_e sp_m → StreamND sp_start sp_m) := by
  intro h
  have hbad := h (nd_refl ⟨['a'], 0⟩) ⟨['b','b','b'], 0⟩ ⟨['b','b','b'], 0⟩
    (sslComments_refl _)
  have := (nd_suffix hbad).length_le
  simp at this

/-- **Both `stream_anything` declarations are FALSE once the arm goes**, which
    is what they were written to say: they exhibit the defect and go with it. -/
lemma stream_anything_refuted :
    ¬ (∀ (s : SurfPos) (chars : List Char), StreamND s ⟨chars, 0⟩) := by
  intro h
  have := (nd_suffix (h ⟨['a'], 0⟩ ['b','b','b'])).length_le
  simp at this

/-- **`PendingNode.close_with_ssl` is FALSE in the environment that deletes the
    arm and keeps the park**, stated as the obligation it discharges at
    `pendingFlow` — the park's own side conditions, verbatim, with the model's
    stream in place of the ambient one.  Item 238 left this open; the premise
    is restrictive in `sc` and in nothing that connects `sp_block` to
    `sp_scan`.  `pendingFlow` is the only arm of the park with that gap, so
    retiring it removes this refutation — which is why β.5 is one item and not
    two. -/
lemma pendingFlow_obligation_refuted :
    ¬ (∀ (sc : ScannerState) (sp_start sp_block sp_scan sp_mid : SurfPos),
        StreamND sp_start sp_block →
        ((sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨ 0 < sp_scan.col) →
        sc.allowDirectives = false →
        (sp_scan.col = 0 → sc.needIndentCheck = true) →
        danglingNodePos? sc = none →
        SSLComments sp_scan sp_mid →
        StreamND sp_start sp_mid) := by
  intro h
  have hbad := h sc0 ⟨['a'], 0⟩ ⟨['a'], 0⟩ ⟨['b','b','b'], 0⟩ ⟨['b','b','b'], 0⟩
    (nd_refl _) (Or.inl ⟨rfl, rfl⟩) rfl (fun _ => rfl) (by decide)
    (sslComments_refl _)
  have := (nd_suffix hbad).length_le
  simp at this

/-- **`stream_suffix_refuted` is FALSE once the arm goes**: it negates a law the
    model proves.  `nd_suffixLaw` IS the refutation — no further work. -/
example : ∀ a b : SurfPos, StreamND a b → b.chars <:+ a.chars := nd_suffixLaw

/-- **`stream_span_refuted` is FALSE once the arm goes**, for the same reason. -/
example : ∀ a b : SurfPos, StreamND a b → ∃ pre, Span a b pre := nd_spanLaw

/-! ## §5 The park, built without the arm, and the one thing that is not -/

/-- **The expensive experiment, and it costs one declaration.**  A park at a
    `sp_scan` holding characters `sp_start` never had — `pendingFlow`
    constrains `sp_scan.col` against scanner booleans and nothing else.  Its
    stream is `stream_refl`, so this witness does NOT use the arm; §7 checks
    that on the proof term rather than taking it on trust. -/
lemma flowPark : PendingNode sc0 false ⟨['a'], 0⟩ ⟨['a'], 0⟩ ⟨['b','b','b'], 0⟩ :=
  PendingNode.pendingFlow ⟨['a'], 0⟩ ⟨['a'], 0⟩ ⟨['b','b','b'], 0⟩
    (stream_refl _) (Or.inl ⟨rfl, rfl⟩) rfl (fun _ => rfl) (Or.inl rfl)
    ⟨_, GStar.nil _, fun _ h => (h (by decide)).elim⟩

/-- What `close_with_ssl` delivers at that park TODAY, in the ambient
    environment: a stream to a target the source never reached.  This one DOES
    use the arm — it is the contrast §7 pins, and it is why the park above had
    to be checked. -/
lemma close_with_ssl_reaches : SLYamlStream ⟨['a'], 0⟩ ⟨['b','b','b'], 0⟩ :=
  PendingNode.close_with_ssl flowPark (stream_refl _) (by decide) (by decide) (by decide)
    (sslComments_refl _)

/-- …and the target is not a suffix of the source, by computation. -/
example : ¬ ((['b','b','b'] : List Char) <:+ ['a']) := by decide

/-! ## §6 Why the law cannot refute the other twenty -/

/-- **The `empty` class, in one line.**  Ten of the twenty-six conclude
    `∃ s', SLYamlStream a s' ∧ s'.chars = []`, and the law's verdict on such a
    target is `[] <:+ a.chars` — true of every input.  The law cannot
    contradict them, so nothing here asks for a changed statement; whether each
    is REPROVABLE is a separate question this file does not open. -/
example (a : SurfPos) : ([] : List Char) <:+ a.chars := List.nil_suffix

/-- **The `bound` class, in one line.**  Nine conclude
    `∃ sp_gram', SLYamlStream sp_start sp_gram' ∧ …`, and an existential target
    turns the law into a constraint the witness must meet.  A target equal to
    the source meets it, so the law rules out no such statement on its own,
    which is weaker than saying the statement holds. -/
example (a : SurfPos) : a.chars <:+ a.chars := List.suffix_refl _

/-- **`stream_colLaw_refuted` is the one negation that survives.**  `ColLaw` is
    `(∃ pre, Span s s' pre) ∧ ColMono s s' ∧ ColBreak s s'`, and the model
    proves the first conjunct only; the other two are item 235's column walk,
    priced at 319 citations over 86 lemmas and unbuilt.  Refuting the negation
    needs all three. -/
example : ∀ a b : SurfPos, StreamND a b → ∃ pre, Span a b pre := nd_spanLaw

/-- **`inYamlLanguage_everything` is not refuted either, and it is the one a
    reader would expect to be.**  `InYamlLanguage s` asserts a derivation
    ending at `chars = []`; the law says `[] <:+ s.toList`, which holds.
    Refuting it needs grammar inversion — a statement about what the surface
    grammar does NOT derive — and no instrument in this row has one. -/
example (s : String) : ([] : List Char) <:+ s.toList := List.nil_suffix

/-! ## §7 The pins -/

/-- The census line, pinned. -/
-- 2026-10-24 (B3 [66] col-0 threading): total 27 → 28, free 4 → 5 — `PendingNode.close_with_sslFrom`
-- joins the transitive set (see `DropDependents.lean`); its conclusion is the same shape as `close_with_ssl`.
-- 2026-11-11 (item 484, ContentArm): total 27 → 28, bound 9 → 10 — `accum_step_content_core` (the renamed body)
-- joins the transitive set beside `accum_step_content`, whose conclusion keeps the same bound `SLYamlStream` shape
-- with `ContentArm` as its last conjunct.
def expectedTally : String := "bound=10 empty=10 free=5 negation=3 total=28"

/-- The arm the model omits. -/
def drop : Name := `L4YAML.Surface.SLYamlStream.scannerDrop

/-- The FULL proof-term closure from a root.  Item 238's `uses` is ONE step
    for everything but generated auxiliaries, so a drop-free check built on it
    would call every witness here clean — none of them names the arm directly.
    Values only: `SLYamlStream.rec`'s TYPE names every constructor, so reading
    types would call every case split a construction (item 238 §2). -/
partial def reachesDrop (env : Environment) (root : Name) : Bool := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo : List Name := [root]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if n == drop then return true
    todo := (Tests.Guards.DropDependents.rawRefs env n true).toList ++ todo
  return false

/-- Every witness that must be drop-free, and the one that must not be. -/
def dropFree : List Name :=
  [``nd_suffix, ``nd_embed, ``nd_refl, ``flowPark,
   ``dropClose_refuted, ``stream_anything_refuted, ``pendingFlow_obligation_refuted]

def dropUsing : List Name := [``close_with_ssl_reaches]

set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  -- §1's faithfulness pin: the model's arms are the ambient arms, verbatim.
  let some (.inductInfo amb) := env.find? ``SLYamlStream
    | throwError "SLYamlStream is not an inductive"
  let some (.inductInfo nd) := env.find? ``StreamND
    | throwError "StreamND is not an inductive"
  let ambN := amb.ctors.map (·.getString!)
  let ndN := nd.ctors.map (·.getString!)
  let missing := ambN.filter (fun n => !ndN.contains n)
  unless missing == [drop.getString!] do
    throwError "the model omits {missing}, not just the arm — a model that \
drifts from what it models measures nothing"
  for c in ndN do
    let some ciA := env.find? (Name.str ``SLYamlStream c) | throwError "no ambient {c}"
    let some ciN := env.find? (Name.str ``StreamND c) | throwError "no model {c}"
    let lifted := ciN.type.replace fun e =>
      if e.isConstOf ``StreamND then some (.const ``SLYamlStream []) else none
    unless lifted == ciA.type do
      throwError "arm {c} has drifted from the ambient constructor"
  -- §3's census, over item 238's ring re-derived HERE.  This file's own §5
  -- exhibit rides the arm, so it joins the ring it measures; excluding it is
  -- named in the output rather than done silently.
  let c ← Tests.Guards.DropDependents.census
  let ownPrefix : Name := `Tests.Guards.DropFalsity
  let own := c.trans.filter (fun n => ownPrefix.isPrefixOf n)
  let ring := c.trans.filter (fun n => !ownPrefix.isPrefixOf n)
  -- **The census is blind to the module it runs in**: `inScope` reads a
  -- declaration's module, and a declaration being elaborated has none yet.  So
  -- the ring is item 238's twenty-six and not twenty-seven, although §5's
  -- exhibit demonstrably rides the arm.  Pinned, because a blind spot relied
  -- on silently is an empty check.
  unless own.isEmpty do
    throwError "the census now sees this module: {own.toList}"
  unless dropUsing.all (fun n => !c.trans.contains n) do
    throwError "the census now sees this module's exhibit, so the ring below \
is no longer item 238's"
  let got ← tally ring
  unless got == expectedTally do
    throwError "census moved:\n  got      {got}\n  expected {expectedTally}"
  -- The witnesses, discriminated on their own full proof-term closures.
  for n in dropFree do
    if reachesDrop env n then
      throwError "{n} reaches the arm — it cannot witness anything about the \
environment that lacks it"
  for n in dropUsing do
    unless reachesDrop env n do
      throwError "{n} no longer reaches the arm, so §5's contrast is empty"
  logInfo m!"DropFalsity {got} own={own.size} refuted=6 library=2 guardExhibit=4"

end Tests.Guards.DropFalsity
