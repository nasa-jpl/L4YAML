import L4YAML.Proofs.Production.StreamAccum

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The census over INDICES (DOCS item 203)

Item 202 left one row — `flowKeyRoute_of_open`'s value-line resume, the only
conclusion conjunct in `StreamAccum` that no arm pays and no relay hides — and
priced its payment as *carrying item 196's CHAIN into the resume twins*, with
one instruction attached:

> Measure whether the CONSUMERS can spend a list before widening the producers;
> that is the direction item 189–192 went and it cost four items.

This is that measurement.  A widening pays only where something READS the wider
shape, so the question is not how many declarations state the field — it is
whether anything tests the index the field names.  For every `∃ x : Nat` and
`∃ x : List Nat` binder in the module's surface whose body states a
`ResumeFrames`, this census counts how many times that binder occurs in its own
body.  **An index that occurs ONCE is write-only**: nothing else in the field
mentions it, so nothing downstream can be testing it, and a list in its place
would name members no consumer could ask about.

## What it reads

The three resume lanes are separated by the bottom their frames stand on.  On
the STREAM lane and the SEQUENCE lane the list `ks` is read — `resumectx_of_landing`
decides `w ∈ ks` and the covers quantify over it.  On the VALUE-LINE lane the
frames list is read the same way **and the bottom's own index is not**: every
one of the `nv` binders occurs exactly once, as `ExplValueLine`'s argument and
nowhere else.

That is the measurement item 202 asked for, and it answers NO: the consumers
cannot spend a list on this lane, because they do not spend the index.

## The surface, and the control on it

The census reads each constant's TYPE, plus the VALUE of a constant whose type
is a DEFINITION rather than a theorem.  Three carriers state the field in their
bodies and in no binder of any type (`ImplicitKeyPack`, `PropsKeyPack`,
`ResumeKeyCtx`), which is item 196's own recorded
gotcha (*a local `have` can carry a copy of a widened type with no binder to
grep for*) in its definitional form.  `surfaceControl` below is the list a
TYPE-ONLY census would miss, pinned — so the cruder instrument's blind spot has
to move a number here before it can hide one there.

`unclassified` is this census's `un=` column, in item 202's sense: a
`ResumeFrames` binder whose bottom is none of the three known lanes.  It is
empty, and a fourth bottom would have to announce itself rather than be
silently dropped. -/

namespace L4YAML.Tests.Guards.IndexCensus

open Lean Elab Command
open L4YAML.Proofs.StreamAccum

/-- Occurrences of the loose bvar at de Bruijn index `i`.  A boolean
    `hasLooseBVar` would answer "yes" for every binder here; the COUNT is what
    separates a read index from a written one. -/
partial def occ (i : Nat) : Expr → Nat
  | .bvar j => if j == i then 1 else 0
  | .app f a => occ i f + occ i a
  | .lam _ t b _ => occ i t + occ (i + 1) b
  | .forallE _ t b _ => occ i t + occ (i + 1) b
  | .letE _ t v b _ => occ i t + occ i v + occ (i + 1) b
  | .mdata _ e => occ i e
  | .proj _ _ e => occ i e
  | _ => 0

/-- A SATURATED `ResumeFrames P ks sp` — or, since item 304, `KeyFrames P ks sp`,
    the value-line stack's own constructor (item 302's stack over mixed levels);
    the partial applications are the same site seen again and are not counted. -/
def resumeBottom (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ =>
      if n != ``ResumeFrames && n != ``KeyFrames then none else
      let args := e.getAppArgs
      if args.size != 3 then none else
        match args[0]!.getAppFn with
        | .const b _ => some b
        | _ => none
  | _ => none

/-- Does `e` state a resume whose frames stand on `bn`? -/
partial def hasBottom (bn : Name) : Expr → Bool
  | e@(.app f a) =>
      (resumeBottom e == some bn) || hasBottom bn f || hasBottom bn a
  | .lam _ t b _ => hasBottom bn t || hasBottom bn b
  | .forallE _ t b _ => hasBottom bn t || hasBottom bn b
  | .letE _ t v b _ => hasBottom bn t || hasBottom bn v || hasBottom bn b
  | .mdata _ e => hasBottom bn e
  | .proj _ _ e => hasBottom bn e
  | _ => false

/-- Any saturated resume at all — what tells an unclassified bottom from a
    binder this census has no business reading. -/
partial def hasResume : Expr → Bool
  | e@(.app f a) => (resumeBottom e).isSome || hasResume f || hasResume a
  | .lam _ t b _ => hasResume t || hasResume b
  | .forallE _ t b _ => hasResume t || hasResume b
  | .letE _ t v b _ => hasResume t || hasResume v || hasResume b
  | .mdata _ e => hasResume e
  | .proj _ _ e => hasResume e
  | _ => false

/-- The ROLE a binder plays in the resume it scopes, read off the term rather
    than off its name: `bottom` if it is the index the value line stands at
    (`ResumeFrames (ExplValueLine _ x) _ _`), `frames` if it is the list of
    still-open levels, `both` if it is somehow both, `other` otherwise.  The
    binder NAME is the cruder key, and `nameControl` below pins the difference:
    a convention is not a measurement. -/
partial def roleAt (i d : Nat) : Expr → Bool × Bool
  | e@(.app f a) =>
      let here :=
        match resumeBottom e with
        | some _ =>
            let args := e.getAppArgs
            let bot := args[0]!.getAppArgs
            ((bot.size != 0 && bot[bot.size - 1]! == Expr.bvar (i + d)),
             args[1]! == Expr.bvar (i + d))
        | _ => (false, false)
      let (lf, rf) := roleAt i d f
      let (la, ra) := roleAt i d a
      (here.1 || lf || la, here.2 || rf || ra)
  | .lam _ t b _ =>
      let (x, y) := roleAt i d t; let (z, w) := roleAt i (d + 1) b; (x || z, y || w)
  | .forallE _ t b _ =>
      let (x, y) := roleAt i d t; let (z, w) := roleAt i (d + 1) b; (x || z, y || w)
  | .letE _ t v b _ =>
      let (x, y) := roleAt i d t; let (z, w) := roleAt i d v
      let (u, q) := roleAt i (d + 1) b; (x || z || u, y || w || q)
  | .mdata _ e => roleAt i d e
  | .proj _ _ e => roleAt i d e
  | _ => (false, false)

def role (body : Expr) : String :=
  match roleAt 0 0 body with
  | (true, true) => "both"
  | (true, false) => "bottom"
  | (false, true) => "frames"
  | (false, false) => "other"

/-- Every `∃ x : τ, body`, as (binder name, type head, occurrences, body). -/
partial def exBinders : Expr → Array (String × String × Nat × Expr) →
    Array (String × String × Nat × Expr)
  | e@(.app (.app (.const ``Exists _) t) (.lam n _ body _)), acc =>
      let tn := match t.getAppFn with | .const c _ => c.toString | _ => "?"
      let acc := acc.push (n.toString, tn, occ 0 body, body)
      match e with
      | .app f a => exBinders a (exBinders f acc)
      | _ => acc
  | .app f a, acc => exBinders a (exBinders f acc)
  | .lam _ t b _, acc => exBinders b (exBinders t acc)
  | .forallE _ t b _, acc => exBinders b (exBinders t acc)
  | .letE _ t v b _, acc => exBinders b (exBinders v (exBinders t acc))
  | .mdata _ e, acc => exBinders e acc
  | .proj _ _ e, acc => exBinders e acc
  | _, acc => acc

/-- Compiler-generated companions restate their parent's binders; they are the
    same site counted again and are not surface. -/
def generated (nm : Name) : Bool :=
  nm.components.any fun c =>
    let s := c.toString
    s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
    s.startsWith "_" ||
    s == "rec" || s == "recOn" || s == "casesOn" || s == "below" ||
    s == "brecOn" || s == "binductionOn" || s == "ibelow" ||
    s == "noConfusion" || s == "noConfusionType" || s == "ndrec" ||
    s == "injEq" || s == "inj" || s == "sizeOf_spec" || s == "toCtorIdx"

partial def conclOf : Expr → Expr
  | .forallE _ _ b _ => conclOf b
  | e => e

/-- A DEFINITION's body is surface — the field is written out there and an
    edit has to reach it.  A THEOREM's body is a proof term, where the same type
    is restated once per intro and is fallout rather than surface (1437
    occurrences against the 43 this census reads). -/
def isDefinition (ci : ConstantInfo) : Bool :=
  match ci with | .defnInfo _ => true | _ => false

def ns : Name := `L4YAML.Proofs.StreamAccum

def lane (body : Expr) : String :=
  if hasBottom ``ExplValueLine body then "valueline"
  else if hasBottom `L4YAML.Surface.SLYamlStream body then "stream"
  else if hasBottom ``SeqEntryTail body then "seq"
  else if hasResume body then "UNCLASSIFIED"
  else ""

/-- The subjects, each with its TYPE surface and (for a predicate `def`) its
    VALUE surface, flagged so the control below can tell them apart. -/
def subjects : CommandElabM (Array (Name × Array (Bool × Expr))) := do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? (ns ++ `flowKeyRoute_of_root)
  let mut out := #[]
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    if generated nm then continue
    let mut ss : Array (Bool × Expr) := #[(false, ci.type)]
    if isDefinition ci then
      if let some v := ci.value? (allowOpaque := true) then
        ss := ss.push (true, v)
    out := out.push (nm, ss)
  return out

/-- One row per (lane, binder, type, occurrence count), with its population. -/
def census : CommandElabM (Array String) := do
  let mut keys : Array String := #[]
  let mut hits : Array String := #[]
  for (_, ss) in ← subjects do
    for (_, s) in ss do
      for (bn, bt, o, body) in exBinders s #[] do
        if bt != "Nat" && bt != "List" then continue
        let l := lane body
        if l == "" then continue
        let k := s!"{l}/{role body}/occ={o}"
        hits := hits.push k
        if !keys.contains k then keys := keys.push k
  return (keys.map fun k => s!"{k}  ×{(hits.filter (· == k)).size}").qsort

/-- **The instrument's second control** (item 202's rule).  The census keyed by
    the binder's NAME instead of by its role in the term, reported per
    constant as the two readings of how many of its binders are the value
    line's own index.  A name is a convention; the rows below are every place
    the convention and the term disagree. -/
def nameControl : CommandElabM (Array String) := do
  let mut rows : Array String := #[]
  for (nm, ss) in ← subjects do
    let mut byName := 0
    let mut byRole := 0
    for (_, s) in ss do
      for (bn, bt, _, body) in exBinders s #[] do
        if bt != "Nat" then continue
        if lane body != "valueline" then continue
        if bn == "nv" then byName := byName + 1
        if role body == "bottom" then byRole := byRole + 1
    if byName != byRole then
      rows := rows.push s!"{nm.getString!} name={byName} role={byRole}"
  return rows.qsort

/-- **The instrument's control** (item 202's rule).  The constants whose
    value-line binders a TYPE-ONLY census cannot see — they state the field in a
    predicate `def`'s body, where no binder of any type mentions it.  An empty
    list here would mean the body surface had stopped earning its keep; a longer
    one, that a fifth carrier had appeared. -/
def surfaceControl : CommandElabM (Array String) := do
  let mut rows : Array String := #[]
  for (nm, ss) in ← subjects do
    let count (body : Bool) : Nat :=
      (ss.filter (fun (b, _) => b == body)).foldl (fun acc (_, s) =>
        acc + ((exBinders s #[]).filter (fun (_, bt, _, bd) =>
          (bt == "Nat" || bt == "List") && lane bd == "valueline")).size) 0
    if count false == 0 && count true > 0 then
      rows := rows.push s!"{nm.getString!} bodyOnly={count true}"
  return rows.qsort

/-- The pinned census, and the row item 202 sent this item to read:
    **`valueline/bottom/occ=1 ×34`** — every index a value-line resume names is
    written once and read nowhere.  `seq/bottom/occ=1 ×9` says the same of the
    sequence lane, and the stream lane has no `bottom` row at all because its
    bottom carries no index.  **43 bottom indices in the module, none of them
    tested.**

    The FRAMES rows are the contrast that makes those numbers mean something:
    the lists ARE read, at occ 2-4, by the `∀ k' ∈ ks` guards, the covers and
    `resumectx_of_landing`'s membership test.  A list in a place where the
    index is read would be spendable; a list where nothing is read is a
    quantifier no consumer can ask about. -/
-- Item 305: `valueline/frames/occ=1` 10 → 3 and `occ=2` 8 → 15, `valueline/other/occ=1` → `occ=3` —
-- the width bound `∀ k' ∈ ks, k' < n` on the two sequence fields, their three restating premises,
-- `pendingProps.h_closeFEV` and `closeThenBlock`'s `h_valFV` names `ks` (and `n`) once more in the binder's own type.
-- 2026-10-29 (item 389): stream frame/other occurrence classes re-counted after the mapping-top conjunct joined the three route faces (it resumes the park's own `ks`: occ=4 ×12 → ×6 and a new occ=5 ×6 class, no new binder).
-- 2026-10-29 (item 394, option B): FlowBaseRoutes.valueF's frame list now occurs three
-- times in its position (Floor, Covered, the resume route) instead of once — two
-- stream/frames positions move occ=1 → occ=3 (×5 → ×3, ×7 → ×9).
def expected : List String :=
  ["seq/bottom/occ=1  ×9",
   "seq/frames/occ=2  ×9",
   "seq/other/occ=2  ×3",
  -- 2026-10-29 (item 394): `FlowBaseRoutes.valueF` and its two close relays read `ResumeFrames (SLYamlStream sp_start) ks` once each (×3 → ×5).
   "stream/frames/occ=1  ×3",
   "stream/frames/occ=2  ×10",
   "stream/frames/occ=3  ×9",
   "stream/frames/occ=4  ×6",
   "stream/frames/occ=5  ×6",
   "stream/other/occ=1  ×27",
   "stream/other/occ=2  ×14",
   "stream/other/occ=3  ×6",
   "stream/other/occ=4  ×4",
   "stream/other/occ=6  ×1",
   "stream/other/occ=8  ×3",
   "valueline/bottom/occ=1  ×34",
   "valueline/frames/occ=1  ×2",
   "valueline/frames/occ=2  ×10",
   "valueline/frames/occ=3  ×8",
   "valueline/frames/occ=4  ×15",
   "valueline/other/occ=10  ×5",
   "valueline/other/occ=13  ×1",
   "valueline/other/occ=16  ×1",
   "valueline/other/occ=19  ×1",
   "valueline/other/occ=2  ×1",
   "valueline/other/occ=3  ×1"]

/-- The three carriers a TYPE-ONLY census cannot see. -/
def expectedSurface : List String :=
  ["ImplicitKeyPack bodyOnly=3",
   "PropsKeyPack bodyOnly=3",
   "ResumeKeyCtx bodyOnly=4"]

/-- **Empty, and that is the reading.**  The binder called `nv` and the binder
    the term uses as a value line's index are the same 34 binders, so in this
    module the convention is faithful — which is a measurement here rather than
    an assumption, and a bottom index introduced under another name would move
    this list rather than pass unseen. -/
def expectedName : List String := []

run_cmd do
  let got ← census
  if got.toList != expected then
    throwError "the index census moved.\nexpected ({expected.length}):\n{
      String.intercalate "\n" expected}\ngot ({got.size}):\n{
      String.intercalate "\n" got.toList}"
  let sc ← surfaceControl
  if sc.toList != expectedSurface then
    throwError "the census's SURFACE control moved — a type-only census now \
      misses a different set.\nexpected:\n{String.intercalate "\n" expectedSurface}\ngot:\n{
      String.intercalate "\n" sc.toList}"
  let nc ← nameControl
  if nc.toList != expectedName then
    throwError "the census's NAME control moved — the binder name and the \
      binder's role in the term no longer agree.\nexpected:\n{
      String.intercalate "\n" expectedName}\ngot:\n{
      String.intercalate "\n" nc.toList}"

end L4YAML.Tests.Guards.IndexCensus
