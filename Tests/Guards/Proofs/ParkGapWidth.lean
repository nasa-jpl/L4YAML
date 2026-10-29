/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.ParkGapCensus

/-!
# How wide the park's gap is, in scanner steps (DOCS item 244)

Item 243 measured the gap `sp_block → sp_scan` at the ELEVEN sites that spend
`SLYamlStream.scannerDrop` and found nothing spanning it: no correspondence at
the block position, no equation, and the only hypothesis naming both endpoints
is the `PendingNode` item 239 refuted.  Its recorded NEXT asked **how many
scanner steps the gap is wide**, and warned that the park might absorb a RUN
rather than a step — in which case the obligation is an induction and a census
counting step equations would under-price it.

## The question has to be asked one level down

Those eleven sites are the park's CONSUMERS, and a consumer holds no scanner
state of its own: `PendingNode.close_with_ssl` receives the park and spends the
escape in its `pendingFlow` branch.  `pendingFlow`'s fields are
`h_stream : SLYamlStream sp_start sp_block` and three facts about `sc` and
`sp_scan.col`; **no field of it names both `sp_block` and `sp_scan`.**  The gap
is therefore fixed where the park is BUILT, by `block_dispatch_deferred` — which
binds `sp_X` free under a stream and pins `sp_scan'` with a correspondence, and
relates the two nowhere.  So §2 reads the producer's own application sites: the
four heads (the producer and its three class wrappers) at **twelve** sites
across **seven** declarations.

## The answer: one step, at six of the nine that have a scanner in scope

| class | sites | width | the step |
|---|---|---|---|
| `_stamp_offcol` / `_stamp_nopack` | 6 | **1** | `scanNextToken_dispatchBlockIndicators` |
| `block_dispatch_deferred` at `accum_content_pending` | 1 | **2** | `…_preprocess` then `…_dispatchContent` |
| `_inline` | 2 | unreached | — |
| the three wrapper bodies | 3 | unreached | nothing in scope |

`corrBlock=0` at all twelve, exactly as item 243 read at the consumers: the
gap's left endpoint carries no scanner state anywhere in the library.  What the
six DO hold is a grammar path from `sp_X` to the dispatch's input position, so
the gap factors and the unpaid factor is one step.

**The width is a measurement of what is IN SCOPE, so the production edges must
be the ones a site HOLDS.**  Counting edges inside an implication's antecedent
reads `accum_content_pending` at width 1 instead of 2 — the site would be
crossing its own gap with the obligation being priced.  `posEdges` descends into
a hypothesis's conclusion and never into its premises, and that restriction is
what moves the one reading.

## The two censuses meet at one step, and the meeting point is empty

Item 242 measured how often the library carries a grammar production across a
scanner step: once, in 294 dispatch holders.  §3 re-derives that ladder for the
three functions these sites actually cross, in THIS module's import closure:

| function | holders | edge | chain |
|---|---|---|---|
| `scanNextToken_dispatchBlockIndicators` | 97 | **0** | **0** |
| `scanNextToken_dispatchContent` | 129 | 2 | 1 |
| `scanNextToken_preprocess` | 186 | 17 | 6 |

A holder count moves with what is imported and the crossings do not: the last
two agree with item 242's own pins, taken one module earlier.

**The six sites whose gap is one step cross the one function with no precedent
at all.**  Not one of its holders carries a production landing on its output,
let alone a path to it.  The function with a worked crossing is at the site
whose gap is two.

## What the one step actually is: one character

§1 proves it rather than counting it, which is what answers the mandate's RUN
warning.  Every arm of `scanNextToken_dispatchBlockIndicators` —
`scanBlockEntry`, `scanKey`, `scanValue` — ends in exactly one
`ScannerState.advance`, and none of the emits, indent pushes or key clearings
in front of it touches the four fields `ScannerSurfCorr` reads.  So the step
consumes ONE character, and under the sites' own non-break indicator the
production owed across it is a single `GLit` — `[184] c-l-block-seq-entry`,
`[190] c-l-block-map-explicit-key` or `[6] c-mapping-value`, the three rules
the scanner function already carries as spec annotations.

**The park does not absorb a run.**  The obligation at six of the twelve is one
literal character, not an induction over a flow collection.
-/

set_option autoImplicit false

open Lean Lean.Meta Lean.Elab
open L4YAML
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.CouplingBridge
open Tests.Guards.DropDependents (usesAll modOf sorted)
open Tests.Guards.DispatchPrice (isProd readDecl)

namespace Tests.Guards.ParkGapWidth

/-! ## §1 The one step is one character -/

/-- The four fields `ScannerSurfCorr` reads off a scanner state.  Two states
    agreeing on them stand at the same surface position. -/
structure Cursor (a b : ScannerState) : Prop where
  input : a.input = b.input
  inputEnd : a.inputEnd = b.inputEnd
  offset : a.offset = b.offset
  col : a.col = b.col

lemma Cursor.rfl' (a : ScannerState) : Cursor a a := ⟨rfl, rfl, rfl, rfl⟩

lemma cursor_trans {a b c : ScannerState} (h₁ : Cursor a b) (h₂ : Cursor b c) : Cursor a c :=
  ⟨h₁.input.trans h₂.input, h₁.inputEnd.trans h₂.inputEnd,
   h₁.offset.trans h₂.offset, h₁.col.trans h₂.col⟩

/-- `advance` reads only those four fields and writes only two of them, so it
    is a function of the cursor alone. -/
lemma cursor_advance {a b : ScannerState} (h : Cursor a b) : Cursor a.advance b.advance := by
  obtain ⟨hi, he, ho, hc⟩ := h
  unfold ScannerState.advance
  rw [hi, he, ho, hc]
  dsimp only
  repeat' split
  all_goals first
    | exact ⟨rfl, rfl, rfl, rfl⟩
    | exact ⟨hi, he, ho, hc⟩

lemma cursor_emit (s : ScannerState) (t : YamlToken) : Cursor (s.emit t) s :=
  ⟨rfl, rfl, rfl, rfl⟩

lemma cursor_pushSeq (s : ScannerState) (n : Int) : Cursor (pushSequenceIndent s n) s := by
  unfold pushSequenceIndent; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

lemma cursor_pushMap (s : ScannerState) (n : Int) : Cursor (pushMappingIndent s n) s := by
  unfold pushMappingIndent; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

lemma cursor_clearKey (s : ScannerState) : Cursor (scanValueClearKey s) s := by
  simp only [scanValueClearKey]
  repeat' split
  all_goals first
    | exact Cursor.rfl' s
    | exact cursor_pushMap s _
    | exact cursor_pushSeq s _
    | exact ⟨rfl, rfl, rfl, rfl⟩

lemma cursor_prepare (s : ScannerState) : Cursor (scanValuePrepare s) s := by
  simp only [scanValuePrepare]
  repeat' split
  all_goals first
    | exact Cursor.rfl' s
    | exact cursor_pushMap s _
    | exact cursor_pushSeq s _
    | exact ⟨rfl, rfl, rfl, rfl⟩

/-- Transport a cursor along a record copy that touches none of the four
    fields — which is how every indicator scan returns. -/
lemma cursor_of {a b c : ScannerState} (h : Cursor b c)
    (hi : a.input = b.input) (he : a.inputEnd = b.inputEnd)
    (ho : a.offset = b.offset) (hc : a.col = b.col) : Cursor a c :=
  ⟨hi.trans h.input, he.trans h.inputEnd, ho.trans h.offset, hc.trans h.col⟩

/-- One emit then one `advance`, from any state sharing the cursor. -/
lemma cursor_step {s t : ScannerState} (h : Cursor t s) (tok : YamlToken) :
    Cursor (t.emit tok).advance s.advance :=
  cursor_advance (cursor_trans (cursor_emit t tok) h)

lemma cursor_blockEntry {s s' : ScannerState} (h : scanBlockEntry s = Except.ok s') :
    Cursor s' s.advance := by
  unfold scanBlockEntry at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h
       subst h
       first
         | exact cursor_of (cursor_step (cursor_pushSeq s (s.col : Int))
             YamlToken.blockEntry) rfl rfl rfl rfl
         | exact cursor_of (cursor_step (Cursor.rfl' s) YamlToken.blockEntry)
             rfl rfl rfl rfl)
    | (exfalso; simp at h)

lemma cursor_key {s s' : ScannerState} (h : scanKey s = Except.ok s') :
    Cursor s' s.advance := by
  unfold scanKey at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h
       subst h
       first
         | exact cursor_of (cursor_step (cursor_pushMap s (s.col : Int))
             YamlToken.key) rfl rfl rfl rfl
         | exact cursor_of (cursor_step (Cursor.rfl' s) YamlToken.key)
             rfl rfl rfl rfl)
    | (exfalso; simp at h)

lemma cursor_value {s s' : ScannerState} (h : scanValue s = Except.ok s') :
    Cursor s' s.advance := by
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h
       subst h
       exact cursor_of (cursor_step (cursor_trans (cursor_prepare (scanValueClearKey s))
         (cursor_clearKey s)) YamlToken.value) rfl rfl rfl rfl)
    | (exfalso; simp at h)

/-- **The gap's one step is exactly one `advance`.**  All three arms of the
    block-indicator dispatch emit a token, push at most one indent and advance
    once; none of that moves `input`, `inputEnd`, `offset` or `col` except the
    single advance. -/
lemma cursor_dispatchBI {s s' : ScannerState} {c : Char}
    (h : scanNextToken_dispatchBlockIndicators s c = Except.ok (some s')) :
    Cursor s' s.advance := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | exact Except.noConfusion h
    | (simp only [Except.ok.injEq, reduceCtorEq] at h; done)
    | (simp only [Except.ok.injEq, Option.some.injEq] at h
       subst h
       first
         | exact cursor_blockEntry ‹_›
         | exact cursor_key ‹_›
         | exact cursor_value ‹_›)

/-- **…so it consumes exactly one character.**  The surface position the step's
    output corresponds to is the input's, minus its head. -/
lemma dispatchBI_consumes_one {s s' : ScannerState} {c ch : Char} {rest : List Char}
    {sp_in sp_out : SurfPos}
    (h_step : scanNextToken_dispatchBlockIndicators s c = Except.ok (some s'))
    (h_in : ScannerSurfCorr s sp_in) (h_out : ScannerSurfCorr s' sp_out)
    (h_chars : sp_in.chars = ch :: rest) :
    sp_out.chars = rest := by
  have hcur := cursor_dispatchBI h_step
  have hcf : CharsFromOffset s.input s.offset (ch :: rest) := h_chars ▸ h_in.chars_from
  match hcf with
  | .cons _ hp _ _ _ hrest =>
    have hmore : s.offset < s.inputEnd := by rw [h_in.end_eq]; exact hp
    have hout := h_out.chars_from
    rw [hcur.input, hcur.offset, advance_input, advance_offset_eq s hmore] at hout
    exact CharsFromOffset_unique hout hrest

/-- **…and the production owed across it is one `GLit`.**  The indicators the
    dispatch admits — `-`, `?`, `:` — are not line breaks, so the column moves
    by one and the span is `[184]`, `[190]` or `[6]`'s own literal: a
    constructor, not an induction. -/
lemma dispatchBI_span_glit {s s' : ScannerState} {c ch : Char} {rest : List Char}
    {sp_in sp_out : SurfPos}
    (h_step : scanNextToken_dispatchBlockIndicators s c = Except.ok (some s'))
    (h_in : ScannerSurfCorr s sp_in) (h_out : ScannerSurfCorr s' sp_out)
    (h_chars : sp_in.chars = ch :: rest)
    (hnl : ch ≠ '\n') (hcr : ch ≠ '\r') :
    GLit ch sp_in sp_out := by
  have hcur := cursor_dispatchBI h_step
  have hcf : CharsFromOffset s.input s.offset (ch :: rest) := h_chars ▸ h_in.chars_from
  match hcf with
  | .cons _ hp _ _ hc _ =>
    have hmore : s.offset < s.inputEnd := by rw [h_in.end_eq]; exact hp
    have hnlb : ¬ (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\n') = true := by
      rw [hc]; simp [hnl]
    have hcrb : ¬ (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\r') = true := by
      rw [hc]; simp [hcr]
    have hrest' : sp_out.chars = rest := dispatchBI_consumes_one h_step h_in h_out h_chars
    have hcol : sp_out.col = sp_in.col + 1 := by
      rw [h_out.col_eq, hcur.col, advance_col_non_newline s hmore hnlb hcrb, h_in.col_eq]
    have hin' : sp_in = ⟨ch :: rest, sp_in.col⟩ := by rw [← h_chars]
    have hout' : sp_out = ⟨rest, sp_in.col + 1⟩ := by rw [← hrest', ← hcol]
    rw [hin', hout']
    exact GLit.mk rest sp_in.col

/-! ## §2 The width census -/

/-- The park's producer and the three wrappers item 185 split its classes into.
    All four take `sp_start sp_X sp_scan' s'` as their first four arguments, so
    one index pair reads every site. -/
def producer : Name := `L4YAML.Proofs.StreamAccum.block_dispatch_deferred
def wrapOffcol : Name := `L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol
def wrapNopack : Name := `L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack
def wrapInline : Name := `L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline

def heads : List Name := [producer, wrapOffcol, wrapNopack, wrapInline]

partial def fvarsAux (e : Expr) : StateM (Std.HashSet Expr × Array Expr) Unit := do
  if (← get).1.contains e then return
  modify fun (s, a) => (s.insert e, a)
  if e.isFVar then modify fun (s, a) => (s, a.push e)
  let _ ← e.foldlM (fun (_ : Unit) s => fvarsAux s) ()

def fvarsOf (e : Expr) : Array Expr := ((fvarsAux e).run ({}, #[])).2.2

/-- A scanner step equation, item 242's reading verbatim. -/
def stepEqFn? (t : Expr) : Option Name := do
  guard (t.isAppOfArity ``Eq 3)
  let lhs := t.appFn!.appArg!
  guard (t.appArg!.isAppOf ``Except.ok)
  let .const f _ := lhs.getAppFn | none
  guard ((`L4YAML.Scanner).isPrefixOf f)
  some f

/-- The production edges a hypothesis of type `t` actually GIVES.  Only
    strictly positive occurrences count: an edge inside an implication's
    antecedent is something the site would have to SUPPLY, and counting it
    would let a site cross its own gap with the obligation being priced. -/
partial def posEdges (prods : Std.HashSet Name) (t : Expr) : MetaM (Array (Expr × Expr)) := do
  match t with
  | .forallE nm a b bi =>
    withLocalDecl nm bi a fun x => posEdges prods (b.instantiate1 x)
  | .mdata _ b => posEdges prods b
  | _ =>
    if t.isAppOfArity ``And 2 then
      return (← posEdges prods t.appFn!.appArg!) ++ (← posEdges prods t.appArg!)
    if t.isAppOfArity ``Exists 2 then
      match t.appArg! with
      | .lam nm a b bi => return ← withLocalDecl nm bi a fun x => posEdges prods (b.instantiate1 x)
      | _ => return #[]
    if let .const n _ := t.getAppFn then
      if prods.contains n then
        let args := t.getAppArgs
        if args.size ≥ 2 then
          return #[(args[args.size-2]!, args[args.size-1]!)]
    return #[]

/-- One application of one of the four heads, with the gap's width in scanner
    steps: productions in scope are free, one step equation costs one. -/
structure Site where
  decl : Name
  fn : Name
  /-- `none` when no chain of steps in scope reaches the scan position. -/
  width : Option Nat
  corrBlock : Nat
  corrScan : Nat
  via : Array Name
deriving Inhabited

abbrev W := StateRefT (Array Site × Std.HashSet Expr) MetaM

/-- Read one application site against the local context it stands in. -/
def record (prods : Std.HashSet Name) (decl fn : Name) (a b : Expr) : W Unit := do
  let lctx ← getLCtx
  let mut corrs : Array (Expr × Expr) := #[]
  let mut steps : Array (Name × Array Expr × Array Expr) := #[]
  let mut pedges : Array (Expr × Expr) := #[]
  for ld in lctx do
    if ld.isImplementationDetail then continue
    let t := ld.type
    unless (← inferType t).isProp do continue
    if t.isAppOfArity ``ScannerSurfCorr 2 then
      corrs := corrs.push (t.appFn!.appArg!, t.appArg!)
    if (stepEqFn? t).isSome then
      let f := (stepEqFn? t).get!
      let inS ← (fvarsOf t.appFn!.appArg!).filterM fun v =>
        return (← inferType v).isConstOf ``ScannerState
      let outS ← (fvarsOf t.appArg!).filterM fun v =>
        return (← inferType v).isConstOf ``ScannerState
      steps := steps.push (f, inS, outS)
    pedges := pedges ++ (← posEdges prods t)
  let posAt (s : Expr) : Array Expr := (corrs.filter (fun q => q.1 == s)).map (·.2)
  let close (S : Std.HashSet Expr) : Std.HashSet Expr := Id.run do
    let mut seen := S
    let mut todo : List Expr := S.toList
    while !todo.isEmpty do
      let x := todo.head!; todo := todo.tail!
      for (l, r) in pedges do
        if l == x && !seen.contains r then seen := seen.insert r; todo := r :: todo
    return seen
  let mut layer := close (({} : Std.HashSet Expr).insert a)
  let mut width : Option Nat := if layer.contains b then some 0 else none
  let mut via : Array Name := #[]
  let mut k := 0
  while width.isNone && k < 6 do
    k := k + 1
    let mut next := layer
    for (f, inS, outS) in steps do
      if inS.any (fun i => (posAt i).any (fun p => layer.contains p)) then
        for o in outS do
          for q in posAt o do
            if !next.contains q then
              next := next.insert q
              via := via.push f
    let grown := close next
    if grown.size == layer.size then k := 99
    layer := grown
    if layer.contains b then width := some k
  let mut uniq : Array Name := #[]
  for f in sorted via do
    unless uniq.contains f do uniq := uniq.push f
  modify fun (hs, v) =>
    (hs.push { decl, fn, width,
               corrBlock := (corrs.filter (fun q => q.2 == a)).size,
               corrScan := (corrs.filter (fun q => q.2 == b)).size,
               via := if width.isSome then uniq else #[] }, v)

/-- Walk a proof term under its binders, item 243's walk with this item's
    heads: the correspondences, the step equations and the productions in
    scope live in the context an application stands in. -/
partial def walk (prods : Std.HashSet Name) (decl : Name) (e : Expr) : W Unit := do
  if (← get).2.contains e then return
  modify fun (hs, v) => (hs, v.insert e)
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .const n _ := f then
      if heads.contains n && args.size > 3 then
        record prods decl n args[1]! args[2]!
    walk prods decl f
    for x in args do walk prods decl x
  | .lam nm t b bi =>
    walk prods decl t
    withLocalDecl nm bi t fun x => walk prods decl (b.instantiate1 x)
  | .letE nm t val b _ =>
    walk prods decl t
    walk prods decl val
    withLetDecl nm t val fun x => walk prods decl (b.instantiate1 x)
  | .forallE nm t b bi =>
    walk prods decl t
    withLocalDecl nm bi t fun x => walk prods decl (b.instantiate1 x)
  | .mdata _ b => walk prods decl b
  | .proj _ _ b => walk prods decl b
  | _ => pure ()

def render (s : Site) : String :=
  let w := match s.width with | some n => toString n | none => "UNREACHED"
  s!"{s.decl} <- {s.fn} width={w} corrBlock={s.corrBlock} corrScan={s.corrScan} \
via={String.intercalate "," (s.via.map (·.getString!)).toList}"

/-! ## §3 The pins -/

/-- **The population, re-derived rather than typed.**  Every authored
    declaration whose proof term references the producer or one of its three
    wrappers, and every application site inside those terms.  DOCS item 287
    moves the inline wrapper's applications to the arms they stand for, so
    `colon_fires_implicit_key`, `colon_fires_props_key` and
    `accum_block_pending` join the population (7 → 10) and the sites move by
    their one each, less the two `accum_block_on_*` lost (12 → 13). -/
def expectedPop : String := "pop=10 sites=13"

/-- **The answer, in one line.**  Six sites one step wide, ~~one~~ two two,
    five with no scanner chain reaching the scan position at all — and
    `corrBlock=0` everywhere, which is item 243's reading taken one level down.
    DOCS item 287 traded the two `accum_block_on_*` inline sites, both
    unreached, for three: `accum_block_pending`'s, two steps wide, and the two
    `:` consumers', unreached. -/
def expectedWidth : String :=
  "w0=0 w1=6 w2=2 unreached=5 corrBlock=0 corrScan=13"

/-- Every site, with the step functions its width is spent on. -/
def expectedSites : List String :=
  ["L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack width=1 \
corrBlock=0 corrScan=1 via=scanNextToken_dispatchBlockIndicators",
   "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol width=1 \
corrBlock=0 corrScan=1 via=scanNextToken_dispatchBlockIndicators",
   "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack width=1 \
corrBlock=0 corrScan=1 via=scanNextToken_dispatchBlockIndicators",
   "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol width=1 \
corrBlock=0 corrScan=1 via=scanNextToken_dispatchBlockIndicators",
   "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack width=1 \
corrBlock=0 corrScan=1 via=scanNextToken_dispatchBlockIndicators",
   "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol width=1 \
corrBlock=0 corrScan=1 via=scanNextToken_dispatchBlockIndicators",
   "L4YAML.Proofs.StreamAccum.accum_block_pending <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline width=2 \
corrBlock=0 corrScan=1 via=scanNextToken_dispatchBlockIndicators,scanNextToken_preprocess",
   "L4YAML.Proofs.StreamAccum.accum_content_pending <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred width=2 \
corrBlock=0 corrScan=1 via=scanNextToken_dispatchContent,scanNextToken_preprocess",
   "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred width=UNREACHED \
corrBlock=0 corrScan=1 via=",
   "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred width=UNREACHED \
corrBlock=0 corrScan=1 via=",
   "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred width=UNREACHED \
corrBlock=0 corrScan=1 via=",
   "L4YAML.Proofs.StreamAccum.colon_fires_implicit_key <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline width=UNREACHED \
corrBlock=0 corrScan=1 via=",
   "L4YAML.Proofs.StreamAccum.colon_fires_props_key <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline width=UNREACHED \
corrBlock=0 corrScan=1 via="]

/-- **The ladder, for the three functions these sites cross**, re-derived in
    THIS module's import closure so the numbers are the ones the census above
    is read against.  Item 242 pinned the last two at 129 and 186 holders in
    its own closure; a holder count moves with what is imported, and the
    crossings do not.  Item 267's carrier source and the dedent it reads through
    are two more holders of preprocessing's equation and cross nothing.  Item
    269 restates that source and the equation is spent once, at
    `preprocess_floor_eq`, which is a third holder that crosses nothing either,
    so the ladder's last row reads 189 with its two crossings unmoved.  Item
    272 adds a fourth holder, the composition that applies the source at an arm
    holding the `[63]` failure located; it hands the equation on rather than
    reading a position off it, so the row reads 190 and both crossings are
    still where item 242 left them.  Item 284 adds sixteen holders and no
    crossing: the four `dispatchBlock_*_offerPred` read the `-`/`?`/`:`
    dispatch's last token, `slotGateAt_spend` the content dispatch's, and the
    slot face's eleven transport and gate lemmas hand preprocessing's equation
    on — so the rows read 101, 130 and 201 with every `edge` and `chain` where
    they were.  DOCS item 287 adds one holder of two of them and no crossing:
    the inline wrapper reads its premises off the dispatch and its
    preprocessing, so the rows read 102, 130 and 202.  DOCS item 293 adds
    three content-dispatch holders and four preprocessing ones and no crossing
    — the possibility lemmas `DispatchPrice` names — so the rows read 102, 133
    and 206.  DOCS item 299 adds two holders of each and no crossing — the
    `docStartLine` field's transport, `dispatchContent_preserves_docStartLine`
    and `dispatchContent_docStartLine` for the content dispatch,
    `preprocess_preserves_docStartLine` and `ad_docStartLine` for
    preprocessing — so the rows read 102, 135 and 208.  DOCS item 300 adds
    one preprocessing holder, `flowOpen_marker`, and no crossing — 102, 135
    and 209. -/
-- 2026-10-20 (item 309): `scanNextToken_preprocess` holders 209 → 212 (the sentinel transports and the refutation).
-- 2026-10-21 (item 313): `holders` +2 on both rungs — `ExplicitValueRefused.step_content` and `PackAlt.step_content`
-- hold the preprocess and the content dispatch as hypotheses; no edge or chain moves.
-- 2026-10-21 (item 314): the dispatch rung's `holders` 137 → 139 — the two `step_dispatch` declarations.
-- 2026-10-21 (item 315): the dispatch rung's `holders` 139 → 140 — `entryPropsKeyPack_of_dispatch`'s new premise.
-- 2026-10-21 (item 318): `dispatchBlockIndicators holders` 102 → 106, `preprocess holders` 214 → 216 — the block lane's two
-- transports (`ExplicitValueRefused.step_blockEntry`, `.step_value`) and their `PackAlt` wrappers hold the block dispatch and
-- the preprocess (+4 each); item 309's `preprocess_currentIndent_neg` and `indent_neg_dis_of_park`, deleted, held the preprocess (−2).
-- 2026-10-21 (item 324): `preprocess holders` 216 → 218 — `ExplicitValueRefused.step_preprocess` and its `PackAlt` wrapper
-- hold the preprocess as a hypothesis; no edge or chain moves.
-- 2026-10-23 (item 348): `scanNextToken_preprocess holders` 223 → 224 — `preprocess_col0_dead` reads the preprocess equation; edge/chain stand.
-- 2026-10-23 (item 349): `scanNextToken_dispatchBlockIndicators` holders=110 edge=0 chain=0 → holders=112 edge=0 chain=0 —
-- `not_blockEntryCandidate_of_dispatch_none` / `indicatorAt_false_of_dispatch_none` hold the dispatch equation.
-- 2026-10-24 (B3 [66] col-0 threading): holders 110/146/224 → 114/157/240 (gate / NextIsSep / JSON-key /
-- reservation lemmas); the block-indicator and content dispatchers each gain one `sp_gram` edge;
-- preprocess chain 6 → 3 — three carriers read the edge directly (holders re-read on the item-355 base).
def expectedLadder : List String :=
-- 2026-10-24 (item 350): holders=112 → 113 — `dispatchBlock_colon_notQuestion` reads the `:`
-- dispatch equation to hand every `:` producer `NotQuestionPark`.
-- 2026-10-23 (item 357): holders=117 → 119 — `dispatchBlockIndicators_markedCols` and its `_of_ne`
--   twin read the block-indicator dispatch to transport `MarkedColsIn` across the `-`/`?`/`:` step.
-- 2026-10-25 (item 358): holders=119 → 120 — `landing_frame_of_cover` (the K1 bridge) holds the dispatch.
-- 2026-10-25 (item 360): holders=120 → 121 — `refused_of_outer_disp` (the K7 bridge) holds the dispatch.
  -- Item 372 (2026-10-27): `seqTopKey_refuted_at_colon` holds the `:` dispatch (+1 holder).
  -- Item 387 (2026-10-29): `seqTop_refuted_at_indicator_le` holds the `:`/`?` dispatch (+1 holder).
  ["scanNextToken_dispatchBlockIndicators holders=127 edge=1 chain=0",
   "scanNextToken_dispatchContent holders=159 edge=3 chain=1",
   "scanNextToken_preprocess holders=243 edge=17 chain=3"]

/-- **What §1's proofs spend.**  `drop=false` is the non-circularity check
    items 242 and 243 also carry: a measurement of what the escape costs may
    not route through the escape.  `glit=true` records that the span's
    conclusion is the grammar's own literal and not a bespoke relation. -/
def expectedSpend : String := "drop=false glit=true corr=true"

set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (authored, usesVal) := usesAll env
  let mut prods : Std.HashSet Name := {}
  let mut surf : Std.HashSet Name := {}
  for n in authored do
    if ← isProd n then
      prods := prods.insert n
      if (`L4YAML.Surface).isPrefixOf (modOf env n) then surf := surf.insert n
  let mut pop : Array Name := #[]
  for n in authored do
    let uv := usesVal.getD n {}
    if heads.any (fun h => uv.contains h) then pop := pop.push n
  let mut sites : Array Site := #[]
  for n in sorted pop do
    let some ci := env.find? n | continue
    let some val := ci.value? (allowOpaque := true) | continue
    let (_, (hs, _)) ← (walk prods n val).run (#[], {})
    sites := sites ++ hs
  let gotP := s!"pop={pop.size} sites={sites.size}"
  unless gotP == expectedPop do
    throwError "the producer's site population moved:\n  got      {gotP}\n  expected {expectedPop}"
  let cnt (f : Site → Bool) : Nat := (sites.filter f).size
  let gotW := s!"w0={cnt (·.width == some 0)} w1={cnt (·.width == some 1)} \
w2={cnt (·.width == some 2)} unreached={cnt (·.width.isNone)} \
corrBlock={cnt (·.corrBlock > 0)} corrScan={cnt (·.corrScan > 0)}"
  unless gotW == expectedWidth do
    throwError "the gap's width moved:\n  got      {gotW}\n  expected {expectedWidth}"
  let rows := (sites.map render).qsort (· < ·)
  unless rows.toList == expectedSites do
    throwError "the sites moved:\n{String.intercalate "\n" rows.toList}"
  -- §3 the ladder, one pass for the three functions
  let fns : Array Name :=
    #[`L4YAML.Scanner.scanNextToken_dispatchBlockIndicators,
      `L4YAML.Scanner.scanNextToken_dispatchContent,
      `L4YAML.Scanner.scanNextToken_preprocess]
  let mut holders : Array Nat := #[0, 0, 0]
  let mut edges : Array Nat := #[0, 0, 0]
  let mut chains : Array Nat := #[0, 0, 0]
  for n in authored do
    let r ← readDecl surf n
    for i in [0, 1, 2] do
      let f := fns[i]!
      if r.fns.contains f then
        holders := holders.set! i (holders[i]! + 1)
        if r.edgeFns.contains f then edges := edges.set! i (edges[i]! + 1)
        if r.chainFns.contains f then chains := chains.set! i (chains[i]! + 1)
  let ladder : List String :=
    (List.range 3).map fun i =>
      s!"{fns[i]!.getString!} holders={holders[i]!} edge={edges[i]!} chain={chains[i]!}"
  unless ladder == expectedLadder do
    throwError "the ladder moved:\n{String.intercalate "\n" ladder}"
  -- §4 what the proofs spend
  let usedBy (n : Name) : Array Name :=
    match env.find? n with
    | none => #[]
    | some ci => ((ci.value? (allowOpaque := true)).getD (mkConst n)).getUsedConstants
  let deps := usedBy ``cursor_dispatchBI ++ usedBy ``dispatchBI_consumes_one
    ++ usedBy ``dispatchBI_span_glit
  let gotS := s!"drop={deps.contains ``SLYamlStream.scannerDrop} \
glit={deps.contains ``GLit} corr={deps.contains ``ScannerSurfCorr}"
  unless gotS == expectedSpend do
    throwError "the span proofs' dependencies moved:\n  got      {gotS}\n  expected {expectedSpend}"
  logInfo m!"ParkGapWidth {gotP} {gotW} ladder={String.intercalate "|" ladder} {gotS}"

end Tests.Guards.ParkGapWidth
