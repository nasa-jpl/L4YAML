import Tests.Guards.Proofs.RelaySupplyCensus

/-!
# Opener fallback reachability (item 375, PR #139 review follow-up)

`Tests/AdversarialInstantiation.lean`'s Priority 43 reads the scanner's landings and the
parser's verdict on the openers' sibling inputs — the UNREFUTABLE leg of item 375's reading.
It cannot read which arm of an opener's five-way route match (`h_routeE`) a proof takes:
that is a term-level fact (§7 — a pin on a `Prop` is vacuous), so it is read here off the
proof terms, with `RelaySupplyCensus`'s edge walker.

For each of the five opener lemmas the fallback arm is the catch-all of the match on the
optional contexts (`_ ∨ True` binders: `h_res_land`, `h_sfx_land`, `h_nodoc_land`,
`h_mk_land`, `h_pr_land`, …).  The fallback is REACHABLE from a caller exactly when that
caller supplies EVERY optional context as `Or.inr trivial` (`DECLINE`); a caller that pays
or relays one of them selects an earlier arm.  The pin below lists, per opener and caller,
how each optional context is supplied, and the summary counts the all-`DECLINE` callers —
the sites item 375 calls "the seven opener arms with no sink".  A caller that is not
all-`DECLINE` is not a fallback site, whatever the parser says about its inputs.
-/

open Lean Meta Elab Command L4YAML.Tests.Guards.RelaySupplyCensus

namespace L4YAML.Tests.Guards.OpenerFallbackReach

def ns : Name := `L4YAML.Proofs.StreamAccum

def openers : List Name :=
  [`colon_open_map, `question_open_map, `flowKeyRoute_of_root,
   `accum_flow_open_depth0, `accum_block_on_closeThenBlock]

/-- `(idx, name)` of every `_ ∨ True` binder of `n`'s type: the optional contexts. -/
def optBinders (n : Name) : MetaM (Array (Nat × Name)) := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ => do
    let mut out := #[]
    for h : i in [:xs.size] do
      let t ← inferType xs[i]
      if let some (_, r) := t.app2? ``Or then
        if r.isConstOf ``True then
          out := out.push (i, (← xs[i].fvarId!.getUserName))
    return out

/-- Every caller path above `callee` (nearest caller first), to depth `fuel`, including the
truncated prefixes. -/
partial def paths (es : Array Edge) (callee : Name) (fuel : Nat) : Array (List Name) :=
  let callers := (es.filter (·.callee == callee)).foldl (init := (#[] : Array Name))
    fun acc e => if acc.contains e.caller then acc else acc.push e.caller
  callers.foldl (init := #[]) fun acc c =>
    let acc := acc.push [c]
    if fuel == 0 then acc else acc ++ (paths es c (fuel - 1)).map (c :: ·)

/-- How binder `idx` of `callee` is settled along one caller path: the `how` at the first hop
that does not `RELAY` it (a relayed binder is re-read at the caller's own `rootTgt` binder);
`RELAY` if the path ends before settling it; `-` if an edge is missing. -/
def settle (es : Array Edge) : Name → Nat → List Name → String
  | _, _, [] => "RELAY"
  | callee, idx, c :: rest =>
    match es.find? (fun e => e.callee == callee && e.caller == c && e.idx == idx) with
    | none => "-"
    | some e =>
      let hd := (e.how.splitOn " ").head!
      match hd, e.rootTgt with
      | "RELAY", some j => settle es c j rest
      | _, _ => hd

/-- One line per distinct `(opener, caller path settlement)`.  `FALLBACK` = every optional
context settles `DECLINE` on that path (the catch-all arm is what the path buys); `PAYS` =
some context settles `PAY` on that path (which arm is selected depends on which context); `OPEN` = a context settles at a case
split / pipe / local fact (`SPLIT`/`VIA`/`LOCAL`/`FIELD`) or is still relayed at the depth
bound, which this reading cannot settle. -/
def rowsFor (n : Name) : CommandElabM (Array String × (Nat × Nat × Nat)) := do
  let full := ns ++ n
  let opts ← liftTermElabM (optBinders full)
  let (es, _) ← edges full
  let mut rows := #[]
  let mut fb := 0
  let mut rt := 0
  let mut op := 0
  for path in paths es full 6 do
    let cells := opts.map fun (i, b) => (b, settle es full i path)
    let dec := (cells.filter (·.2 == "DECLINE")).size
    let pay := (cells.filter (·.2 == "PAY")).size
    let verdict :=
      if opts.size > 0 && dec == opts.size then "FALLBACK"
      else if pay > 0 then "PAYS" else "OPEN"
    let row := s!"{n} ← {" ← ".intercalate (path.map (·.replacePrefix ns Name.anonymous |>.toString))}: {
      " ".intercalate (cells.map (fun (b, h) => s!"{b}={h}")).toList} {verdict}"
    if rows.contains row then continue
    if verdict == "FALLBACK" then fb := fb + 1
    else if verdict == "PAYS" then rt := rt + 1 else op := op + 1
    rows := rows.push row
  rows := rows.push s!"{n}: opts={opts.size} paths={rows.size} fallback={fb} pays={rt} open={op}"
  return (rows, (fb, rt, op))

def expectedSummary : String :=
  "openers=5 fallback=0 pays=18 open=18"

def expectedRows : List String :=
  ["colon_open_map ← indicator_open_map: h_sfx_land=RELAY h_nodoc_land=RELAY h_mk_land=RELAY h_res_land=RELAY h_ref_land=RELAY h_cov_in=SPLIT h_pr_land=RELAY OPEN",
    "colon_open_map ← indicator_open_map ← accum_block_on_noPending: h_sfx_land=DECLINE h_nodoc_land=PAY h_mk_land=DECLINE h_res_land=DECLINE h_ref_land=DECLINE h_cov_in=SPLIT h_pr_land=DECLINE PAYS",
    "colon_open_map ← indicator_open_map ← accum_block_on_pendingBlock: h_sfx_land=DECLINE h_nodoc_land=DECLINE h_mk_land=DECLINE h_res_land=SPLIT h_ref_land=DECLINE h_cov_in=SPLIT h_pr_land=DECLINE OPEN",
    "colon_open_map ← indicator_open_map ← accum_block_on_pendingBlock ← accum_block_pending: h_sfx_land=DECLINE h_nodoc_land=DECLINE h_mk_land=DECLINE h_res_land=SPLIT h_ref_land=DECLINE h_cov_in=SPLIT h_pr_land=DECLINE OPEN",
    "colon_open_map ← indicator_open_map ← accum_block_on_closeThenBlock: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=RELAY h_cov_in=SPLIT h_pr_land=SPLIT OPEN",
    "colon_open_map ← indicator_open_map ← accum_block_on_closeThenBlock ← accum_block_on_pendingContent: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=PAY h_cov_in=SPLIT h_pr_land=SPLIT PAYS",
    "colon_open_map ← indicator_open_map ← accum_block_on_closeThenBlock ← accum_block_on_pendingContent ← accum_block_pending: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=PAY h_cov_in=SPLIT h_pr_land=SPLIT PAYS",
    "colon_open_map ← indicator_open_map ← accum_block_on_closeThenBlock ← accum_block_pending: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=DECLINE h_cov_in=SPLIT h_pr_land=SPLIT OPEN",
    "colon_open_map ← indicator_open_map ← accum_block_on_closeThenBlock ← accum_block_on_pendingBlock: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=DECLINE h_cov_in=SPLIT h_pr_land=SPLIT OPEN",
    "colon_open_map ← indicator_open_map ← accum_block_on_closeThenBlock ← accum_block_on_pendingBlock ← accum_block_pending: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=DECLINE h_cov_in=SPLIT h_pr_land=SPLIT OPEN",
    "colon_open_map ← indicator_open_map ← accum_block_on_closeThenBlock ← accum_block_on_pendingBlockContent: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=PAY h_cov_in=SPLIT h_pr_land=SPLIT PAYS",
    "colon_open_map ← indicator_open_map ← accum_block_on_closeThenBlock ← accum_block_on_pendingBlockContent ← accum_block_pending: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=PAY h_cov_in=SPLIT h_pr_land=SPLIT PAYS",
    "colon_open_map ← indicator_open_map ← accum_block_on_pendingBlockContent: h_sfx_land=DECLINE h_nodoc_land=DECLINE h_mk_land=DECLINE h_res_land=SPLIT h_ref_land=PAY h_cov_in=SPLIT h_pr_land=DECLINE PAYS",
    "colon_open_map ← indicator_open_map ← accum_block_on_pendingBlockContent ← accum_block_pending: h_sfx_land=DECLINE h_nodoc_land=DECLINE h_mk_land=DECLINE h_res_land=SPLIT h_ref_land=PAY h_cov_in=SPLIT h_pr_land=DECLINE PAYS",
    "colon_open_map: opts=7 paths=14 fallback=0 pays=7 open=7",
    "question_open_map ← indicator_open_map: h_sfx_land=RELAY h_nodoc_land=RELAY h_mk_land=RELAY h_res_land=RELAY h_ref_land=RELAY h_cov_in=SPLIT h_cov_nil=SPLIT h_pr_land=RELAY OPEN",
    "question_open_map ← indicator_open_map ← accum_block_on_noPending: h_sfx_land=DECLINE h_nodoc_land=PAY h_mk_land=DECLINE h_res_land=DECLINE h_ref_land=DECLINE h_cov_in=SPLIT h_cov_nil=SPLIT h_pr_land=DECLINE PAYS",
    "question_open_map ← indicator_open_map ← accum_block_on_pendingBlock: h_sfx_land=DECLINE h_nodoc_land=DECLINE h_mk_land=DECLINE h_res_land=SPLIT h_ref_land=DECLINE h_cov_in=SPLIT h_cov_nil=SPLIT h_pr_land=DECLINE OPEN",
    "question_open_map ← indicator_open_map ← accum_block_on_pendingBlock ← accum_block_pending: h_sfx_land=DECLINE h_nodoc_land=DECLINE h_mk_land=DECLINE h_res_land=SPLIT h_ref_land=DECLINE h_cov_in=SPLIT h_cov_nil=SPLIT h_pr_land=DECLINE OPEN",
    "question_open_map ← indicator_open_map ← accum_block_on_closeThenBlock: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=RELAY h_cov_in=SPLIT h_cov_nil=SPLIT h_pr_land=SPLIT OPEN",
    "question_open_map ← indicator_open_map ← accum_block_on_closeThenBlock ← accum_block_on_pendingContent: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=PAY h_cov_in=SPLIT h_cov_nil=SPLIT h_pr_land=SPLIT PAYS",
    "question_open_map ← indicator_open_map ← accum_block_on_closeThenBlock ← accum_block_on_pendingContent ← accum_block_pending: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=PAY h_cov_in=SPLIT h_cov_nil=SPLIT h_pr_land=SPLIT PAYS",
    "question_open_map ← indicator_open_map ← accum_block_on_closeThenBlock ← accum_block_pending: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=DECLINE h_cov_in=SPLIT h_cov_nil=SPLIT h_pr_land=SPLIT OPEN",
    "question_open_map ← indicator_open_map ← accum_block_on_closeThenBlock ← accum_block_on_pendingBlock: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=DECLINE h_cov_in=SPLIT h_cov_nil=SPLIT h_pr_land=SPLIT OPEN",
    "question_open_map ← indicator_open_map ← accum_block_on_closeThenBlock ← accum_block_on_pendingBlock ← accum_block_pending: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=DECLINE h_cov_in=SPLIT h_cov_nil=SPLIT h_pr_land=SPLIT OPEN",
    "question_open_map ← indicator_open_map ← accum_block_on_closeThenBlock ← accum_block_on_pendingBlockContent: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=PAY h_cov_in=SPLIT h_cov_nil=SPLIT h_pr_land=SPLIT PAYS",
    "question_open_map ← indicator_open_map ← accum_block_on_closeThenBlock ← accum_block_on_pendingBlockContent ← accum_block_pending: h_sfx_land=SPLIT h_nodoc_land=DECLINE h_mk_land=SPLIT h_res_land=SPLIT h_ref_land=PAY h_cov_in=SPLIT h_cov_nil=SPLIT h_pr_land=SPLIT PAYS",
    "question_open_map ← indicator_open_map ← accum_block_on_pendingBlockContent: h_sfx_land=DECLINE h_nodoc_land=DECLINE h_mk_land=DECLINE h_res_land=SPLIT h_ref_land=PAY h_cov_in=SPLIT h_cov_nil=SPLIT h_pr_land=DECLINE PAYS",
    "question_open_map ← indicator_open_map ← accum_block_on_pendingBlockContent ← accum_block_pending: h_sfx_land=DECLINE h_nodoc_land=DECLINE h_mk_land=DECLINE h_res_land=SPLIT h_ref_land=PAY h_cov_in=SPLIT h_cov_nil=SPLIT h_pr_land=DECLINE PAYS",
    "question_open_map: opts=8 paths=14 fallback=0 pays=7 open=7",
    "flowKeyRoute_of_root ← accum_flow_open_depth0: h_col=DECLINE h_sfx=LOCAL h_nodoc=DECLINE h_tail143=LOCAL h_mapF=LOCAL OPEN",
    "flowKeyRoute_of_root: opts=5 paths=1 fallback=0 pays=0 open=1",
    "accum_flow_open_depth0: opts=0 paths=0 fallback=0 pays=0 open=0",
    "accum_block_on_closeThenBlock ← accum_block_on_pendingContent: h_sfx=DECLINE h_mk=DECLINE h_tail139=PAY h_valF=DECLINE h_seqF=RELAY h_mapF=RELAY h_pr=DECLINE h_valFV=DECLINE PAYS",
    "accum_block_on_closeThenBlock ← accum_block_on_pendingContent ← accum_block_pending: h_sfx=DECLINE h_mk=DECLINE h_tail139=PAY h_valF=DECLINE h_seqF=FIELD h_mapF=FIELD h_pr=DECLINE h_valFV=DECLINE PAYS",
    "accum_block_on_closeThenBlock ← accum_block_pending: h_sfx=DECLINE h_mk=DECLINE h_tail139=DECLINE h_valF=DECLINE h_seqF=DECLINE h_mapF=DECLINE h_pr=SPLIT h_valFV=DECLINE OPEN",
    "accum_block_on_closeThenBlock ← accum_block_on_pendingBlock: h_sfx=DECLINE h_mk=DECLINE h_tail139=DECLINE h_valF=DECLINE h_seqF=RELAY h_mapF=DECLINE h_pr=DECLINE h_valFV=SPLIT OPEN",
    "accum_block_on_closeThenBlock ← accum_block_on_pendingBlock ← accum_block_pending: h_sfx=DECLINE h_mk=DECLINE h_tail139=DECLINE h_valF=DECLINE h_seqF=FIELD h_mapF=DECLINE h_pr=DECLINE h_valFV=SPLIT OPEN",
    "accum_block_on_closeThenBlock ← accum_block_on_pendingBlockContent: h_sfx=DECLINE h_mk=DECLINE h_tail139=PAY h_valF=DECLINE h_seqF=RELAY h_mapF=DECLINE h_pr=DECLINE h_valFV=DECLINE PAYS",
    "accum_block_on_closeThenBlock ← accum_block_on_pendingBlockContent ← accum_block_pending: h_sfx=DECLINE h_mk=DECLINE h_tail139=PAY h_valF=DECLINE h_seqF=FIELD h_mapF=DECLINE h_pr=DECLINE h_valFV=DECLINE PAYS",
    "accum_block_on_closeThenBlock: opts=8 paths=7 fallback=0 pays=4 open=3" ]

run_cmd do
  let mut rows : Array String := #[]
  let mut fb := 0
  let mut rt := 0
  let mut op := 0
  for n in openers do
    let (rs, (f, r, o)) ← rowsFor n
    rows := rows ++ rs
    fb := fb + f; rt := rt + r; op := op + o
  let got := s!"openers={openers.length} fallback={fb} pays={rt} open={op}"
  logInfo s!"rows:\n{"\n".intercalate rows.toList}"
  if got != expectedSummary || rows.toList != expectedRows then
    throwError "OpenerFallbackReach moved.\nexpected: {expectedSummary}\ngot:      {got}\nPaste-ready rows:\n{
      "\n".intercalate (rows.toList.map (fun r => s!"   \"{r}\","))}"


/-! ## The two splitting builders' `h_res_land` (item 380, PR #146 review follow-up)

`accum_block_on_pendingBlock` / `accum_block_on_pendingBlockContent` hand the opener (through
`indicator_open_map`) an `h_res_land` built by a CASE SPLIT, and WHICH arm a proof takes is a
term-level fact (§7): Priority 48's walk reads the LANDING (no pop, own level), not the arm.
This pin reads the arms off the proof terms, with the edge walker, per builder: every leaf of
the split, NAMED BY ITS PATH through the nested splitters (`Edge.leafPath`, `<splitter>#<arm>`
per hop) with its kind and source.  The split is `Or.casesOn` on the park's `h_closeF`: arm 1
is the frameless park (`DECLINE`, `closed`); arm 0 opens `dite` on `hmem` — its arm 0 the
resume `Or.inl ⟨ks', …⟩` from the park's `closeF` + `resumeAt` (`PAY`, `free`) and its arm 1
the `Classical.em (s_prep.indents = sc.indents)` read as `Or.elim` (a two-arm split since this
item, `RelaySupplyCensus.isTwoArm`), whose arm 0 is the NO-POP landing — `Or.inr trivial`,
where the accepted root sibling `a: 1⏎b: 2` lands (item 380's re-read) — and whose arm 1
holds item 378's popped landing: the uncovered park and `lo > k` (`DECLINE`), the two `absurd`
refutations of the sequence top (`VIA absurd`), and the live register's `:` (`DECLINE`).  Item
381 pays the no-pop arm from the park's own `closeF` on a non-nil compact tail: exactly the
`…>Or.elim#0` leaf flips `DECLINE` → `PAY` at both builders, and no other leaf moves.  This pin
is the baseline that payment is read against (§10: re-run before spending). -/

def builders : List Name := [`accum_block_on_pendingBlock, `accum_block_on_pendingBlockContent]

/-- Per builder, the ONE edge that supplies `indicator_open_map`'s `h_res_land`: its `how`
(`SPLIT <splitter>`), the split's leaves by kind, and the sources of its leaves (the
constant each arm's witness comes from — the resume arm's `resumeAt`, the declined arms'
`trivial`).  Read off the proof term, never off the scanner. -/
def builderSplitRows : CommandElabM (Array String) := do
  let env ← getEnv
  let callee := ns ++ `indicator_open_map
  let (es, _) ← edges callee
  let mut rows := #[]
  for b in builders do
    let full := ns ++ b
    for e in es do
      if e.caller == full && e.callee == callee && binderName env callee e.idx == `h_res_land then
        let named := (Array.range e.leaves.size).map (fun i =>
          s!"{e.leafPath[i]?.getD "?"}={e.leaves[i]?.getD "?"}:{e.leafSrc[i]?.getD "?"}")
        let summary := " ".intercalate named.qsort.toList
        let row := s!"{b} → h_res_land: {e.how} [{summary}]"
        if rows.contains row then continue
        rows := rows.push row
  return rows

-- 2026-10-28 (item 385): `accum_block_on_pendingBlock`'s `…>dite#1>Or.elim#0` leaf (the no-pop landing) DECLINE:closed → VIA
-- deeperLandingResumeSeq — paid from the park's own `h_closeF` node route, not `PAY` (the helper declines the dedent itself);
-- `accum_block_on_pendingBlockContent`'s stays DECLINE:closed: its `h_closeF_old` is comments-domained (the node is closed, item 381).
-- 2026-10-29 (item 389): the `-` park's k = n arm splits on the stack top's kind — the mapping top is PAY:free (the park's conjunct routes the sibling), the sequence top stays DECLINE; the content twin's match indices move with its new pushed/no-push split.
def expectedBuilderSplit : List String :=
  ["accum_block_on_pendingBlock → h_res_land: SPLIT Or.casesOn [Or.casesOn#0>dite#0=PAY:free Or.casesOn#0>dite#1>Or.elim#0>dite#0=PAY:free Or.casesOn#0>dite#1>Or.elim#0>dite#1>Or.elim#0=VIA absurd: Or.casesOn#0>dite#1>Or.elim#0>dite#1>Or.elim#1>dite#0>Or.casesOn#0=PAY:free Or.casesOn#0>dite#1>Or.elim#0>dite#1>Or.elim#1>dite#0>Or.casesOn#1=DECLINE:free Or.casesOn#0>dite#1>Or.elim#0>dite#1>Or.elim#1>dite#1=DECLINE:closed Or.casesOn#0>dite#1>Or.elim#1>accum_block_on_pendingBlock.match_1_33#0>dite#0>accum_block_on_pendingBlock.match_1_31#0=VIA absurd: Or.casesOn#0>dite#1>Or.elim#1>accum_block_on_pendingBlock.match_1_33#0>dite#0>accum_block_on_pendingBlock.match_1_31#1>Or.elim#0=VIA absurd: Or.casesOn#0>dite#1>Or.elim#1>accum_block_on_pendingBlock.match_1_33#0>dite#0>accum_block_on_pendingBlock.match_1_31#1>Or.elim#1=DECLINE:closed Or.casesOn#0>dite#1>Or.elim#1>accum_block_on_pendingBlock.match_1_33#0>dite#1=DECLINE:closed Or.casesOn#0>dite#1>Or.elim#1>accum_block_on_pendingBlock.match_1_33#1=DECLINE:closed Or.casesOn#1=DECLINE:closed]",
   "accum_block_on_pendingBlockContent → h_res_land: SPLIT Or.casesOn [Or.casesOn#0>dite#0=PAY:free Or.casesOn#0>dite#1>Or.elim#0=DECLINE:closed Or.casesOn#0>dite#1>Or.elim#1>accum_block_on_pendingBlockContent.match_1_21#0>dite#0>accum_block_on_pendingBlockContent.match_1_19#0=VIA absurd: Or.casesOn#0>dite#1>Or.elim#1>accum_block_on_pendingBlockContent.match_1_21#0>dite#0>accum_block_on_pendingBlockContent.match_1_19#1>Or.elim#0=VIA absurd: Or.casesOn#0>dite#1>Or.elim#1>accum_block_on_pendingBlockContent.match_1_21#0>dite#0>accum_block_on_pendingBlockContent.match_1_19#1>Or.elim#1=DECLINE:closed Or.casesOn#0>dite#1>Or.elim#1>accum_block_on_pendingBlockContent.match_1_21#0>dite#1=DECLINE:closed Or.casesOn#0>dite#1>Or.elim#1>accum_block_on_pendingBlockContent.match_1_21#1=DECLINE:closed Or.casesOn#1=DECLINE:closed]"]

run_cmd do
  let rows ← builderSplitRows
  if rows.toList != expectedBuilderSplit then
    throwError "the builders' h_res_land split moved.\nexpected: {expectedBuilderSplit}\nPaste-ready rows:\n{
      "\n".intercalate (rows.toList.map (fun r => s!"   \"{r}\","))}"

end L4YAML.Tests.Guards.OpenerFallbackReach
