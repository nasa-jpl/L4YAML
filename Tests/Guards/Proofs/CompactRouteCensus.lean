module

public import L4YAML.Scanner.Scanner



public meta import L4YAML.Scanner.Scanner
public meta import L4YAML.Scanner.State
@[expose] public section Blanket

/-!
# The COMPACT route's emptiness, re-measured at the runtime (item 204)

> **ITEM 209: the route is GONE.**  `block_dispatch_deferred_stamp_compact` is
> deleted and both of its sites are `compact_deferral_refuted … |>.elim`.  What
> this module measured is therefore no longer a property of a live escape
> class; it is the corpus evidence that stood behind the refutation while the
> refutation was unspendable, and it stays as that.  The proof's own runtime
> reading is `BlockDeferralClasses` §28.3, which measures the STRICT floor at
> the preprocessed state — the fact `[197]`'s equation needs and never gets.

`block_dispatch_deferred_stamp_compact`'s two sites are reached by a `:` whose
dispatch state has the stamp source UNDECIDED — the explicit-key register live,
the cleared key not surviving, and the `:` standing at `explicitKeyCol` — and
whose step satisfies `InlineResidue`: the park is off column 0 and the step
crossed NO break.

Item 185 measured that family empty with a SYNTACTIC proxy (a sweep of 35 937
three-line programs, counting programs that "carry a compact `:`").  The
sentence "2 sites, measured empty" then rode nineteen consecutive items, and
the sweep that produced it was not re-derivable — §10's own failure mode
("a number no instrument can re-derive is a guess"), at three times the length
of the record case item 166 set.

This module re-derives it, and reads the wrapper's OWN premise off the scanner
state instead of guessing it from the text.  The domain is the same shape as
item 185's: a 33-fragment line alphabet, three lines, 35 937 programs.

**The measurement (first reading, item 204).**  244 programs reached the
premise; ZERO of those were accepted; and all 244 were refused by ONE error —
§8.2.2 `[197]`'s own `s-indent(n)` test, which is the very equation
`explicit_at_indent_of_dispatch` reads forwards.  The class was empty over this
domain because the scanner refused every input that would enter it.

**Current reading (item 337).**  ZERO programs reach the premise and the
refusal histogram is empty: the stale-key hook (items 333, 335, 337) kills the
explicit-key register when its level closes — on a `-` strictly left of the
`?`'s column since item 337 — so no later-line `:` is dispatched with the
register live.  The zero is now UNREACHABILITY, not refusal, and it is not
vacuous: the mid-line control (`noMidOk`, the same discriminator without the
`InlineResidue` conjunct) still fires 934 times on the same corpus, so the
instrument sees the shapes and the premise is what they no longer satisfy.

**Why the zero is not vacuous, and why the syntactic proxy was not enough.**
Two controls ride with it.  The domain REACHES the premise 244 times, so the
zero is a refusal rather than an empty search.  And dropping the `InlineResidue`
conjunct alone raises the accepted count from 0 to 916 — so the zero is
produced by the MID-LINE requirement and not by a discriminator that never
fires.  A first version of this instrument tested the shape on the program TEXT
(a mid-line `?` at column x, a mid-line `:` at column x on a later line) and
reported 28 accepted hits; every one was a false positive, the register having
been consumed by an intervening column-0 `:`.  The state, not the text, is what
carries the premise.
-/

namespace Tests.Guards.CompactRouteCensus

open L4YAML
open L4YAML.Scanner

/-- The three stamp wrappers' shared premise (`_h_src` negated), evaluated on a
    dispatch state: the register is LIVE, the cleared key does not survive, and
    the `:` stands at the register's own column. -/
def stampSrcUndecided (s : ScannerState) : Bool :=
  !s.inFlow && s.explicitKeyLine != none &&
  (scanValueClearKey s).simpleKey.possible == false &&
  (s.col : Int) == s.explicitKeyCol

/-- One program's verdict: did any `:` dispatch reach the stamp wrappers'
    premise (`hit`), did one reach it with `InlineResidue`'s premise too
    (`hitMid` — the park off column 0 and the step crossing no break), and was
    the whole scan accepted. -/
partial def probe (input : String) : Bool × Bool × Bool :=
  let rec go (s : ScannerState) (fuel : Nat) (hit hitMid : Bool) : Bool × Bool × Bool :=
    match fuel with
    | 0 => (hit, hitMid, false)
    | fuel' + 1 =>
      let (hit', hitMid') :=
        match scanNextToken_preprocess s with
        | .ok (some (s_prep, c)) =>
          let s_dis := if s_prep.allowDirectives then
              { s_prep with allowDirectives := false, documentEverStarted := true }
            else s_prep
          if c == ':' && stampSrcUndecided s_dis then
            (true, hitMid || (s.col != 0 && s_prep.line == s.line))
          else (hit, hitMid)
        | _ => (hit, hitMid)
      match scanNextToken s with
      | .ok (some s') => go s' fuel' hit' hitMid'
      | .ok none =>
        match scanLoop_checkDanglingNode s with
        | .error _ => (hit', hitMid', false)
        | .ok () =>
          match scanLoop_checkFlowValueIndent s with
          | .ok () => (hit', hitMid', true)
          | .error _ => (hit', hitMid', false)
      | .error _ => (hit', hitMid', false)
  go ((ScannerState.mk' input).emit .streamStart) 200 false false

/-- The line alphabet: the three indicators at three depths, their compact
    fills, scalars, flow and a comment. -/
def frags : List String :=
  [ "a: 1", "b: 2", "k:", "- a", "- b", "-",
    "? a", "? b", "?", ": a", ": b", ":",
    "- ? a", "- : a", "- - a", "- ? b", "- : b",
    "  a: 1", "  - a", "  ? a", "  : a", "  ?", "  :",
    "    ? a", "    : a", "    - a",
    "[1]", "{a: b}", "- [1]", "? [1]", ": [1]",
    "#c", "" ]

def programs : List String :=
  frags.flatMap fun a => frags.flatMap fun b => frags.map fun c =>
    a ++ "\n" ++ b ++ "\n" ++ c ++ "\n"

/-- `(total, accepted, reachedPremise, reachedAndAccepted, reachedNoMidAndAccepted)`.
    The last is the CONTROL: the same discriminator without `InlineResidue`'s
    conjunct, which must be far from zero or the zero beside it says nothing. -/
def census : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut total := 0
  let mut accepted := 0
  let mut reached := 0
  let mut reachedOk := 0
  let mut noMidOk := 0
  for p in programs do
    let (hit, hitMid, ok) := probe p
    total := total + 1
    if ok then accepted := accepted + 1
    if hitMid then reached := reached + 1
    if hitMid && ok then reachedOk := reachedOk + 1
    if hit && ok then noMidOk := noMidOk + 1
  return (total, accepted, reached, reachedOk, noMidOk)

/-! **The measurement (first reading).**  35 937 programs, 8 660 accepted; 244
    reach the COMPACT premise and NONE of those is accepted; and the same
    discriminator without the mid-line conjunct is accepted 916 times, which is
    what says the zero belongs to `InlineResidue` and not to a discriminator
    that never fires.  Items 333 and 335 (the stale-key hook, `pendingKeys`)
    moved it to `(35937, 8344, 232, 0, 938)`: every stale-register acceptance
    that reached the premise became a refusal. -/
/-! **Re-read (item 337).**  With the `-` dedent arm of `closeStaleExplicitKey`
    (a `-` strictly left of the pending `?` closes it), no frags³ program reaches
    the COMPACT premise any more (232 → 0): every reach was a stale-register
    `misindentedExplicitValue`.  Those 232 split 170 → accepted (8 344 → 8 514;
    all `… - ? a⏎- : b` programs, i.e. the `- : b` empty-key divergence libyaml
    refuses, recorded at item 333) and the rest → other refusals; `noMidOk`
    938 → 934. -/
#guard census == (35937, 8514, 0, 0, 934)

/-- What refuses a program: the error's constructor name, or `ACCEPTED`. -/
partial def refusal (input : String) : String :=
  let rec go (s : ScannerState) (fuel : Nat) : String :=
    match fuel with
    | 0 => "fuel"
    | fuel' + 1 =>
      match scanNextToken s with
      | .ok (some s') => go s' fuel'
      | .ok none =>
        match scanLoop_checkDanglingNode s with
        | .error e => s!"EOF {repr e}"
        | .ok () =>
          match scanLoop_checkFlowValueIndent s with
          | .ok () => "ACCEPTED"
          | .error e => s!"EOF {repr e}"
      | .error e => ((reprStr e).splitOn " ").headD (reprStr e)
  go ((ScannerState.mk' input).emit .streamStart) 200

/-- The refusals of every program that reaches the premise, as a histogram. -/
def refusalCensus : List (String × Nat) := Id.run do
  let mut m : List (String × Nat) := []
  for p in programs do
    let (_, hitMid, _) := probe p
    if hitMid then
      let k := refusal p
      m := if m.any (fun e => e.1 == k)
           then m.map (fun e => if e.1 == k then (e.1, e.2 + 1) else e)
           else (k, 1) :: m
  return m

/-! **ONE cause — historically; NONE to classify now.**  Through item 335 every
    program that reached the compact premise was refused by §8.2.2 `[197]`'s
    `s-indent(n)` test — the equation `explicit_at_indent_of_dispatch` reads
    forwards out of the same `.ok` path — and that single-cause histogram
    (`[(misindentedExplicitValue, 232)]` at item 335) is what made the emptiness
    a REFUTATION target rather than an accident of the corpus.  Since item 337
    no program reaches the premise at all (`census` above, third number 0), so
    the histogram is empty by construction; the proof and the sweep remain the
    same fact read two ways (`BlockDeferralClasses` §4, §23). -/
#guard refusalCensus == []

end Tests.Guards.CompactRouteCensus

end Blanket
