module

public import L4YAML.Scanner.Scanner



public meta import L4YAML.Scanner.Scanner
public meta import L4YAML.Scanner.State
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The dangling park is revocable (DOCS item 141)

Items 139 and 140 left one item named: a `danglingNodePos?` face on
`pendingContent`, spent where `h_closable` is stated, so that the accumulation
can refute `bareNodeRoute` — the reading row 19's 1c deletes — instead of
serving it.  Item 140 gave the mid-stream check its two states, which is what
made the refusal exist for the indented half of the family.  This file is that
face SIZED, and the size is not the finding.

The finding is that **the park's reading is not a fact the park can assert.**  A
completed node parked at an open level's own column reads `some` the instant its
token is appended — and the very next `:` takes it back, because a run still on
its own line may yet become a key.  `a: 1⏎b` and `a: 1⏎b: 2` are the SAME park:
`some 1,0` against a stack of two.  What separates them is the landing, not the
park.

That is measurable, and §3 measures it over the family the campaign cares about
and over ordinary YAML.  The consequence for the face is structural: a
`danglingNodePos?` disjunct on `h_closable` can be REFUTED only where the
landing crossed a break (`scanNextToken_checkDanglingNode` is gated on
`simpleKeyAllowed`) or at end of input (`scanLoop_checkDanglingNode` is not
gated at all).  At a same-line `:` there is no refutation, so the disjunct must
be CARRIED — and §4 measures how often that is: ~~2272 of 2275 dangling parks
observed across 490 real YAML files are a `:` landing with the flag down, 2179
of them at a column other than 0~~ — **332 of 346**, corrected at item 156,
which found §4's corpus walk reading the suite's test DESCRIPTORS rather than
its payloads.  Every sibling key of every nested block mapping is one.

So the face cannot be spent until the block landing stops requiring an
unconditional stream through a park the next `:` turns into a key — which is
`accum_block_on_closeThenBlock` together with `rootMapRoute`/`rootMapRouteF`,
three of the six sites the constructor flip already reports.  Item 139 listed
that family as a PEER of the dangling window.  It is its PREREQUISITE.

§1 is the face's would-be domain — the live family, and how each member dies.
§2 is the contradiction the face would spend, at both of its homes, with the
gating asymmetry that decides where it can be spent.  §3 is revocability.  §4 is
the census.  §5 is the block lane's two witnesses.  §6 is what this reorders. -/

namespace L4YAML.Tests.Guards.StreamDanglingParkRevocable

open L4YAML L4YAML.Scanner

private def posStr : Option YamlPos → String
  | some p => s!"{p.line},{p.col}"
  | none => "none"

private def stepN (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | n + 1 =>
    match scanNextToken s with
    | .ok (some s') => stepN s' n
    | _ => none

/-- The PARK's own reading: `danglingNodePos?` at the state a landing's dispatch
    leaves behind, against the stack it is read with.  This is the state
    `pendingContent` carries as `sc`, so this is exactly what a face on the park
    could assert. -/
private def parkAt (input : String) (n : Nat) : String :=
  match stepN ((ScannerState.mk' input).emit .streamStart) n with
  | none => "no-state"
  | some s => s!"{posStr (danglingNodePos? s)} ind={s.indents.size}"

/-- What the NEXT landing does with that park: refuse it, end the stream on it,
    or dispatch a character — with the break flag the mid-stream check is gated
    on. -/
private def landAt (input : String) (n : Nat) : String :=
  match stepN ((ScannerState.mk' input).emit .streamStart) n with
  | none => "no-state"
  | some s =>
    match scanNextToken s with
    | .error e => s!"REFUSED {repr e}"
    | .ok none => "EOF"
    | .ok (some _) =>
      match scanNextToken_preprocess s with
      | .ok (some (s1, c)) => s!"c={repr c} ska={s1.simpleKeyAllowed}"
      | _ => "no-landing"

/-! ## §1  The face's would-be domain

The family item 139 left open, at the park the landing MAKES.  Every member
reads `some` against a stack of at least two — which is the half
`bareDocument_refutes_landing` cannot reach, because `scanNextToken_checkBareDocument`
stands aside above size 1 — and every member dies, but at two different places. -/

-- The four that die at END OF INPUT.  `scanLoop_checkDanglingNode` is the
-- refusal, and it is not gated on anything.
#guard (parkAt "a: 1\nb" 4, landAt "a: 1\nb" 4) == ("1,0 ind=2", "EOF")
#guard (parkAt "- a\nb" 3, landAt "- a\nb" 3) == ("1,0 ind=2", "EOF")
#guard (parkAt "k:\n  a\n# c\nb" 4, landAt "k:\n  a\n# c\nb" 4) == ("3,0 ind=2", "EOF")
#guard (parkAt "k:\n  a\nb" 4, landAt "k:\n  a\nb" 4) == ("2,0 ind=2", "EOF")

-- The two that die MID-STREAM, at the next landing.  The second is item 140's:
-- before that item the landing's unwind hid the run and this input scanned clean.
#guard (parkAt "a: 1\nb\nc: 2\n" 4, landAt "a: 1\nb\nc: 2\n" 4)
  == ("1,0 ind=2", "REFUSED L4YAML.ScanError.invalidBareDocument 1 0")
#guard (parkAt "k:\n  a: 1\n  b\nc: 2\n" 6, landAt "k:\n  a: 1\n  b\nc: 2\n" 6)
  == ("2,2 ind=3", "REFUSED L4YAML.ScanError.invalidBareDocument 2 2")

/-! ## §2  The contradiction, and the asymmetry that places it

Both refusals are one rewrite away from `False` once the park's reading is in
hand.  What differs is the premise: the mid-stream check is gated on the
LANDING's `simpleKeyAllowed`, and the end-of-input check is gated on nothing.
That asymmetry is the whole reason §4's census decides the shape — it says
exactly where a disjunct can be discharged. -/

/-- §9.2's mid-stream refusal, spent as a contradiction — the twin of item 139's
    `bareDocument_refutes_landing` at the other half of the discriminator.  The
    run is read off `s_run` (item 140) and the break off `s_land`, so the two
    states are the landing's own two. -/
lemma danglingNode_refutes_landing {s_run s_land : ScannerState}
    (h_dn : scanNextToken_checkDanglingNode s_run s_land = .ok ())
    (h_ska : s_land.simpleKeyAllowed = true)
    {p : YamlPos} (h_some : danglingNodePos? s_run = some p) : False := by
  unfold scanNextToken_checkDanglingNode at h_dn
  rw [ite_eq_left h_ska, h_some] at h_dn
  cases h_dn

/-- The same contradiction at end of input, and it needs NO flag: `scanLoop`
    reads the array the run is still in and refuses unconditionally.  This is
    why §1's four EOF members are the half a face could actually discharge. -/
lemma danglingNode_refutes_eof {s : ScannerState}
    (h_dn : scanLoop_checkDanglingNode s = .ok ())
    {p : YamlPos} (h_some : danglingNodePos? s = some p) : False := by
  unfold scanLoop_checkDanglingNode at h_dn
  rw [h_some] at h_dn
  cases h_dn

-- The gating, at its type: with the flag DOWN the mid-stream check succeeds on
-- a state whose reading is `some`, so there is nothing to spend there.
example (s_run s_land : ScannerState) (h : s_land.simpleKeyAllowed = false) :
    scanNextToken_checkDanglingNode s_run s_land = .ok () := by
  unfold scanNextToken_checkDanglingNode
  rw [ite_eq_right (by simp [h])]

/-! ## §3  Revocability — the measurement that decides the shape

The park cannot tell `a: 1⏎b` from `a: 1⏎b: 2`.  Both make the same park, with
the same reading against the same stack; one landing later the second has been
taken back, because the `:` resolved the run into a key.  A face stated on the
park would therefore be asserting something that the next token can falsify,
which is why it has to be a DISJUNCT and not a field. -/

-- The pair that cannot be told apart at the park.  Compare with §1's first row:
-- `parkAt "a: 1\nb" 4` is the same string.
#guard parkAt "a: 1\nb: 2\n" 4 == "1,0 ind=2"
#guard landAt "a: 1\nb: 2\n" 4 == "c=':' ska=false"
#guard parkAt "a: 1\nb: 2\n" 5 == "none ind=2"

-- And at a column other than 0 — the ordinary nested mapping, which §4 shows is
-- the bulk of the census.
#guard parkAt "k:\n  a: 1\n  b: 2\n" 6 == "2,2 ind=3"
#guard landAt "k:\n  a: 1\n  b: 2\n" 6 == "c=':' ska=false"
#guard parkAt "k:\n  a: 1\n  b: 2\n" 7 == "none ind=3"

/-! ## §4  The census

`census` walks the real scanner and records one letter per state whose
`danglingNodePos?` reads `some`: `R` refused at that landing, `E` the stream
ended on it, `D` it survived a landing whose flag was DOWN (no refutation
available), `U` it survived with the flag UP (impossible outside a flow — the
check would have fired).

~~Over the 490 `.yaml` files in `yaml-test-suite/src` and `examples/` this
instrument records **2275** observations: **2** `R`, **0** `E`, **2273** `D`,
**0** `U`; of the 2272 `D`s whose landing is a `:`, **2179** sit at a column
other than 0.~~  **Those are DESCRIPTOR numbers** (item 156): the suite's
`src/*.yaml` are test descriptors, each a root sequence of mappings, and
walking them counts their own nested mappings.  Over the 406 payloads
`Tests.SuiteRunner.parseTestFile` extracts, plus `examples/` (payloads
already), the instrument records **346** observations: **8** `R`, **6** `E`,
**332** `D`, **0** `U`.  The split that decides this file's shape is the same
one — the carried `D`s are 96 % of it — but the discharge-able half is 14
rather than 2, and six of those are end-of-input, which a descriptor file can
never produce.  That corpus walk is not reproduced here — a guard that reads
files is invisible to Lake — but the same instrument over the fixed list below
shows the same split, and DOCS items 141 and 156 record the corpus numbers.
[Re-run at item 145, which widened §9.2's landing refusal to the landing's own
column, the corpus numbers are unchanged in every cell; what moved is one row
of the fixed list, noted where it sits.] -/

private def censusFrom (s : ScannerState) (acc : String) : Nat → String
  | 0 => acc ++ "!"
  | n + 1 =>
    let here :=
      match danglingNodePos? s with
      | none => ""
      | some _ =>
        match scanNextToken s with
        | .error _ => "R"
        | .ok none => "E"
        | .ok (some _) =>
          match scanNextToken_preprocess s with
          | .ok (some (s1, _)) => if s1.simpleKeyAllowed then "U" else "D"
          | _ => "?"
    match scanNextToken s with
    | .ok (some s') => censusFrom s' (acc ++ here) n
    | _ => acc ++ here

private def census (input : String) : String :=
  censusFrom ((ScannerState.mk' input).emit .streamStart) "" 64

-- The family the face was for: four end the stream, two are refused mid-stream.
-- Not one of them survives a landing, which is what makes them discharge-able.
#guard ["a: 1\nb", "- a\nb", "k:\n  a\n# c\nb", "k:\n  a\nb",
        "a: 1\nb\nc: 2\n", "k:\n  a: 1\n  b\nc: 2\n"].map census
  == ["E", "E", "E", "E", "R", "R"]

-- Ordinary YAML: four of these nine carry a dangling park that SURVIVES with the
-- flag down, and five never make one at all.  The survivors are the disjunct's
-- real cost.  [Item 145 moved the eighth row from `D` to none — `k: [1, 2]⏎␣␣b`
-- lands at column 2 with only levels -1 and 0 open, so §9.2 refuses it at `1,2`
-- before the run it would park exists.  The CORPUS census above is unmoved:
-- re-run at item 145 over the same 490 files it is still 2275 / 2 R / 0 E /
-- 2273 D / 0 U, with 2179 of the colon landings off column 0.]
#guard ["a: 1\nb: 2\n", "- a\n- b\n", "a: 1\n...\nb", "a: 1\n---\nb",
        "k:\n  a: 1\n  b: 2\n", "a: &x 1\n*x : 2\n", "a: 1\n\"b\" : 2\n",
        "k: [1, 2]\n  b\nc: 2\n", "a\n# c\nb"].map census
  == ["D", "", "", "", "D", "D", "D", "", ""]

-- The two markers close the level, so the same text makes no park at all: that
-- is item 139's sentinel half, where `checkBareDocument` is the refusal instead.
#guard census "a: 1\n...\nb" == ""
#guard census "a: 1\n---\nb" == ""

/-! ## §5  The block lane's witnesses

`accum_block_pending` builds its `h_close_pending` BEFORE the case split, so a
disjunct on `h_closable` reaches it whatever the park is — and the landing there
may be a `:` on the park's own line, where §2's gating leaves nothing to
discharge with.  The two inputs below are that case, and both scan clean, so the
carry is not a corner of the language: it is the language.

The first is the ordinary one — a sibling key one level in.  The second is a
punting one: `pendingContent`'s `h_key` hands `ImplicitKeyPack` for plain and
quoted heads and punts on alias content, and an alias key is where the punt
meets a dangling park. -/

private def lastTok (input : String) (n : Nat) : String :=
  match stepN ((ScannerState.mk' input).emit .streamStart) n with
  | none => "no-state"
  | some s =>
    match lastRealTokenVal? s.tokens with
    | none => "none"
    | some t => s!"{repr t}"

private def scanOk (input : String) : String :=
  match scan input with
  | .ok _ => "SCAN-OK"
  | .error e => s!"SCAN-ERR {repr e}"

-- The ordinary witness: a nested mapping's second key.
#guard scanOk "k:\n  a: 1\n  b: 2\n" == "SCAN-OK"
#guard (parkAt "k:\n  a: 1\n  b: 2\n" 6, landAt "k:\n  a: 1\n  b: 2\n" 6)
  == ("2,2 ind=3", "c=':' ska=false")

-- The punting witness: an ALIAS key, which `h_key` does not pack.
#guard scanOk "a: &x 1\n*x : 2\n" == "SCAN-OK"
#guard (parkAt "a: &x 1\n*x : 2\n" 5, landAt "a: &x 1\n*x : 2\n" 5)
  == ("1,0 ind=2", "c=':' ska=false")
#guard lastTok "a: &x 1\n*x : 2\n" 5 == "L4YAML.YamlToken.alias \"x\""

-- …and the PACKED control beside it, so the punt is shown to be the punt and not
-- the shape: a double-quoted head is a key `h_key` does pack.
#guard lastTok "a: 1\n\"b\" : 2\n" 4
  == "L4YAML.YamlToken.scalar \"b\" (L4YAML.ScalarStyle.doubleQuoted)"

/-! ## §6  What this reorders

The two lemmas in §2 are the contradiction the face will spend when it is
spendable, and nothing spends them yet — the same standing `nodocMapRoute` has
had since item 116, and for the same reason: the route they refute is not the
one the accumulation takes until its landing is narrowed.  [Item 156 supplied
the `some` reading they take as a premise — `danglingPark_of_dispatch` and its
two spent forms, in `StreamAccum` — and item 157 BUILT the face, as a premise
on `h_closable` and on `PendingNode.close_with_ssl`.  The two lemmas below are
still unspent, and now for a sharper reason: the face's own refutation
(`danglingPark_refutes_route`) is taken at the PRODUCER, where the park is made,
rather than at the landing that closes it.  See `DanglingParkFace`.]

What has to come first is the BLOCK landing.  The disjunct has no home at a
same-line `:` (§2's gating, §4's 2272), and that landing's own route is already
flagged: `rootMapRoute`, `rootMapRouteF` and `accum_block_on_closeThenBlock` are
three of the six errors the `[210]` constructor flip reports, and they are
`bareNodeRoute`'s KEY-side siblings — the reading the same landings take when
the completed node turns out to be a key rather than a node.  Item 139 listed
that family beside the dangling window.  It is underneath it.

Measured cost of the face itself, by the campaign's own method (state it, build,
read back the distinct sites Lean reports): **19** sites for the disjunct on
`h_closable` plus `PendingNode.close_with_ssl`'s conclusion — 14 producers and
5 consumers — then **28** once `accum_block_pending`'s pre-split `have` carries
it, then **32** once the four `accum_block_on_*` signatures do.  The waves
converge; ~~what does not converge is the fifth consumer, because §5's witnesses
have no refutation to be discharged by.~~

**Item 157: the fifth consumer converges too, and the shape is why.**  Stated as
a PREMISE (item 156's shape) rather than as a disjunct on the conclusion, the
face rides inside `h_close_pending`'s own type — so the `have` before
`accum_block_pending`'s case split costs nothing, and the premise is discharged
where the close is SPENT.  `accum_block_on_closeThenBlock` spends it in exactly
one place, the branch where preprocessing produced a landing, and there
`landing_or_park_ska` supplies the flag.  §5's two witnesses take the no-break
arm, which spends `h_stream_fallback` — a different parameter — and never reach
the park's close at all. -/

end L4YAML.Tests.Guards.StreamDanglingParkRevocable

end Blanket
