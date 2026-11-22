module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The indent stack's base, carried by the accumulation (DOCS item 146)

Item 145 made §9.2's landing refusal read the landing's own COLUMN, and the
contradiction it supports came out with TWO stack premises: the landing did not
dedent (`h_nopop`), and it stands at no open level (`h_open`).  The first is
redundant — a landing that popped rests AT the column of the entry it popped
down to (`preprocess_landing_at_level`, item 129), so it stands at an open level
by construction and `h_open` refutes it outright.

Saying so needs `ScannerState.WellFormed`'s sixth conjunct, `SentinelBase`: a
stack popped to a single entry is only known to sit below every landing if that
entry is the sentinel at `-1`.  Item 128 threaded the conjunct through every
scanner STEP and seeded it at `mk'`; what was missing was a carrier through the
grammar ACCUMULATION, which is what this item adds.  The premise now rides
`scanLoop_grammar_prod` beside the other seven, is re-established at each step,
and reaches §9.2's refusal as a conjunct of `BareLandingFacts`.

§1 is the carriage — the three joints a rider has.  §2 is the bridge the
carriage pays for.  §3 is the refutation at its new type.  §4 checks the
invariant against the scanner itself rather than only proving it.  §5 is the
measured price and what it leaves for U3. -/

namespace L4YAML.Tests.Guards.AccumIndentBaseCarried

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

/-! ## §1  The carriage

A rider on the accumulation needs three things: a seed, a step, and a binder on
the loop.  Item 128 supplied the first two; this item supplies the third, and
the binder is what makes them reachable from inside a dispatch. -/

/-- The seed: `ScannerState.mk'` builds the stack the conjunct describes. -/
example (input : String) :
    L4YAML.Proofs.IndentStackBase.SentinelBase (ScannerState.mk' input) :=
  L4YAML.Proofs.IndentStackBase.mk'_base input

/-- The step: a push writes past the end of the stack and the unwind's guard
    stops at size 1, so index 0 survives a whole `scanNextToken`. -/
example {s s' : ScannerState} (hok : scanNextToken s = .ok (some s'))
    (h : L4YAML.Proofs.IndentStackBase.SentinelBase s) :
    L4YAML.Proofs.IndentStackBase.SentinelBase s' :=
  L4YAML.Proofs.IndentStackBase.scanNextToken_base hok h

/-- The binder: the loop takes it, and `scan_content_gives_stream_v2` is what
    discharges it — the seed's stack passes through the `streamStart` emission
    and §5.2's BOM untouched. -/
example (input : String) (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) :
    ∃ sp_final : SurfPos, SLYamlStream ⟨input.toList, 0⟩ sp_final ∧
      sp_final.chars = [] :=
  scan_content_gives_stream_v2 input tokens h

/-! ## §2  What the carriage pays for

The bridge is one implication, and it is the whole reason the premise travels:
`¬ open` forces `nopop`, so the dedent exemption §9.2's refusal is stated with
is a CONSEQUENCE of the column reading rather than a second case to split on. -/

/-- The bridge. -/
example {sc s_prep : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc)
    (h_open : (s_prep.indents.any fun e => e.column == (s_prep.col : Int)) = false) :
    s_prep.indents = sc.indents :=
  preprocess_indents_eq_of_no_open_level hok h_base h_open

/-- …and the reading it is built from: a landing that popped rests on an entry
    the incoming stack already held, at that entry's own column. -/
example {sc s_prep : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_pop : s_prep.indents ≠ sc.indents)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc) :
    ∃ e, s_prep.indents.back? = some e ∧ e ∈ sc.indents ∧
      e.column = (s_prep.col : Int) :=
  preprocess_landing_at_level hok h_pop h_base

/-- The step the base is what makes unconditional: a stack popped to one entry
    sits at `-1`, which no landing column reaches. -/
example {s : ScannerState} (h : L4YAML.Proofs.IndentStackBase.SentinelBase s)
    (hsz : s.indents.size ≤ 1) : s.currentIndent = -1 :=
  h.currentIndent_of_size_le_one hsz

/-! ## §3  The refutation, with one stack premise

The transport the contradiction rests on is unchanged — `CompletedTail` is held
on the PARK and read at the LANDING, so preprocessing has to carry the token
tail across — but what buys that transport is now the column reading alone. -/

/-- The contradiction at its type. -/
example {sc s_prep : ScannerState} {c : Char}
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow : s_prep.inFlow = false)
    (h_ska : s_prep.simpleKeyAllowed = true)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc)
    (h_open : (s_prep.indents.any fun e => e.column == (s_prep.col : Int)) = false)
    (h_tail : CompletedTail sc) : False :=
  bareDocument_refutes_landing h_bare h_pre h_noflow h_ska h_base h_open h_tail

/-- The bundle's six conjuncts, assembled as the landing arms assemble them. -/
example {sc s_prep : ScannerState} {c : Char}
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow : s_prep.inFlow = false)
    (h_ska : s_prep.simpleKeyAllowed = true)
    (h_tail : CompletedTail sc)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc) :
    BareLandingFacts sc s_prep c :=
  ⟨h_bare, h_pre, h_noflow, h_ska, h_tail, h_base⟩

/-- …and spent at one premise. -/
example {sc s_prep : ScannerState} {c : Char}
    (h : BareLandingFacts sc s_prep c)
    (h_op : (s_prep.indents.any fun e => e.column == (s_prep.col : Int)) = false) :
    False :=
  h.refutes h_op

/-- The three bundle-carrying routes keep their types: the bundle is where the
    premise went, so a caller with nothing to say still passes `Or.inr trivial`
    and still gets the unguarded route. -/
example {sp_start sp_land sp_key : SurfPos} {k : Nat}
    (hcol0 : sp_land.col = 0)
    (h_stream : SLYamlStream sp_start sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v :=
  rootMapRoute_or_refused (sc := ScannerState.mk' "") (s_prep := ScannerState.mk' "")
    (c := 'x') (Or.inr trivial) hcol0 h_stream h_ind

/-- `bareNodeRoute_or_refused` takes the readings loose rather than bundled, so
    the premise is a binder there. -/
example {sc s_prep : ScannerState} {c : Char} {sp_start sp_anchor : SurfPos}
    (h_stream : SLYamlStream sp_start sp_anchor)
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow : s_prep.inFlow = false)
    (h_ska : s_prep.simpleKeyAllowed = true)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc) :
    ∀ sp_m, SBlockNode 0 .blockIn sp_anchor sp_m → SLYamlStream sp_start sp_m :=
  bareNodeRoute_or_refused h_stream h_bare h_pre h_noflow h_ska h_base (Or.inr trivial)

/-! ## §4  The invariant, checked against the scanner

The conjunct is proved, so the walk below cannot fail — which is the point of
running it: it is the statement that the PROVED invariant and the RUNTIME stack
are the same object, at every state of every input, and it is what would break
first if a future stack writer forgot index 0. -/

private def baseHolds (s : ScannerState) : Bool :=
  match s.indents[0]? with
  | some e => e.column == -1 && !e.isSequence
  | none => false

/-- Walks `scanNextToken` from the seed, counting states seen and states whose
    stack has lost its base. -/
private def walkBase (s : ScannerState) : Nat → Nat × Nat → Nat × Nat
  | 0, acc => acc
  | fuel + 1, (seen, bad) =>
    let acc := (seen + 1, bad + (if baseHolds s then 0 else 1))
    match scanNextToken s with
    | .ok (some s') => walkBase s' fuel acc
    | _ => acc

private def census (inputs : List String) : Nat × Nat :=
  inputs.foldl (fun acc i => walkBase (ScannerState.mk' i) 200 acc) (0, 0)

-- Legal shapes at every depth, the three landing lanes item 145 refuses, the
-- sentinel family, a dedent, a flow interior and two block scalars: 121 states,
-- none of them without the base.
#guard census
  ["a: 1\nb: 2\n", "k:\n  a: 1\n  b: 2\n", "- a\n- b\n", "k:\n  - a\n  - b\n",
   "? \"a\"\n: v\n", "k: [1, 2]\nb: 2\n", "k: |\n  x\nb: 2\n", "k:\n  a: 1\nb: 2\n",
   "k:\n  \"x\"\n  b: 2\n", "k:\n  \"a\"\n  [1, 2]\n", "k:\n  a\n  : v\n",
   "\"x\"\nb: 2\n", "a\n# c\nb: 2\n", "[1, 2]\nb: 2\n",
   "a:\n  b:\n    c: 1\nd: 2\n", "{a: 1, b: [2, 3]}\n", "k: >\n  folded\n",
   "---\na: 1\n...\n---\nb: 2\n"] == (121, 0)

-- The stack the seed builds, read directly.
#guard baseHolds (ScannerState.mk' "a: 1\n") == true

/-! ## §5  The price, and what it leaves

Measured after the fact rather than before: the premise is held by **16**
declarations — `bareDocument_refutes_landing`, `bareNodeRoute_or_refused`, the
bridge, and the thirteen accumulation lemmas between `scanLoop_grammar_prod` and
the four landing faces — and passed at **35** places in `StreamAccum` plus
**9** in this guard tree.  Item 145 priced it at 12 declarations and 59 sites
from a static caller closure; the closure over-counted the sites (the premise
went into `BareLandingFacts`, so the five `h_ref` pass-through lemmas never see
it) and under-counted the holders.

`SLYamlStream.implicitContinue` is unmoved at FIVE `[210]` flip errors, at
`topLevelFlowResumeSep`, `rootMapRoute`, `rootMapRouteF`, `bareNodeRoute` and
`structural_dispatch_to_pending`; the raw-route census is unmoved at ~~TWO
holders~~ two `bareNodeRoute` holders.  Neither could move: this item pays a
premise, it removes no construction site.

> **Corrected by item 167** (2026-09-14).  The census instrument counts all
> four raw routes and prints THREE holders — `bareNodeRoute` at
> `bareNodeRoute_or_refused_content` (2 applications) and
> `content_dispatch_after_close` (1), and `rootMapRoute` at
> `flowKeyRoute_of_root` (1).  The third has stood since item 56, so "TWO"
> here and in the log after it is the `bareNodeRoute` half alone, not the
> census's own total.  Item 167 leaves all three declarations byte-identical
> and moves neither figure.

What it leaves is two premise paths that asked for the same conjunct, each
measured against the carriage rather than against nothing:

* **U3's own spend.**  `preprocess_landing_mem_or_seq` reads the landing at
  `entryKeyPack_of_dispatch`'s dedent branch and wants the base beside item
  130's floored cover.  The base's residue there is **5** declarations —
  `entryKeyPack_of_dispatch` and the four `accum_content_on_*` lemmas between it
  and `accum_content_pending` — and **10** call sites.
* **Item 130's premise path.**  It measured `Mono` and `SentinelBase` reaching
  the four `:`/`?` producers at 2 sites, then 4, then 25.  The 25-site level is
  `accum_block_pending` and its neighbours, which carry the base now, so the
  base's residue is **8** declarations and **12** call sites — `indicator_open_map`,
  the four producers, and the three lemmas around them. -/

end L4YAML.Tests.Guards.AccumIndentBaseCarried

end Blanket
