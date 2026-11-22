module

public import L4YAML.Scanner.Scanner

public meta import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch
public meta import L4YAML.Scanner.IndexedDispatch
public import L4YAML.Proofs.Scanner.FlowAdjacency
public import L4YAML.Proofs.Scanner.FlowAdjacencyIx

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The flow-adjacency check's `:` exemption is conditional (DOCS item 9d)

`scanNextToken_checkFlowAdjacency` rejects a node that follows a completed flow
value with no separator (`[[a][b]]`, `["a""b"]`).  It exempted `,` `:` `]` `}`,
on the reading that those are separators or closers rather than node starts.

That is right for `,` `]` `}` and **wrong for `:`**.  A `:` is a value indicator
only when `isValueCandidate` holds — exactly the guard on the `:` arm of
`scanNextToken_dispatchBlockIndicators`, which runs on the same state one
dispatcher later.  A `:` that fails it falls through to content dispatch and
starts a *plain scalar* (`[126] ns-plain-first` admits `:` followed by
`ns-plain-safe`), so it is a node start like any other.

The gap it left is reachable: a comment terminates the plain scalar `a`, and the
`:b` on the next line then opens a second entry with no `,` between them —

```yaml
[a #c
 :b]
```

— which `[138] ns-s-flow-seq-entries` and `[141] ns-s-flow-map-entries` forbid,
and which PyYAML rejects.  Item 9d narrows the exemption to
`!(c == ':' && isValueCandidate s)` in both pipelines.

**How this was found.** Not from a failing test: from β.3's flow-interior content
step, which needs `tailOf sc.tokens ≠ .value` to apply `FlowOpenStack.receiveNode`
and could not get it for `c = ':'`.  A brute-force sweep of every input of length
≤ 5 over two 15-character alphabets (≈1.6M inputs) produced **zero** hits, and the
counterexample only appeared once the probe alphabet included `#`.  Absence of
hits in a bounded sweep is not vacuity — the shortest witness is 10 characters.
-/

namespace Tests.Guards.ScannerFlowColonAdjacency

open L4YAML
open L4YAML.Scanner

/-- Legacy and indexed verdicts as a comparable pair: `none` on success,
    `some e` on rejection.  Equal pairs mean the two pipelines agree. -/
private def verdicts (input : String) : Option ScanError × Option ScanError :=
  ( (match scan input with | .ok _ => none | .error e => some e)
  , (match Indexed.ScannerStateIx.scanIx input with | .ok _ => none | .error e => some e) )

/-- Both pipelines reject `input` with the same `invalidFlowEntry` position. -/
private def rejects9d (input : String) (line col : Nat) : Bool :=
  verdicts input == (some (.invalidFlowEntry line col), some (.invalidFlowEntry line col))

/-- Both pipelines accept `input`. -/
private def bothAccept (input : String) : Bool := verdicts input == (none, none)

/-- Both pipelines reject `input` — without pinning *which* error.  Used where a
    second, unrelated defect also fires and the two pipelines disagree on which
    one they report first (see §5). -/
private def bothReject (input : String) : Bool :=
  (verdicts input).1.isSome && (verdicts input).2.isSome

/-! ## §1  The shapes item 9d rejects

Position is pinned: the error points at the offending node start, not at the
enclosing collection or at the comment. -/

#guard rejects9d "[a #c\n :b]\n" 1 1          -- the original counterexample
#guard rejects9d "{a #c\n :b}\n" 1 1          -- flow mapping twin
#guard rejects9d "[a #c\n :b, c]\n" 1 1       -- more entries after
#guard rejects9d "[a #c\n:b]\n" 1 0           -- next entry at column 0
#guard rejects9d "[a\n#c\n :b]\n" 2 1         -- comment on its own line
#guard rejects9d "[a #c\n #d\n :b]\n" 2 1     -- two comments
#guard rejects9d "[a, b #c\n :d]\n" 1 1       -- not the first entry
#guard rejects9d "{a: b #c\n :d}\n" 1 1       -- after a mapping value
#guard rejects9d "[a #c\n :b #d\n :e]\n" 1 1  -- first offender reported

/-! ## §2  What the check already rejected, unchanged

The non-`:` node starts were never exempt; item 9d did not touch them. -/

#guard rejects9d "[a #c\n b]\n" 1 1           -- plain scalar after a comment
#guard rejects9d "[[a][b]]\n" 0 4             -- adjacent flow sequences
#guard rejects9d "[\"a\"\"b\"]\n" 0 4         -- adjacent quoted scalars
#guard rejects9d "[[a]b]\n" 0 4               -- collection then scalar

/-! ## §3  Every `:` that IS a value indicator still passes

This is the half the narrowing must not break: `isValueCandidate` covers the
blank-separated form [147], the JSON-key adjacent form [148]/[149], and the
`?`-explicit form. -/

#guard bothAccept "[a: b]\n"
#guard bothAccept "{a: b}\n"
#guard bothAccept "{\"a\": b}\n"      -- JSON key, blank after `:`
#guard bothAccept "{\"a\":b}\n"       -- JSON key, adjacent value [149]
#guard bothAccept "[[a]: b]\n"        -- flow-sequence key
#guard bothAccept "{[a]: b}\n"
#guard bothAccept "[? a : b]\n"       -- explicit key
#guard bothAccept "{? a : b}\n"
#guard bothAccept "[a: b, c: d]\n"
#guard bothAccept "a: {b: c}\n"       -- flow nested in block

/-! ## §4  Plain scalars that merely *contain* or *start with* `:`

A `:` reaching content dispatch is fine wherever the previous token did not
complete a value — that is the legitimate traffic through the arm, and it is
what makes the exemption conditional rather than removable. -/

#guard bothAccept "[:a]\n"            -- `:a` is a plain scalar [126]
#guard bothAccept "{:a}\n"
#guard bothAccept "[a, :b]\n"         -- after a `,`
#guard bothAccept "[a :b]\n"          -- ONE scalar `a :b` — no comment to end it
#guard bothAccept "[a \n :b]\n"       -- multi-line plain scalar, same reason
#guard bothAccept "[a #c\n, b]\n"     -- comment, then a proper `,`
#guard bothAccept "[a #c\n ]\n"       -- comment, then the close
#guard bothAccept "[a #c\n]\n"
#guard bothAccept "{a #c\n}\n"

/-! ## §5  A pre-existing parity gap this probe surfaced

`[*x #c⏎ :b]` is invalid twice over: the alias `*x` is undefined **and** the
`:b` is a separator-less entry.  Both pipelines reject it, but they disagree on
which defect they report, because the indexed scanner has no alias-definedness
check at all — `scanIx "[*x]"` succeeds where `scan "[*x]"` reports
`undefinedAlias`.  That divergence predates item 9d and is unrelated to it; it is
pinned here only so the guard file records what it observed. -/

#guard bothReject "[*x #c\n :b]\n"

/-! ## §6  Flow basics, unchanged -/

#guard bothAccept "[a, b]\n"
#guard bothAccept "{a: 1, b: 2}\n"
#guard bothAccept "[]\n"
#guard bothAccept "[[a, [b, {c: [d]}]]]\n"
#guard bothAccept "- [a, b]\n- c\n"

/-! ## §7  The proof-side handles

`notCompletes_of_checkFlowAdjacency_ok_nodeStart` is the inversion β.3's content
step consumes; `checkFlowAdjacency_ok_of_valueIndicator` is the construction
direction the emit→scan towers discharge at every `: ` the emitter writes.
Pinned by axiom profile rather than by a `sorry`-free warning — a delegated proof
can be sorry-free and still ride `sorryAx` through a dependency. -/

open L4YAML.Proofs.FlowAdjacency in
/-- info: 'L4YAML.Proofs.FlowAdjacency.notCompletes_of_checkFlowAdjacency_ok_nodeStart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms notCompletes_of_checkFlowAdjacency_ok_nodeStart

open L4YAML.Proofs.FlowAdjacency in
/-- info: 'L4YAML.Proofs.FlowAdjacency.checkFlowAdjacency_ok_of_valueIndicator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms checkFlowAdjacency_ok_of_valueIndicator

open L4YAML.Proofs.FlowAdjacencyIx in
/-- info: 'L4YAML.Proofs.FlowAdjacencyIx.notCompletes_of_checkFlowAdjacencyIx_ok_nodeStart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms notCompletes_of_checkFlowAdjacencyIx_ok_nodeStart

end Tests.Guards.ScannerFlowColonAdjacency

end Blanket
