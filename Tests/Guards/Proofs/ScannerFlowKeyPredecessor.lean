module

public import L4YAML.Scanner.Scanner

public meta import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch

public meta import L4YAML.Scanner.IndexedDispatch
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # A flow `?` opens an entry (DOCS item 9g)

`[150] ns-flow-pair(n,c)` is `"?" s-separate ns-flow-map-explicit-entry(n,c)`,
and an `ns-flow-pair` is an *entry* of `[138] ns-s-flow-seq-entries` /
`[141] ns-s-flow-map-entries`.  So inside a flow collection a `?` may stand only
where the collection is about to read a fresh entry: directly after its own
`[`/`{`, or directly after a `,`.

The scanner enforced nothing, and `[? ? a]`, `[: ?]`, `[&a ? b]` and `[!t ?]`
all scanned clean in both pipelines.  §1 pins the rejections.

**Why the error is `unexpectedChar` and not a bespoke one.**  The test rides on
the `?` arm's dispatch condition rather than sitting in an `if … then throw` of
its own, so a `?` that fails it falls through to
`scanNextToken_dispatchContent`.  That is not a loss of precision: every
character `isKeyCandidate` admits after the `?` is a blank or a flow indicator,
and neither is `ns-plain-safe`, so `canStartPlainScalarBool` is false for all of
them and the fall-through is always the error.  §2 pins the two shapes that
distinguish this from a blanket ban on `?`.

**Why this one is gated on `s.inFlow`** (unlike item 9f, which is not).  It is a
lookback, and in block context a `key` token may legitimately follow a `value`
or an `anchor` — `a:⏎? b⏎: c` and `&a⏎? b⏎: c` are both valid, and both put one
directly after the other in the stream.  Separating those needs the indent
machinery (Reflection 615).  §4 pins them.
-/

namespace Tests.Guards.ScannerFlowKeyPredecessor

open L4YAML
open L4YAML.Scanner

/-- Legacy and indexed verdicts as a comparable pair: `none` on success,
    `some e` on rejection.  Equal pairs mean the two pipelines agree. -/
private def verdicts (input : String) : Option ScanError × Option ScanError :=
  ( (match scan input with | .ok _ => none | .error e => some e)
  , (match Indexed.ScannerStateIx.scanIx input with | .ok _ => none | .error e => some e) )

/-- Both pipelines reject `input` at the `?`, with the same position. -/
private def rejects9g (input : String) (line col : Nat) : Bool :=
  verdicts input == (some (.unexpectedChar '?' line col),
                     some (.unexpectedChar '?' line col))

/-- Both pipelines accept `input`. -/
private def bothAccept (input : String) : Bool := verdicts input == (none, none)

/-! ## §1  A `?` that does not open an entry

The three predecessors that reach this test are the ones that neither bound an
entry nor complete a value: `key`, `value`, and a node property.  (A predecessor
that *does* complete a value — `scalar`, `alias`, `]`, `}` — is rejected one
dispatcher earlier by `scanNextToken_checkFlowAdjacency`, item 9b.) -/

#guard rejects9g "[? ? a]\n" 0 3                  -- after `key`
#guard rejects9g "[? ?]\n" 0 3
#guard rejects9g "{? ? a}\n" 0 3
#guard rejects9g "[: ?]\n" 0 3                    -- after `value` (empty-key entry)
#guard rejects9g "[a: ? b]\n" 0 4
#guard rejects9g "{a: ? b}\n" 0 4
#guard rejects9g "[&a ? b]\n" 0 4                 -- after a node property
#guard rejects9g "[!t ?]\n" 0 4
#guard rejects9g "[&a !t ? b]\n" 0 7
#guard rejects9g "[a, ? b, ? ? c]\n" 0 11         -- nested in a longer entry list

/-! ## §2  What must stay accepted

Two shapes distinguish this from a blanket ban on `?` in flow: a `?` that is not
a key indicator at all (it starts a plain scalar, or sits inside one), and a `?`
that *does* open an entry. -/

#guard bothAccept "[a ? b]\n"                     -- ONE plain scalar `a ? b`
#guard bothAccept "[??]\n"                        -- ONE plain scalar `??`
#guard bothAccept "[? ?x]\n"                      -- key is the plain scalar `?x`
#guard bothAccept "[? a]\n"                       -- after `[`
#guard bothAccept "{? a}\n"                       -- after `{`
#guard bothAccept "[a, ? b]\n"                    -- after `,`
#guard bothAccept "{a: b, ? c: d}\n"
#guard bothAccept "[? , ? , a]\n"                 -- empty pairs, each after `,`
#guard bothAccept "[? :]\n"                       -- empty key, empty value
#guard bothAccept "[? ,]\n"
-- (`[?]`, `[?,a]` — the same shapes with the `s-separate` missing — are item
--  9j's, in `ScannerFlowKeyFollower`.)
#guard bothAccept "[? &x]\n"                      -- key is `&x` + e-scalar
#guard bothAccept "[? !t]\n"
#guard bothAccept "[? [b]]\n"
#guard bothAccept "[? {b: c}]\n"
#guard bothAccept "[? \"q\" : a]\n"
#guard bothAccept "[? #z\n a]\n"                  -- separation across a comment
#guard bothAccept "[? a #z\n , b]\n"

/-! ## §3  The `,` really is what re-opens the entry

Each rejected input below differs from the accepted one beside it by a single
`,`, and that character is the whole rule.

`[? a ? b]` is *not* one of these pairs, and §2's `[a ? b]` says why: `a ? b`
is one plain scalar, so its `?` never reaches the dispatch at all.  It is pinned
here as accepted next to the pair it is easily mistaken for. -/

#guard rejects9g "[&a ? b]\n" 0 4
#guard bothAccept "[&a, ? b]\n"
#guard rejects9g "[a: ? b]\n" 0 4
#guard bothAccept "[a:, ? b]\n"
#guard rejects9g "[? ? a]\n" 0 3
#guard bothAccept "[? , ? a]\n"                   -- (the space is item 9j's rule)
#guard bothAccept "[? a ? b]\n"                   -- the key is the scalar `a ? b`

/-! ## §4  Block context is untouched

Each of these puts a `key` token directly after a `value` or an `anchor` in the
stream, and each is valid — which is why the test carries the `s.inFlow` gate. -/

#guard bothAccept "? a\n: b\n"
#guard bothAccept "a: 1\n? b\n: c\n"              -- `key` directly after `value`
#guard bothAccept "&a\n? b\n: c\n"                -- `key` directly after `anchor`
#guard bothAccept "!t\n? b\n: c\n"                -- …and after a `tag`
#guard bothAccept "? a\n? b\n"
#guard bothAccept "? [a, b]\n: c\n"               -- a flow collection as the key
#guard bothAccept "? a\n: ? b\n"
#guard bothAccept "---\n&mapping\n&key [ &item a, b, c ]: value\n"
#guard bothAccept "k: &alias1 v\ntop3: &node3 \n  *alias1 : scalar3\n"

end Tests.Guards.ScannerFlowKeyPredecessor

end Blanket
