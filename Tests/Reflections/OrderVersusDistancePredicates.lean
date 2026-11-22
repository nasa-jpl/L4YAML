/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-! # Reflection 616 — order predicates look back, distance predicates cannot

A scanner accumulates a **token stream**, and a strictening is usually written as
a *lookback* over it: "token `B` may not follow token `A`".  That works because
the stream records what each token IS and where it STARTS.

It stops working the moment the rule is about the **text between** two tokens.
"`A` and `B` must be separated" is not a statement about their order — it is a
statement about `A`'s **extent**, and the extent is exactly what the emitted
stream does not keep.  §2 proves that: two runs whose emitted streams are
*identical*, down to the recorded positions, differ on whether the two tokens
abut.  No lookback over the stream can decide it, however far back it reads.

The extent does exist — but only inside the dispatch that produced `A`, before
the token was emitted.  So a distance rule has exactly one place it can live:
**forward, at the producing dispatch**, on the character its own walk stopped on.
That is also why such a guard needs no context gate the way an adjacency guard
does (Reflection 615): nothing token-less can slip between a token and the
character it stopped before.

## The second half: sibling classes decide what is even reachable (§3)

Two sibling productions that differ only in their name's **character class** do
not fail on the same inputs.  `[102] ns-anchor-char` is `ns-char` minus the flow
indicators, so `&a"x"` is ONE anchor named `a"x"`; `[153] ns-tag-char` also drops
everything outside `ns-uri-char`, so `!t"x"` is a tag and then a *separate*
double-quoted scalar, abutting it.  The reachable-follower sets are the
complements of the two classes, so their difference — the characters one sibling
absorbs and the other stops at — is exactly the region a probe of the first
sibling is *structurally* silent on.

**Probe the class difference, not the surface shape.**  Sequel to Reflection 615:
615 says a probe list inherits the blind spot of the guard it was written for;
616 says it also inherits the character class of whichever sibling it was written
against.

L4YAML DOCS item 9f, 2026-08-07.  `[161] ns-flow-node` reads `c-ns-properties`
then EITHER `s-separate` and content OR nothing (`e-scalar`) — there is no third
arm — yet `[&a[b]]`, `[&a{b: c}]`, `[!t"x"]`, `[!t[b]]` and `[*x[b]]` all scanned
clean in both pipelines.  Items 9b/9e had already put two lookbacks on this
stream (`checkFlowAdjacency`, `trailingPropertyRun`) and neither could have seen
it.  Fixed by a forward test at the `&`/`*`/`!` dispatch, folded into the
existing guard's `if` so the dispatcher gained no `if` at all (Reflection 613) —
and, in consequence, no proof site changed.  See
`Tests/Guards/Proofs/ScannerNodePropertyDelimiter.lean`.
-/

namespace Tests.Reflections.OrderVersusDistancePredicates

/-! ## §1  What a scanner keeps, and what it throws away -/

/-- Token classes, coarsened to the distinction the rule cares about. -/
inductive Kind where
  /-- `&anchor` or `!tag`. -/
  | prop
  /-- A scalar, or a collection opening. -/
  | content
  deriving DecidableEq, Repr

/-- A token as the **producing dispatch** still knows it: class, start, and end.
    `stop` is live for exactly one dispatch and is then discarded. -/
structure Scanned where
  /-- The token's class. -/
  kind : Kind
  /-- Offset of its first character. -/
  start : Nat
  /-- Offset one past its last character — **not** emitted. -/
  stop : Nat
  deriving DecidableEq, Repr

/-- A token as the **stream** keeps it.  This is `Positioned YamlToken`: a value
    and a position, with no extent. -/
structure Emitted where
  /-- The token's class. -/
  kind : Kind
  /-- Offset of its first character. -/
  start : Nat
  deriving DecidableEq, Repr

/-- Emission: the extent is dropped. -/
def project (t : Scanned) : Emitted := ⟨t.kind, t.start⟩

/-! ## §2  The impossibility

`abuts` is the distance rule: some token begins exactly where the previous one
ended, with no text between them.  The two witnesses emit the *same* stream —
same classes, same recorded positions — and disagree on it. -/

/-- The distance rule. -/
def abuts : List Scanned → Bool
  | a :: b :: rest => (a.stop == b.start) || abuts (b :: rest)
  | _ => false

/-- `&ab` immediately followed by `[`: a three-character property, then content
    at offset 3. -/
def streamAbutting : List Scanned := [⟨.prop, 0, 3⟩, ⟨.content, 3, 4⟩]

/-- `&a [`: a two-character property, a space, then content at offset 3. -/
def streamSeparated : List Scanned := [⟨.prop, 0, 2⟩, ⟨.content, 3, 4⟩]

/-- The two emit the *same* stream — the recorded positions agree too, so this is
    not a matter of the scanner recording positions more carefully. -/
theorem projections_agree :
    streamAbutting.map project = streamSeparated.map project := rfl

/-- And they disagree on the rule. -/
theorem abutment_differs : abuts streamAbutting ≠ abuts streamSeparated := by decide

/-- **No lookback can decide a distance rule.**  Any test the scanner can run
    over its own token array is a function of the emitted stream; by
    `projections_agree` that function returns one value for two runs that
    `abutment_differs` says must get different answers. -/
theorem no_lookback_sees_abutment :
    ¬ ∃ p : List Emitted → Bool, ∀ l : List Scanned, p (l.map project) = abuts l := by
  rintro ⟨p, hp⟩
  have h1 : p (streamAbutting.map project) = abuts streamAbutting := hp streamAbutting
  have h2 : p (streamAbutting.map project) = abuts streamSeparated := by
    rw [projections_agree]; exact hp streamSeparated
  exact abutment_differs (h1.symm.trans h2)

/-! ### The contrast: an order rule DOES factor through the stream

Item 9e's "two properties in a row" is a function of the class sequence alone,
which is why it could be a lookback — and could be read two tokens deep, or ten,
at no extra cost. -/

/-- The order rule, written where it actually lives: on the class sequence. -/
def twoPropsKinds : List Kind → Bool
  | a :: b :: rest => (a == .prop && b == .prop) || twoPropsKinds (b :: rest)
  | _ => false

/-- Its reading on a run. -/
def twoPropsInARow (l : List Scanned) : Bool := twoPropsKinds (l.map Scanned.kind)

/-- **Order rules factor through the emitted stream** — by construction, since
    `twoPropsInARow` is `twoPropsKinds` composed with a projection.  Stating it
    this way is the point: the proof is one rewrite, and no analogous rewrite
    exists for `abuts`. -/
theorem twoPropsInARow_is_an_order_rule (l₁ l₂ : List Scanned)
    (h : l₁.map Scanned.kind = l₂.map Scanned.kind) :
    twoPropsInARow l₁ = twoPropsInARow l₂ := by
  unfold twoPropsInARow; rw [h]

/-! ### Where the distance rule can live instead

At the producing dispatch the extent is still in hand, so the same fact is one
character lookup away. -/

/-- The forward test: the character the token's own walk stopped before must be
    separation or an entry boundary — never the start of content.  `none` (end of
    input) passes. -/
def forwardOk (t : Scanned) (src : List Char) : Bool :=
  match src[t.stop]? with
  | none => true
  | some c => c == ' ' || c == ',' || c == ']' || c == '}'

/-! `&ab[x]` — the property ends at 3 and `[` is right there. -/
#guard forwardOk ⟨.prop, 0, 3⟩ "&ab[x]".toList == false

/-! `&ab [x]` — same property, a space follows. -/
#guard forwardOk ⟨.prop, 0, 3⟩ "&ab [x]".toList == true

/-! `&ab` at end of input. -/
#guard forwardOk ⟨.prop, 0, 3⟩ "&ab".toList == true

/-! `&ab,` — the node ended with `e-scalar` and the entry closes. -/
#guard forwardOk ⟨.prop, 0, 3⟩ "&ab,c".toList == true

/-! ## §3  Sibling classes decide what a probe can reach

The two property forms accept different characters INSIDE the name, so the same
follower is absorbed by one and stops the other. -/

/-- `[102] ns-anchor-char`: `ns-char` minus the flow indicators. -/
def anchorChar (c : Char) : Bool :=
  !(c == ',' || c == '[' || c == ']' || c == '{' || c == '}')

/-- `[153] ns-tag-char`: also minus everything outside `ns-uri-char` — the quotes
    are the part that matters here. -/
def tagChar (c : Char) : Bool :=
  anchorChar c && !(c == '"' || c == '\'')

/-- A name of this class stops at `c`. -/
def stopsAnchor (c : Char) : Bool := !anchorChar c

/-- A tag name stops at `c`. -/
def stopsTag (c : Char) : Bool := !tagChar c

/-- Characters that START content, as opposed to ending the entry. -/
def startsContent (c : Char) : Bool :=
  c == '[' || c == '{' || c == '"' || c == '\'' || c == 'x'

/-- The delimiter check is *reachable* for a form exactly when its own class
    stops there and what follows is content. -/
def reaches (stops : Char → Bool) (c : Char) : Bool := stops c && startsContent c

/-- The characters a probe of this rule would naturally try. -/
def probeAlphabet : List Char :=
  [' ', ',', ']', '}', '[', '{', '"', '\'', '*', '&', ':', 'x']

/-- What the anchor form can fail on. -/
def anchorGaps : List Char := probeAlphabet.filter (reaches stopsAnchor)

/-- What the tag form can fail on. -/
def tagGaps : List Char := probeAlphabet.filter (reaches stopsTag)

/-! Only the flow indicators end an anchor name … -/
#guard anchorGaps == ['[', '{']

/-! … while a tag also stops at either quote. -/
#guard tagGaps == ['[', '{', '"', '\'']

/-! **The trap, as a set difference.**  It is nonempty, so a sweep run against
    the anchor form is silent on precisely the characters the tag form fails on —
    and its silence is structural, not evidence. -/
#guard tagGaps.filter (fun c => !anchorGaps.contains c) == ['"', '\'']

/-! The converse direction is empty: the anchor form has no gap of its own, so
    the two are not merely different — one strictly contains the other, which is
    why probing the *wrong* one looks like a complete answer. -/
#guard anchorGaps.filter (fun c => !tagGaps.contains c) == []

/-- Stated without the alphabet: the extra reachable followers are exactly the
    characters the anchor name absorbs and the tag name does not. -/
theorem gap_is_the_class_difference :
    ∀ c ∈ probeAlphabet,
      (reaches stopsTag c && !reaches stopsAnchor c)
        = (anchorChar c && !tagChar c && startsContent c) := by decide

/-! ## §4  Blast radius of adding the distance rule to an order rule -/

/-- Item 9e's guard: an order rule. -/
def guardOrder (l : List Scanned) : Bool := twoPropsInARow l

/-- Item 9f folds the distance rule into the same test. -/
def guardBoth (l : List Scanned) : Bool := twoPropsInARow l || abuts l

/-- They differ on exactly one class — streams the order rule accepts whose
    tokens abut — stated as an `iff` so the strictening is visibly neither
    vacuous nor wider than claimed. -/
theorem guards_differ_exactly_on_abutment (l : List Scanned) :
    (guardOrder l ≠ guardBoth l) ↔ (twoPropsInARow l = false ∧ abuts l = true) := by
  unfold guardOrder guardBoth
  cases h1 : twoPropsInARow l <;> cases h2 : abuts l <;> simp

/-! The class is nonempty: `streamAbutting` is a single property followed by
    content, which item 9e's order rule has nothing to say about. -/
#guard guardOrder streamAbutting == false
#guard guardBoth streamAbutting == true

/-! And the gate costs nothing where the order rule already fired. -/
#guard guardOrder [⟨.prop, 0, 2⟩, ⟨.prop, 3, 5⟩] == true
#guard guardBoth [⟨.prop, 0, 2⟩, ⟨.prop, 3, 5⟩] == true

/-! ## §5  Axiom profile -/

/-- info: 'Tests.Reflections.OrderVersusDistancePredicates.no_lookback_sees_abutment' depends on axioms: [propext] -/
#guard_msgs in
#print axioms no_lookback_sees_abutment

/-- info: 'Tests.Reflections.OrderVersusDistancePredicates.twoPropsInARow_is_an_order_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms twoPropsInARow_is_an_order_rule

/-- info: 'Tests.Reflections.OrderVersusDistancePredicates.gap_is_the_class_difference' does not depend on any axioms -/
#guard_msgs in
#print axioms gap_is_the_class_difference

/-- info: 'Tests.Reflections.OrderVersusDistancePredicates.guards_differ_exactly_on_abutment' depends on axioms: [propext] -/
#guard_msgs in
#print axioms guards_differ_exactly_on_abutment

end Tests.Reflections.OrderVersusDistancePredicates

end Blanket
