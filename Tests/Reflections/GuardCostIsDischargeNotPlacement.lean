/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-! # A strictening costs its discharge, not its placement (Reflection 617)

Two guards, added to the same dispatcher on the same day, with the *same shape*
— a one-token lookback into the emitted stream, rejecting a predecessor the
grammar has no production for.  One cost **one** proof site.  The other is
blocked on strengthening an invariant threaded through twenty-one files.

The difference is not where the `if` went, and it is not how big the gap is
between the guard and the invariant the proofs already thread — §3 shows that
gap is *identical* for the two, down to the same one-token witness.  The
difference is whether the **producer** ever walks the guarded path.  The
round-trip tower has to show the emitter's own output still scans; a guard on a
character the emitter never writes generates no obligation at all, so every
placement of it is free.  A guard on a character the emitter writes at every
mapping pair generates the obligation "the emitter's `:` passes this test" — and
that obligation is the same wherever the `if` sits.

So the order of operations is: **cost the producer first.**  One sweep of the
emitter for the guarded character settles the price before any placement
analysis; placement then decides only which inversion the downstream proofs get.

Sequel to Reflection 616 (which says where a rule *can* live: order rules look
back, distance rules must look forward) and the proof-obligation axis of
Reflection 613 (which costs the *elaboration*: an added `if` in a `do` block
duplicates the continuation).  Both of those are about the guard.  This one is
about everything downstream of it.

L4YAML DOCS item 9g, 2026-08-08.  `[150] ns-flow-pair` is
`"?" s-separate ns-flow-map-explicit-entry` and an `ns-flow-pair` is an *entry*,
so inside a flow collection a `?` stands only after `[`, `{` or `,` — yet
`[? ? a]`, `[: ?]`, `[&a ? b]` and `[!t ?]` all scanned clean in both pipelines.
The rule shipped as a third conjunct on the `?` arm's dispatch condition and
cost exactly one `by_cases`.  Its sibling — a flow entry has at most one value,
so `[a: b: c]` and `{a: : b}` have no derivation either — is the same lookback
one arm over, and is blocked: the emit→scan towers thread "the last real token
does not complete a flow value", `.value` satisfies that, and the emitter writes
`:` at every pair.
-/

namespace Tests.Reflections.GuardCostIsDischargeNotPlacement

/-! ## §0  The substrate

`Tok` is what the scanner emits, `Ch` what the emitter writes.  `open`/`comma`
bound an entry; `node` completes one; `key`/`value` are the two indicators. -/

inductive Tok where
  | open | comma | key | value | node
  deriving DecidableEq, Repr, BEq

inductive Ch where
  | cOpen | cClose | cComma | cQ | cColon | cNode
  deriving DecidableEq, Repr, BEq

/-- The toy of `YamlToken.opensFlowEntry`. -/
def opensEntry : Tok → Bool
  | .open => true
  | .comma => true
  | _ => false

/-- The toy of `YamlToken.completesFlowValue`. -/
def completes : Tok → Bool
  | .node => true
  | _ => false

/-! ## §1  The two guards have the same shape

Both are a predicate applied to the last emitted token — nothing else.  Whatever
explains the cost difference, it is not the shape, the depth of the lookback, or
the arm they sit on. -/

/-- `?` may only open an entry (item 9g, shipped). -/
def pQ : Option Tok → Bool
  | some t => opensEntry t
  | none => false

/-- `:` may not follow a `value` — one value per entry (item 9g's sibling, open). -/
def pC : Option Tok → Bool
  | some t => !(t == Tok.value)
  | none => true

def guardQ (ts : List Tok) : Bool := pQ ts.getLast?
def guardC (ts : List Tok) : Bool := pC ts.getLast?

theorem guards_are_the_same_shape :
    (∃ p : Option Tok → Bool, ∀ ts, guardQ ts = p ts.getLast?) ∧
    (∃ p : Option Tok → Bool, ∀ ts, guardC ts = p ts.getLast?) :=
  ⟨⟨pQ, fun _ => rfl⟩, ⟨pC, fun _ => rfl⟩⟩

/-! ## §2  The producer decides

`emit` is the toy round-trip producer.  It writes `:` for every pair and never
writes `?` — exactly the asymmetry `grep "'?'" L4YAML/Output/` reports in one
second, and exactly the fact that settles the two guards' prices. -/

inductive Doc where
  | leaf
  | pair (k v : Doc)
  | two (x y : Doc)
  deriving Repr

def emit : Doc → List Ch
  | .leaf => [.cNode]
  | .pair k v => .cOpen :: (emit k ++ .cColon :: (emit v ++ [.cClose]))
  | .two x y => .cOpen :: (emit x ++ .cComma :: (emit y ++ [.cClose]))

theorem emit_never_q (d : Doc) : Ch.cQ ∉ emit d := by
  induction d with
  | leaf => simp [emit]
  | pair k v ihk ihv => simp [emit, ihk, ihv]
  | two x y ihx ihy => simp [emit, ihx, ihy]

theorem emit_uses_colon : (emit (.pair .leaf .leaf)).contains Ch.cColon = true := by decide

/-! ### The discharge obligation, made explicit

`toks` is what the scanner emits for `emit d`; `consults pre d` lists every
point at which a guard would be consulted, paired with the token prefix visible
there.  A guard's obligation in the round-trip proof is exactly: hold at every
entry of this list whose character is the guarded one. -/

def toks : Doc → List Tok
  | .leaf => [.node]
  | .pair k v => .open :: (toks k ++ .value :: toks v)
  | .two x y => .open :: (toks x ++ .comma :: toks y)

def consults (pre : List Tok) : Doc → List (Ch × List Tok)
  | .leaf => []
  | .pair k v =>
      consults (pre ++ [.open]) k
        ++ (Ch.cColon, pre ++ [.open] ++ toks k)
             :: consults (pre ++ [.open] ++ toks k ++ [.value]) v
  | .two x y =>
      consults (pre ++ [.open]) x
        ++ consults (pre ++ [.open] ++ toks x ++ [.comma]) y

/-- **The `?` guard's obligation is empty.**  No consultation the producer
    reaches is a `?`, so the round-trip proof never mentions the guard and every
    placement of it is free. -/
theorem guardQ_obligation_is_vacuous (d : Doc) :
    ∀ pre, ∀ p ∈ consults pre d, p.1 ≠ Ch.cQ := by
  induction d with
  | leaf => intro pre p hp; simp [consults] at hp
  | pair k v ihk ihv =>
      intro pre p hp
      simp only [consults, List.mem_append, List.mem_cons] at hp
      rcases hp with h | h | h
      · exact ihk _ p h
      · subst h; simp
      · exact ihv _ p h
  | two x y ihx ihy =>
      intro pre p hp
      simp only [consults, List.mem_append] at hp
      rcases hp with h | h
      · exact ihx _ p h
      · exact ihy _ p h

/-- **The `:` guard's obligation is not empty**, and its very first instance
    already puts the guard face to face with the token prefix it must clear. -/
theorem guardC_obligation_is_not_vacuous :
    (consults [] (.pair .leaf .leaf)).contains (Ch.cColon, [Tok.open, Tok.node]) = true := by
  decide

/-! ## §3  The gap against the threaded invariant is the SAME for both

`inv` is the toy of the invariant the emit→scan towers actually carry: the last
real token does not complete a flow value.  Neither guard follows from it — and
the counterexample is the *same one token*.  So the size of the gap does not
predict the cost either; only §2 does. -/

def pInv : Option Tok → Bool
  | some t => !completes t
  | none => true

def inv (ts : List Tok) : Bool := pInv ts.getLast?

/-- The crux of the reflection: identical gap, identical witness, opposite cost.
    `.value` does not complete a value, so the threaded invariant admits it —
    and both guards reject it. -/
theorem same_gap :
    (inv [Tok.value] = true ∧ guardQ [Tok.value] = false) ∧
    (inv [Tok.value] = true ∧ guardC [Tok.value] = false) := by decide

/-! ### What closing the gap costs, when you must

`inv'` is the strengthened invariant: the last token *opens an entry*.  It
implies both guards, and it is strictly stronger — so adopting it is real work
at every site that produces the old one, not a rename.  In L4YAML that is the
whole price of the `:` half: the towers state the old invariant in twenty-one
files, and each producer of it would have to establish the new one. -/

def pInv' : Option Tok → Bool
  | some t => opensEntry t
  | none => false

def inv' (ts : List Tok) : Bool := pInv' ts.getLast?

/-- Everything in §1 and §3 factors through `getLast?`, so one case analysis on
    the option settles all three implications at once. -/
theorem pInv'_implies (o : Option Tok) (h : pInv' o = true) :
    pQ o = true ∧ pC o = true ∧ pInv o = true := by
  cases o with
  | none => exact absurd h (by decide)
  | some t => revert h; cases t <;> decide

theorem inv'_implies_both (ts : List Tok) (h : inv' ts = true) :
    guardQ ts = true ∧ guardC ts = true :=
  ⟨(pInv'_implies _ h).1, (pInv'_implies _ h).2.1⟩

theorem inv'_is_strictly_stronger :
    (∀ ts, inv' ts = true → inv ts = true)
    ∧ inv [Tok.value] = true ∧ inv' [Tok.value] = false :=
  ⟨fun _ h => (pInv'_implies _ h).2.2, by decide, by decide⟩

/-! ## §4  The method: sweep the PRODUCER

Reflection 614's sweep is over the *consumer's* input, and says what its
alphabet must contain before its silence means anything.  This one is over the
*producer's* output, and its silence is exactly the thing you want: it is a
statement that the guard has no discharge obligation.  State the bound either
way. -/

def allDocs : Nat → List Doc
  | 0 => [.leaf]
  | n + 1 =>
      .leaf :: (allDocs n).flatMap fun a =>
        (allDocs n).flatMap fun b => [.pair a b, .two a b]

def guardedChars (d : Doc) : List Ch := (consults [] d).map Prod.fst

/-! The bound, stated: 723 documents of depth ≤ 3, exhaustively. -/
#guard (allDocs 3).length == 723

/-! Zero hits — the `?` guard is never consulted on producer output, so it has
    nothing to discharge and every placement of it is free. -/
#guard (allDocs 3).all fun d => !((guardedChars d).contains Ch.cQ)

/-! Same sweep, same bound, opposite verdict: 697 of the 723 consult the `:`
    guard, so wherever it is placed it owes 697 discharges. -/
#guard ((allDocs 3).filter fun d => (guardedChars d).contains Ch.cColon).length == 697

/-! And on the producer's *characters*, the same asymmetry one grep would show. -/
#guard (allDocs 3).all fun d => !((emit d).contains Ch.cQ)
#guard (allDocs 3).any fun d => (emit d).contains Ch.cColon

/-! ## §5  Axiom profile -/

/-- info: 'Tests.Reflections.GuardCostIsDischargeNotPlacement.emit_never_q' depends on axioms: [propext] -/
#guard_msgs in
#print axioms emit_never_q

/-- info: 'Tests.Reflections.GuardCostIsDischargeNotPlacement.guardQ_obligation_is_vacuous' depends on axioms: [propext] -/
#guard_msgs in
#print axioms guardQ_obligation_is_vacuous

/-- info: 'Tests.Reflections.GuardCostIsDischargeNotPlacement.same_gap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms same_gap

/-- info: 'Tests.Reflections.GuardCostIsDischargeNotPlacement.inv'_implies_both' depends on axioms: [propext] -/
#guard_msgs in
#print axioms inv'_implies_both

end Tests.Reflections.GuardCostIsDischargeNotPlacement

end Blanket
