module


@[expose] public section Blanket

/-!
# Reflection 614 — a guard's exemption list inherits the *next* dispatcher's side condition

A rejection guard that runs early in a pipeline often needs to let some
characters through because they are *not* what it rejects:

```lean
-- "reject a node that follows a completed value with no separator"
if lastCompletedValue && c ≠ ',' && c ≠ ':' && c ≠ ']' && c ≠ '}' then reject
```

The exemption list is a claim about **roles**: "`,` `:` `]` `}` are separators or
closers, not node starts". For `,` `]` `}` that claim is unconditional — those
characters have exactly one role. For `:` it is not: whether a `:` is a value
indicator is decided by a *later* dispatcher, under its own side condition
(`isValueCandidate`). A `:` that fails that test falls through and starts a plain
scalar — a node start, the very thing the guard exists to reject.

**The rule.** When a guard exempts a character on the grounds that "it plays role
R here", and some later stage decides role R under a condition `P`, the exemption
must carry `P`. Otherwise the guard leaks on exactly the inputs where the
character changes role — and those are the inputs nobody writes down, because
the character's *usual* role is the one in everyone's head.

Mechanically the fix is one conjunct: `c ≠ ':'` becomes
`¬(c = ':' ∧ isValueCandidate s)`. The inversion lemma the proofs consume gains
the matching premise `c = ':' → isValueCandidate s = false`, and the construction
lemma splits in two — one for the unconditional characters, one taking `P` as an
argument. §3 below is that pair.

## The second half: the leak is invisible to the obvious probe

The leak was not found by a failing test. It was found from a *proof* — an arm
that could not be closed because it could not rule out `tail = value` — and then
localised by brute force: every input of length ≤ 5 over two 15-character
alphabets, ≈1.6M strings, scanned and checked. **Zero hits.**

The alphabets held every character the lesson seemed to be about: `[ ] { } , : a
b " ' * & ? - \n \t !`. The witness needs `#`:

```yaml
[a #c
 :b]
```

A comment is what *ends* the plain scalar `a`; without one, `a :b` keeps scanning
as a single scalar and the two entries never become adjacent. The shortest
witness is 10 characters, so no length-≤5 sweep over any alphabet could have
found it.

**The rule.** When probing whether a proof arm is reachable, build the alphabet
from the constructs that **end a token**, not from the syntax the arm is about.
Token terminators — comments, line breaks, indentation changes, EOF — are what
put two constructs next to each other, and adjacency is what most of these arms
are about. And *state the bound*: "0 hits over inputs of length ≤ 5" is a fact
about the sweep, never evidence of vacuity.

§4 is that probe, in miniature: the same sweep over an alphabet without the
terminator (0 hits) and with it (hits), so the demo carries its own
counterexample-to-the-method.

## What this file pins

Unlike Reflection 613 this is a *design* lesson, not an elaborator fact, so there
is nothing here that a toolchain bump should break. What the guards pin is the
lesson's own arithmetic: that the unconditional exemption really does admit the
witness (§2), that the conditional one really does reject it while keeping every
legitimate `:` (§2), and that the sweep's verdict really does depend on the
alphabet (§4). If a future edit "simplifies" the exemption back to a plain
inequality, §2 fails.

L4YAML instance (DOCS item 9d, 2026-08-07): `scanNextToken_checkFlowAdjacency`
exempted `:` unconditionally, so `[a #c⏎ :b]` and `{a #c⏎ :b}` scanned clean in
both pipelines — separator-less flow entries, which `[138] ns-s-flow-seq-entries`
and `[141] ns-s-flow-map-entries` forbid and PyYAML rejects. Found from β.3's
flow-interior content step, which needs `tailOf sc.tokens ≠ .value` to apply
`FlowOpenStack.receiveNode`. Regression net:
`Tests/Guards/Proofs/ScannerFlowColonAdjacency.lean`.
-/

namespace Tests.Reflections.RoleDependentGuardExemption

set_option autoImplicit false

/-! ## §1  A two-dispatcher pipeline in miniature

`Tok` is the token history, `Ch` the alphabet. `dispatchSep` runs first and
handles the separators; whatever it declines falls through to `dispatchNode`,
which starts a node. `Colon` is the role-ambiguous character: `dispatchSep`
consumes it as a separator **only** when `isSep` holds — that is the later side
condition the early guard has to know about. -/

inductive Ch where
  | comma | colon | close | node
  deriving DecidableEq, Repr, BEq

inductive Tok where
  /-- The previous token completed a value: a node may not follow directly. -/
  | value
  /-- A separator: a node may follow. -/
  | sep
  deriving DecidableEq, Repr, BEq

/-- The later dispatcher's own side condition — here, "the `:` is followed by a
    blank", which is what makes it a separator rather than a scalar's first
    character. Carried on the state so the demo can vary it. -/
structure St where
  last : Tok
  /-- `true`: a following `:` is a separator. `false`: it starts a node. -/
  colonIsSep : Bool
  deriving Repr, BEq

inductive Err where
  | adjacentNodes
  deriving DecidableEq, Repr, BEq

/-- Second dispatcher: consumes `Colon` as a separator exactly when `colonIsSep`.
    Returns `none` to fall through. -/
def dispatchSep (s : St) (c : Ch) : Option St :=
  match c with
  | .comma => some { s with last := .sep }
  | .close => some { s with last := .sep }
  | .colon => if s.colonIsSep then some { s with last := .sep } else none
  | .node  => none

/-- Third dispatcher: everything that reaches here starts a node. -/
def dispatchNode (s : St) (_c : Ch) : St := { s with last := .value }

/-! ## §2  The two guards

`guardLoose` states the exemption as a bare membership test — the shape that
reads correctly and leaks. `guardTight` carries the later side condition. -/

/-- The leaky exemption: `Colon` is exempt because "`:` is a separator". -/
def guardLoose (s : St) (c : Ch) : Option Err :=
  if s.last == .value && c != .comma && c != .colon && c != .close then
    some .adjacentNodes
  else none

/-- Item 9d's shape: `Colon` is exempt only while it really is a separator. -/
def guardTight (s : St) (c : Ch) : Option Err :=
  if s.last == .value && c != .comma && !(c == .colon && s.colonIsSep) && c != .close then
    some .adjacentNodes
  else none

/-- One step under a chosen guard. -/
def step (guard : St → Ch → Option Err) (s : St) (c : Ch) : Except Err St :=
  match guard s c with
  | some e => .error e
  | none =>
    match dispatchSep s c with
    | some s' => .ok s'
    | none => .ok (dispatchNode s c)

/-- Run a whole input. -/
def run (guard : St → Ch → Option Err) (s : St) : List Ch → Except Err St
  | [] => .ok s
  | c :: cs => match step guard s c with
    | .error e => .error e
    | .ok s' => run guard s' cs

/-- Core has no `BEq (Except Err St)`, so the guards compare through this. -/
private def same : Except Err St → Except Err St → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

/-! The witness: a completed value, then a `:` that is **not** a separator.
Loose admits it; tight rejects it. -/

def witness : St := { last := .value, colonIsSep := false }

#guard same (run guardLoose witness [.colon]) (.ok { last := .value, colonIsSep := false })
#guard same (run guardTight witness [.colon]) (.error .adjacentNodes)

/-! And the half that must not break: a `:` that IS a separator stays exempt
under both guards, so no legitimate input changes verdict. -/

private def legit : St := { last := .value, colonIsSep := true }

#guard same (run guardLoose legit [.colon]) (.ok { last := .sep, colonIsSep := true })
#guard same (run guardTight legit [.colon]) (.ok { last := .sep, colonIsSep := true })

/-! The characters with only one role are unaffected either way. -/

#guard same (run guardLoose witness [.comma]) (run guardTight witness [.comma])
#guard same (run guardLoose witness [.close]) (run guardTight witness [.close])
#guard same (run guardLoose witness [.node]) (.error .adjacentNodes)
#guard same (run guardTight witness [.node]) (.error .adjacentNodes)

/-! After a separator both guards let anything through — the guard fires only on
`last = .value`, so tightening it cannot reject a separated node. -/

private def afterSep : St := { last := .sep, colonIsSep := false }

#guard [Ch.comma, .colon, .close, .node].all fun c =>
  same (run guardLoose afterSep [c]) (run guardTight afterSep [c])

/-- **The blast radius, stated as a theorem rather than a slogan.** The two
    guards differ on exactly one class of state/character pair: `last = .value`,
    `c = .colon`, `colonIsSep = false`. Everywhere else they agree, which is why
    the strictening is safe to ship. -/
theorem guards_agree_off_the_leak (s : St) (c : Ch)
    (h : ¬(s.last = .value ∧ c = .colon ∧ s.colonIsSep = false)) :
    guardLoose s c = guardTight s c := by
  cases s with
  | mk last colonIsSep =>
    revert h
    cases last <;> cases c <;> cases colonIsSep <;> decide

/-- And they really do differ there — the exemption is not vacuous. -/
theorem guards_differ_on_the_leak :
    guardLoose witness .colon ≠ guardTight witness .colon := by decide

/-! ## §3  What the change costs the proofs

Both directions of the guard are consumed by proofs, and both change shape.

* **Inversion** (given the guard passed, derive a fact): gains the premise
  `c = colon → colonIsSep = false`. Sites that pass a *literal* non-colon
  character discharge it with `simp`, so they do not change.
* **Construction** (prove the guard passes): the unconditional lemma loses
  `Colon` from its disjunction, and a second lemma takes the side condition as an
  argument. In L4YAML the emitter always writes `": "` with a following blank, so
  every emit→scan tower discharges the new lemma from a fact it already had — the
  call sites moved one `have` earlier, nothing more. -/

/-- Inversion: a passing guard at a node start means the previous token did not
    complete a value. Note the `colon` premise — this is the whole edit. -/
theorem notValue_of_guardTight_none {s : St} {c : Ch}
    (h : guardTight s c = none)
    (hc : c ≠ .comma ∧ c ≠ .close)
    (hcolon : c = .colon → s.colonIsSep = false) :
    s.last ≠ .value := by
  obtain ⟨h1, h2⟩ := hc
  obtain ⟨last, cis⟩ := s
  revert h hcolon h1 h2
  cases last <;> cases c <;> cases cis <;> decide

/-- The pre-change corollary, for sites where `c` is a literal node start: it
    still follows, so those call sites need no edit at all. -/
theorem notValue_of_guardTight_none_nodeChar {s : St} {c : Ch}
    (h : guardTight s c = none) (hc : c ≠ .comma ∧ c ≠ .colon ∧ c ≠ .close) :
    s.last ≠ .value :=
  notValue_of_guardTight_none h ⟨hc.1, hc.2.2⟩ (fun hcol => absurd hcol hc.2.1)

/-- Construction, unconditional half: the single-role characters. -/
theorem guardTight_none_of_sepChar {s : St} {c : Ch}
    (h : c = .comma ∨ c = .close) : guardTight s c = none := by
  obtain ⟨last, cis⟩ := s
  revert h
  cases last <;> cases c <;> cases cis <;> decide

/-- Construction, conditional half: a `:` that really is a separator. -/
theorem guardTight_none_of_colonIsSep {s : St} {c : Ch}
    (hc : c = .colon) (hv : s.colonIsSep = true) : guardTight s c = none := by
  obtain ⟨last, cis⟩ := s
  revert hc hv
  cases last <;> cases c <;> cases cis <;> decide

/-! ## §4  The probe, and why its alphabet decided the answer

The leak is a state/character pair, but a *scanner* only reaches that pair for
inputs that put a completed value directly before a non-separator `:`. Below,
`Src` is a character-level input alphabet and `compile` is the little scanner
that turns it into steps. `Space` glues a value and a following `:` into one
token — so no sweep over `{Value, Colon, Space}` can ever produce the pair.
`Hash` is the terminator that breaks the glue.

The two sweeps below are the demo's real payload: **same length bound, same
guard, opposite verdicts** — the alphabet is what decided it. -/

inductive Src where
  /-- Starts (or continues) a value token. -/
  | val
  /-- Ambiguous: glued onto a preceding value if one is open, else a node start. -/
  | colon
  /-- Whitespace: does NOT end an open value token — it is absorbed into it. -/
  | space
  /-- A comment: ENDS an open value token. This is the terminator the first
      alphabet lacked. -/
  | hash
  deriving DecidableEq, Repr, BEq

/-- The miniature scanner: `open?` tracks whether a value token is still being
    collected. A `:` reaching the dispatcher while no value token is open is a
    node start; while one is open it is absorbed. -/
private def compile : Bool → List Src → List Ch
  | _, [] => []
  -- A value character while no token is open STARTS a node and opens the token.
  | false, .val :: rest => .node :: compile true rest
  | true, .val :: rest => compile true rest
  -- A `:` while no token is open reaches the dispatchers, which decide its role;
  -- if it is not a separator it starts a plain scalar, so it opens too.
  | false, .colon :: rest => .colon :: compile true rest
  | true, .colon :: rest => compile true rest
  -- Whitespace is absorbed by an open token: it does NOT end one.
  | o, .space :: rest => compile o rest
  -- A comment ends the open token.  This is the only closer in the alphabet.
  | _, .hash :: rest => compile false rest

/-- A source string exposes the leak when the loose and tight guards disagree on
    it, starting from a clean state where `:` is not a separator. -/
private def exposes (w : List Src) : Bool :=
  let s : St := { last := .sep, colonIsSep := false }
  same (run guardLoose s (compile false w)) (.error .adjacentNodes) !=
    same (run guardTight s (compile false w)) (.error .adjacentNodes)

private def words (alphabet : List Src) : Nat → List (List Src)
  | 0 => [[]]
  | n + 1 => (words alphabet n).flatMap fun w => alphabet.map fun c => w ++ [c]

private def sweep (alphabet : List Src) (n : Nat) : List (List Src) :=
  ((List.range (n + 1)).flatMap (words alphabet)).filter exposes

/-- Everything the lesson looks like it is about — and no terminator. -/
private def alphaObvious : List Src := [.val, .colon, .space]

/-- The same, plus the construct that ends a token. -/
private def alphaWithTerminator : List Src := [.val, .colon, .space, .hash]

/-! **Zero hits, and not because the guard is fine.** Every input of length ≤ 6
over the obvious alphabet: the sweep is exhaustive and says nothing. -/

#guard (sweep alphaObvious 6).isEmpty

/-! Add the terminator and the same bound finds it. -/

#guard !(sweep alphaWithTerminator 6).isEmpty

/-! The shortest witness, exactly: `value`, terminator, `colon`. It is length 3
here and 10 characters in the real scanner — in both cases longer than the
obvious alphabet could ever reach, for a reason that has nothing to do with
length. -/

#guard (sweep alphaWithTerminator 6).all (fun w => w.length ≥ 3)
#guard (sweep alphaWithTerminator 6).contains [.val, .hash, .colon]

/-! And the honest form of the negative result: the bound is part of the claim. -/

#guard ((List.range 7).map fun n => (sweep alphaObvious n).length) == [0, 0, 0, 0, 0, 0, 0]

/-! ## §5  Axiom pins

The two theorems that carry the lesson's content — that the change is confined to
one class of inputs, and that the class is non-empty. -/

/-- info: 'Tests.Reflections.RoleDependentGuardExemption.guards_agree_off_the_leak' does not depend on any axioms -/
#guard_msgs in
#print axioms guards_agree_off_the_leak

/-- info: 'Tests.Reflections.RoleDependentGuardExemption.guards_differ_on_the_leak' does not depend on any axioms -/
#guard_msgs in
#print axioms guards_differ_on_the_leak

/-- info: 'Tests.Reflections.RoleDependentGuardExemption.notValue_of_guardTight_none' does not depend on any axioms -/
#guard_msgs in
#print axioms notValue_of_guardTight_none

end Tests.Reflections.RoleDependentGuardExemption

end Blanket
