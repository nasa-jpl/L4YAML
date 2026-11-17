module

public import Scripts.Ledger

@[expose] public section Blanket

/-!
# Scripts.Census.Dashboard — every directed census, its goal, and the distance left (DOCS item 514)

The guards under `Tests/Guards/Proofs/` pin some two hundred readings as `def expected… : String :=
"k=v k=v …"` literals.  Some of those fields are OBJECTIVES — a count the campaign drives to zero
(`CapstonePathAudit.on`, `GhostIndexCensus.ghost`, the `DECLINE` edges), or up to a bound the same
pin names (`SurfaceSpanCensus.covered → closure`, `ScannerFlowOpenUnderRun.paid → cells`) — and the
rest are READINGS, snapshots with no direction (term sizes, thread lengths, the rows of a walk).
Nothing in the tree says which is which, so the question "how much is left, and what moves it" has
been answered from memory, per census, per item.

This module answers it from the pins.  `roster` is the list of directed fields: for each, the guard
file and pin that holds the reading, the field, the goal (`zero`, a constant, or another field of
the same pin), the monotonicity the guard enforces (`shrinkOnly` / `growOnly` / `hold`), the rule or
step it serves, and what moves it.  `readPins` takes the current reading OFF THE PIN LITERALS — the
same literals the guards compare against the environment on every full build, so the dashboard is
exactly as current as the last green build (§3: read what is pinned before measuring) — and
`distance` is `|now − goal|`.  Every field of every `String` pin that is not on the roster is listed
under *readings without a target*, so a census cannot hide by being left off the roster.

`--check` (`lake run census-dashboard -- --check`) fails when a roster row names a pin or a field
the guards no longer hold: a renamed census moves the roster in the same PR or the gate goes red.
The roster is a hand-written list, as the guards' own expected values are: each row cites the item
whose text states the direction.

Hand parsers only (plan §6 Q1: no regex dependency), each with its `#guard` rows: the Lean string
literal (escapes and `\`-newline continuation), `def NAME : String :=` / `: Nat :=` heads with
comment lines between the head and the literal, and the `key=value` fields of a reading, found
anywhere in the literal (inside `[…]`, `(…)`, after `|`, inside another field's value), the first
occurrence of a key winning.
-/

namespace Scripts.Census.Dashboard

/-! ## The Lean string literal, read off source text -/

def isAsciiWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- The body of a string literal whose opening `"` has been consumed: `(body, rest)`.  Escapes
    `\"`, `\\`, `\n`, `\t`, `\'`; a `\` followed by a line break is Lean's continuation (the break
    and the next line's leading white space are dropped).  `none` on an unterminated literal. -/
partial def strLit (cs : List Char) (acc : List Char := []) : Option (String × List Char) :=
  match cs with
  | [] => none
  | '"' :: rest => some (String.ofList acc.reverse, rest)
  | '\\' :: rest =>
    match rest with
    | 'n' :: r => strLit r ('\n' :: acc)
    | 't' :: r => strLit r ('\t' :: acc)
    | '\\' :: r => strLit r ('\\' :: acc)
    | '"' :: r => strLit r ('"' :: acc)
    | '\'' :: r => strLit r ('\'' :: acc)
    | '\r' :: '\n' :: r | '\n' :: r => strLit (r.dropWhile (fun c => c == ' ' || c == '\t')) acc
    | c :: r => strLit r (c :: '\\' :: acc)
    | [] => none
  | c :: rest => strLit rest (c :: acc)

#guard strLit "abc\" tail".toList == some ("abc", " tail".toList)
#guard strLit "a\\\"b\\\\c\"".toList == some ("a\"b\\c", [])
#guard strLit "x=1 \\\n   y=2\"".toList == some ("x=1 y=2", [])
#guard strLit "open".toList == none

/-- After `:=`: skip white space and `--` comment lines, then read a string literal or a `Nat`. -/
partial def literalAfter (cs : List Char) : Option String :=
  let cs := cs.dropWhile isAsciiWs
  match cs with
  | '-' :: '-' :: rest => literalAfter (rest.dropWhile (· != '\n'))
  | '"' :: rest => (strLit rest).map (·.1)
  | c :: _ =>
    if c.isDigit then some (String.ofList (cs.takeWhile Char.isDigit)) else none
  | [] => none

/-- The literal of `def NAME : String :=` or `def NAME : Nat :=` in `text`, as a string. -/
def pinLiteral? (text name : String) : Option String :=
  let heads := [s!"def {name} : String :=", s!"def {name} : Nat :=", s!"def {name} :="]
  heads.findSome? fun h =>
    match text.splitOn h with
    | _ :: after :: _ => literalAfter after.toList
    | _ => none

#guard pinLiteral? "def expectedA : String :=\n  -- moved\n  \"a=1 b=2\"\n" "expectedA" == some "a=1 b=2"
#guard pinLiteral? "def expectedClosure : Nat := 287  -- -1\n" "expectedClosure" == some "287"
#guard pinLiteral? "def expectedB : String := \"x\"" "expectedA" == none

/-- Every `def expected… ` name declared in `text`, in order. -/
def pinNames (text : String) : Array String := Id.run do
  let mut out := #[]
  for line in text.splitOn "\n" do
    if line.startsWith "def expected" then
      let rest := line.toList.drop 4
      let name := String.ofList (rest.takeWhile fun c => c.isAlphanum || c == '_')
      if !name.isEmpty then out := out.push name
  return out

#guard pinNames "def expectedA : String :=\n\"\"\ndef foo := 1\ndef expectedB : Nat := 3\n" == #["expectedA", "expectedB"]

/-! ## `key=value` fields of a reading -/

def isKeyChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '-' || c == '.' || c == '/'

/-- Every `key=value` in `s`, wherever it stands (inside brackets, after `|`); `value` runs to the
    next white space, `,`, `]`, `)`, `;` or `|`.  The FIRST occurrence of a key wins. -/
def fields (s : String) : Array (String × String) := Id.run do
  let cs := s.toList.toArray
  let mut out : Array (String × String) := #[]
  let mut i := 0
  while i < cs.size do
    if isKeyChar cs[i]! && (i == 0 || !isKeyChar cs[i-1]!) then
      let mut j := i
      while j < cs.size && isKeyChar cs[j]! do j := j + 1
      if j < cs.size && cs[j]! == '=' then
        let key := String.ofList (cs.extract i j).toList
        let mut k := j + 1
        while k < cs.size && !(isAsciiWs cs[k]! || cs[k]! == ',' || cs[k]! == ']' || cs[k]! == ')' || cs[k]! == ';' || cs[k]! == '|') do
          k := k + 1
        let val := String.ofList (cs.extract (j + 1) k).toList
        if !(out.any (·.1 == key)) then out := out.push (key, val)
        i := j + 1
      else i := j
    else i := i + 1
  return out

#guard fields "positions=269 on=7 off=189 [DECLINE=241, FIELD=61] roots=capstone:26+blueprint:222(unresolved=5) thm=1 thm=2"
  == #[("positions", "269"), ("on", "7"), ("off", "189"), ("DECLINE", "241"), ("FIELD", "61"),
       ("roots", "capstone:26+blueprint:222(unresolved=5"), ("unresolved", "5"), ("thm", "1")]
#guard fields "paid=10 owed=14 hok=PPP ride=0/3 a=7+2" == #[("paid", "10"), ("owed", "14"), ("hok", "PPP"), ("ride", "0/3"), ("a", "7+2")]

/-- A pin's fields: its `key=value` pairs, or — for a pin whose whole literal is one count (the
    `Nat` pins: `expectedClosure`, `expectedConsumeAllUsers`) — the single field `value`. -/
def pinFields (lit : String) : Array (String × String) :=
  let fs := fields lit
  if fs.isEmpty && !lit.isEmpty && lit.all Char.isDigit then #[("value", lit)] else fs

#guard pinFields "287" == #[("value", "287")]
#guard pinFields "a=1" == #[("a", "1")]
#guard pinFields "PPP" == #[]

/-- A field's value as a count: digits; `a+b` sums (the births' `7+2`); `a/b` reads `a`. -/
def count? (v : String) : Option Nat :=
  let v := (v.splitOn "/").headD v
  let parts := v.splitOn "+"
  if parts.all (fun p => !p.isEmpty && p.all Char.isDigit) then
    some (parts.foldl (fun acc p => acc + p.toNat!) 0)
  else none

#guard count? "269" == some 269
#guard count? "7+2" == some 9
#guard count? "10/24" == some 10
#guard count? "PPP" == none
#guard count? "" == none

/-! ## The roster -/

/-- Where a directed field wants to go. -/
inductive Goal where
  /-- to zero -/
  | zero
  /-- to a constant -/
  | const (n : Nat)
  /-- to another field of the same pin (`covered → closure`) -/
  | field (name : String)
  /-- a non-numeric reading that must hold (`drop=false`, the non-circularity checks) -/
  | flag (value : String)
  deriving Repr, BEq, Inhabited

/-- What the guard enforces about the reading's movement. -/
inductive Move where
  /-- the pin may only go down; a rise needs the owner's word -/
  | shrinkOnly
  /-- the pin may only go up -/
  | growOnly
  /-- the reading is at its goal and must stay there -/
  | hold
  deriving Repr, BEq, Inhabited

def Move.render : Move → String
  | .shrinkOnly => "shrink-only"
  | .growOnly => "grow-only"
  | .hold => "hold"

/-- One directed census field. -/
structure Target where
  /-- the guard file's stem under `Tests/Guards/Proofs/`, or `scripts-ledger` -/
  census : String
  pin : String
  field : String
  goal : Goal
  move : Move
  /-- the rule, step or lane the field serves -/
  serves : String
  /-- what moves the reading toward the goal -/
  moves : String
  /-- the item or guard whose text states the direction -/
  basis : String
  /-- a sub-count of another row's field (`on-drop` of `on`): shown, not added to the totals -/
  component : Bool := false
  deriving Repr, Inhabited

/-- The directed fields.  A row leaves when its census is deleted; a row joins when a guard pins a
    count with a stated direction.  Keep `basis` honest: it is the only thing that makes a row's
    goal a reading of the tree rather than of someone's memory. -/
def roster : List Target := [
  -- The `∨ True` retirement lane (the owner's directive on item 394: fix all `∨ True`).
  { census := "CapstonePathAudit", pin := "expectedSummary", field := "on", goal := .zero, move := .shrinkOnly,
    serves := "parse_iff_grammar: no vacuous arm on a fact the capstone consumes",
    moves := "R12's (ω-pay-births) (d): the (2b) fixpoint pays the three ON park fields' `∨ PackAlt` (`pendingBlock.h_kslot`, `pendingBlockContent.h_kslot`, `pendingContent.h_vpack`) from the births, the `[map k]` resume fact and the `FlowStackK` carrier (items 510 / 513 → 140 sites / 19 decls)",
    basis := "item 439 (`CapstonePathAudit`: pins are shrink-only, ON re-pinned DOWN when an item pays or retires)" },
  { census := "CapstonePathAudit", pin := "expectedSummary", field := "off", goal := .zero, move := .shrinkOnly,
    serves := "the owner's `fix all ∨ True` — positions OFF the capstone's path",
    moves := "after ON reaches 0: each OFF position paid or retired by its own item (94 honest declines, 53 unread, 25 conclusions as of item 512)",
    basis := "item 439 (OFF is the residue the directive still names; the ON set is the risk)" },
  { census := "OrTrueAudit", pin := "expectedSummary", field := "positions", goal := .zero, move := .shrinkOnly,
    serves := "the owner's `fix all ∨ True` (item 394)",
    moves := "every `∨ True` / `∨ PackAlt _` / `∨ PackAltG _` position in an authored type retired: paid (the alternative made a real obligation), deleted, or restated; ON-path first (`CapstonePathAudit.on`), then OFF",
    basis := "item 395 (`OrTrueAudit`: the roster the retirement lane works from; shrink-only, a new position needs the owner's word)" },
  { census := "OrTrueAudit", pin := "expectedSummary", field := "PackAlt", goal := .zero, move := .shrinkOnly,
    serves := "Rule 8: `PackAlt sc` is `True` under a name (item 311)",
    moves := "the pack lane: births paid at the producers (`entryKeyPack_of_dispatch`, `entryPropsKeyPack_of_dispatch`, `content_dispatch_routed`), then the park fields and their relays",
    basis := "items 311 / 395" },
  { census := "OrTrueAudit", pin := "expectedSummary", field := "PackAltG", goal := .zero, move := .shrinkOnly,
    serves := "Rule 8: `PackAltG g` is `True` under a name",
    moves := "the five `PackAltG` conclusions (item 511's roster), each a conclusion narrowing with its relay damage priced first",
    basis := "items 311 / 511" },
  { census := "OrTrueAudit", pin := "expectedSummary", field := "conclusions", goal := .zero, move := .shrinkOnly,
    serves := "a conclusion `Or.inr trivial` proves is not an obligation (§8)",
    moves := "narrow each `… ∨ True` conclusion to its residue (`lake run restate -- narrow-conclusion` prices the relay damage first, item 228)",
    basis := "items 227 / 228 / 395" },
  { census := "OrTrueAudit", pin := "expectedSummary", field := "inrTrivial", goal := .zero, move := .shrinkOnly,
    serves := "the `Or.inr trivial` writes — the vacuous arms taken",
    moves := "falls as positions are paid: a paid position leaves its writers nothing vacuous to write",
    basis := "item 395" },
  { census := "OrTrueAudit", pin := "expectedSummary", field := "unresolved", goal := .zero, move := .shrinkOnly,
    serves := "supply the census could not class",
    moves := "read each unresolved supplier (a pipe the walker does not see through) and teach the census the shape or restate the site",
    basis := "item 395 (`supply: … unresolved=`)" },
  -- The pack lane's own residue.
  { census := "BlockDeferralClasses", pin := "expectedPackBirths", field := "entryKeyPack_of_dispatch", goal := .zero, move := .shrinkOnly,
    serves := "the pack producers' `PackAlt` writes (`lake run check-pack-births`)",
    moves := "(d) births: the dedent arms pay through `markedCols_le_of_top` (item 498), the root births through the root closing lemma (item 508), the compact births through the `[map k]` resume fact (item 494)",
    basis := "items 431 / 500 / 512 (`a+b` = writes at the entry producer + its props twin's shared helper)" },
  { census := "BlockDeferralClasses", pin := "expectedPackBirths", field := "entryPropsKeyPack_of_dispatch", goal := .zero, move := .shrinkOnly,
    serves := "the pack producers' `PackAlt` writes", moves := "as `entryKeyPack_of_dispatch`", basis := "items 431 / 500 / 512" },
  { census := "BlockDeferralClasses", pin := "expectedPackBirths", field := "content_dispatch_routed", goal := .zero, move := .shrinkOnly,
    serves := "the pack producers' `PackAlt` writes",
    moves := "the content dispatcher's 25 writes: each optional context (`h_keyctx`, `h_suffixctx`, `h_nodocctx`, `h_markerctx`, …) made plain at its callers",
    basis := "items 211 / 431" },
  { census := "BlockDeferralClasses", pin := "expectedPackResidue", field := "decline", goal := .zero, move := .shrinkOnly,
    serves := "the pack residue flip (`lake run pack-census -- residue`)",
    moves := "every site that DECLINES a pack (`Or.inr`) in the residue tree; paid with the positions above",
    basis := "items 340 / 357" },
  { census := "BlockDeferralClasses", pin := "expectedPackResidue", field := "uncond", goal := .zero, move := .shrinkOnly,
    serves := "the pack residue flip",
    moves := "the roots the flip must make unconditional — the producers that still hand a `PackAlt`-shaped fact down",
    basis := "items 340 / 357" },
  -- Rule 8.
  { census := "GhostIndexCensus", pin := "expectedSummary", field := "ghost", goal := .zero, move := .shrinkOnly,
    serves := "Rule 8: no ghost index on the accumulation invariant",
    moves := "re-index each `List FrameLevel` / `List Nat` / `Array Bool` / `FrameTail` binder by a projection of `sc` (item 405: `h_kslot` over `markedCols sc`, 75 → 73) or add the missing field to `ScannerState`; #327's (i) for the sequence lane's outer frames",
    basis := "item 331 (`GhostIndexCensus`: the list to shrink; nothing may join it)" },
  { census := "GhostIndexCensus", pin := "expectedSummary", field := "snapshot", goal := .zero, move := .shrinkOnly,
    serves := "Rule 8: an `Option ScannerState` carried as an index",
    moves := "replace each snapshot by the projection the consumer reads off it",
    basis := "item 331" },
  { census := "GhostIndexCensus", pin := "expectedSummary", field := "or", goal := .zero, move := .shrinkOnly,
    serves := "Rule 8: an `∨` inside a carrier field whose alternative restates state",
    moves := "falls with `OrTrueAudit.positions` — the per-field disjuncts are the same `∨ PackAlt` positions seen from the carrier",
    basis := "item 331 (`disjunct` class: the shape Rule 8 forbids)" },
  -- Rule 1.
  { census := "DeadDeclarationCensus", pin := "expectedDeadCensus", field := "B-roster", goal := .zero, move := .shrinkOnly,
    serves := "Rule 1: no theorem without a capstone",
    moves := "each roster name is deleted (item 506 deleted 87 unreached scanner facts on the owner's word) or reached by a capstone chain (`DeadDeclarationRoster.lean` lists them)",
    basis := "items 476 / 477 (`lake run dead-census -- --check`)" },
  { census := "DeadDeclarationCensus", pin := "expectedDeadCensus", field := "A-campaign", goal := .zero, move := .shrinkOnly,
    serves := "Rule 1: declarations the campaign built that no root reaches YET",
    moves := "lands when the lane's capstone chain composes them (S3's `scan_trace`, Row 19's step (3), R12's fixpoint); what is left when a lane closes moves to the (B) roster",
    basis := "item 476 (class (A) campaign in progress)" },
  { census := "DeadDeclarationCensus", pin := "expectedDeadCensus", field := "unresolved", goal := .zero, move := .shrinkOnly,
    serves := "Blueprint/04 rows whose root name resolves to no constant",
    moves := "fix the row in `Blueprint/04-capstones.md` / `scripts/blueprint-capstones.txt` or restore the constant",
    basis := "item 476 (`roots=… blueprint:N(unresolved=M)`)" },
  -- The supply / spend censuses over `StreamAccum`'s optional premises.
  { census := "RelaySupplyCensus", pin := "expectedTally", field := "DECLINE", goal := .zero, move := .shrinkOnly,
    serves := "supply of the `_ ∨ True` premises: an `Or.inr` written at the call site",
    moves := "paid when the premise's alternative is a real obligation the caller can meet; falls with `OrTrueAudit.positions`",
    basis := "item 212 (`RelaySupplyCensus`: `PAY` / `DECLINE` leaves)" },
  { census := "ArmSpendCensus", pin := "expectedTally", field := "DECLINE", goal := .zero, move := .shrinkOnly,
    serves := "spend of the loose arm conjunct at its readers",
    moves := "as `RelaySupplyCensus.DECLINE`, over the arm family",
    basis := "item 224" },
  { census := "NarrowingWorthCensus", pin := "expectedFaceTally", field := "binders", goal := .zero, move := .shrinkOnly,
    serves := "the optional (`_ ∨ True`) binder population of `StreamAccum` — the denominator items 212–226 lacked",
    moves := "each binder narrowed to a load-bearing premise or deleted; falls with `OrTrueAudit.positions`",
    basis := "item 227" },
  { census := "PremiseNecessityCensus", pin := "expectedDeadTally", field := "dead", goal := .zero, move := .shrinkOnly,
    serves := "binders no proof reads",
    moves := "the lane-stub binders of the `PackAlt` helpers go with `PackAlt`; the rest are deleted where they stand",
    basis := "item 226 (`expectedDead`: lane stubs)" },
  -- Punts: a producer declining to build what the park awaits.
  { census := "ValueLinePacks", pin := "expectedLine", field := "punt", goal := .zero, move := .shrinkOnly,
    serves := "value-line pack writers that take the option's `True` arm",
    moves := "each punt replaced by the pack (route + frames + tail) the writer holds, or by a relay of its caller's",
    basis := "items 261 / 405" },
  { census := "ValueLineOrigins", pin := "expectedLine", field := "punt", goal := .zero, move := .shrinkOnly,
    serves := "value-line pack rows whose chain is born as a punt",
    moves := "as `ValueLinePacks.punt`, read at the origin",
    basis := "item 262" },
  { census := "RouteShapes", pin := "expectedLine", field := "punt", goal := .zero, move := .shrinkOnly,
    serves := "park closure slots that punt (`∨ True` closures)",
    moves := "one re-routing lemma per spine (`SSLComments ⇒ Stream`, `SBlockNode(_+1,blockOut) ⇒ Stream`, …) spent where the closure is built",
    basis := "item 248" },
  -- The flow open under-run gate.
  { census := "ScannerFlowOpenUnderRun", pin := "expectedArmTable", field := "paid", goal := .field "cells", move := .growOnly,
    serves := "the under-run refusal at the break/EOF gate (items 66 / 172)",
    moves := "the carrier on the anchor (two declarations, `expectedWirePrice`), then each owed cell paid at its arm",
    basis := "item 172 (`cells=24 paid=N owed=M`)" },
  { census := "ScannerFlowOpenUnderRun", pin := "expectedArmTable", field := "owed", goal := .zero, move := .shrinkOnly,
    serves := "the under-run gate", moves := "as `paid`", basis := "item 172" },
  -- β.5: `SLYamlStream.scannerDrop`.
  { census := "SuffixGapAudit", pin := "expectedChain", field := "broken", goal := .zero, move := .shrinkOnly,
    serves := "β.5: the one arm whose premises connect nothing (`scannerDrop`)",
    moves := "delete the arm (Row 12's six steps); every statement in `DropDependents.T` reproved or restated first",
    basis := "item 236" },
  { census := "SuffixGapAudit", pin := "expectedChain", field := "connected", goal := .field "arms", move := .growOnly,
    serves := "every surface arm connects its source to its target", moves := "as `broken`", basis := "item 236" },
  { census := "FreeSurfaceCensus", pin := "expectedCensus", field := "free", goal := .zero, move := .shrinkOnly,
    serves := "theorems true without their hypotheses while the arm stands",
    moves := "β.5 retires the arm (15 stop being free); the `survivesBeta5` ones are restated",
    basis := "item 237" },
  { census := "FreeSurfaceCensus", pin := "expectedCensus", field := "survivesBeta5", goal := .zero, move := .shrinkOnly,
    serves := "free theorems β.5 does not fix", moves := "restate each (its conclusion holds by `rfl`)", basis := "item 237" },
  { census := "DropDependents", pin := "expectedCensus", field := "T", goal := .zero, move := .shrinkOnly,
    serves := "β.5's reproof bill: proofs running through the arm",
    moves := "each reproved without the arm (the `ParkBill` fixpoint names the ones that sorry)",
    basis := "item 238" },
  { census := "DropDependents", pin := "expectedCensus", field := "D", goal := .zero, move := .shrinkOnly,
    serves := "β.5: direct constructions of the arm", moves := "`dropClose` and `close_with_ssl`'s `pendingFlow` branch (item 239's two restatements) and the two Tests-side exhibits", basis := "item 238" },
  { census := "ParkBill", pin := "expectedFixpoint", field := "sorried", goal := .zero, move := .shrinkOnly,
    serves := "β.5's retire flip: declarations that sorry at the fixpoint",
    moves := "each a reproof under the deleted arm; `lake run flip-beta5` re-reads it",
    basis := "item 240 / `ParkBill`" },
  { census := "ParkBill", pin := "expectedArms", field := "arms", goal := .zero, move := .shrinkOnly,
    serves := "the escape still standing (`block_dispatch_deferred`)",
    moves := "empty the escape's domain (step 12.3): every input that reached it takes a named arm",
    basis := "`ParkBill.expectedArms` (`left=[block_dispatch_deferred]`)" },
  -- Coverage up to a bound.
  { census := "SurfaceSpanCensus", pin := "expectedCoverage", field := "covered", goal := .field "closure", move := .growOnly,
    serves := "the suffix law over the surface closure",
    moves := "a suffix lemma per uncovered production in `Proofs/Foundation/SurfaceSpanSupply.lean`",
    basis := "item 229" },
  { census := "SurfaceSpanCensus", pin := "expectedCoverage", field := "uncovered", goal := .zero, move := .shrinkOnly,
    serves := "the suffix law", moves := "as `covered`", basis := "item 229" },
  { census := "ColumnWalkPrice", pin := "expectedSupply", field := "withSuffixLemma", goal := .field "productions", move := .growOnly,
    serves := "suffix lemmas over the typed productions", moves := "as `SurfaceSpanCensus.covered`", basis := "item 235" },
  { census := "ColumnWalkPrice", pin := "expectedSupply", field := "missing", goal := .zero, move := .shrinkOnly,
    serves := "suffix lemmas", moves := "as `SurfaceSpanCensus.covered`", basis := "item 235" },
  -- Rule 9.
  { census := "scripts-ledger", pin := "open", field := "rows", goal := .zero, move := .shrinkOnly,
    serves := "Rule 9: scripts are Lean",
    moves := "port each `todo` row to a `lean_exe` (plan `Blueprint/09-scripts-in-lean.md`); an `exception` row needs the owner's reason",
    basis := "Rule 9 (PR #193); `lake run check-scripts-lean` (shrink-only pin `# open: N`)" },
  -- Holds: readings at their goal that a guard keeps there.
  { census := "GateVocabulary", pin := "expectedGateVocab", field := "unresolved", goal := .zero, move := .hold,
    serves := "every gate name the prose cites resolves", moves := "`lake run check-gate-vocab` keeps it at 0", basis := "items 265 / 266" },
  { census := "OpenerFallbackReach", pin := "expectedSummary", field := "fallback", goal := .zero, move := .hold,
    serves := "the openers' catch-all route arm is unreachable", moves := "the guard keeps it at 0", basis := "item 375" },
  { census := "ColumnAdvanceCensus", pin := "expectedSplit", field := "violations", goal := .const 1, move := .hold,
    serves := "the column law is false and ONE arm refutes it (`SLDocumentPrefix.bom`)", moves := "a second violation is a finding, not a count to chase", basis := "item 234" },
  { census := "SuffixGapAudit", pin := "expectedSplit", field := "refuted", goal := .const 1, move := .hold,
    serves := "`[211] l-yaml-stream` has no suffix lemma because the statement is false", moves := "β.5 (see `broken`)", basis := "item 235 / 236" },
  -- Item 518: the readings whose guard states a direction, moved onto the roster.
  -- CapstonePathAudit by class (components of `on` / `off`).
  { census := "CapstonePathAudit", pin := "expectedSummary", field := "unresolved", goal := .zero, move := .shrinkOnly,
    serves := "positions the capstone-path classifier cannot class ON or OFF", moves := "read each (a nested position the walker does not follow) and teach the classifier the shape, or restate the site", basis := "item 439 (`unresolved` is the classifier's own refusal)" },
  { census := "CapstonePathAudit", pin := "expectedSummary", field := "on-drop", goal := .zero, move := .shrinkOnly, component := true,
    serves := "ON positions at the on-drop producers' `else` arms", moves := "R12 (d): the dedent `else` arms pay from `markedCols_le_of_top` and the `[map k]` resume fact", basis := "items 439 / 493 / 498" },
  { census := "CapstonePathAudit", pin := "expectedSummary", field := "on-relay", goal := .zero, move := .shrinkOnly, component := true,
    serves := "ON positions relayed into the three park fields", moves := "mechanical once the fields are plain (the (2b) fixpoint's 120 relays)", basis := "items 439 / 501" },
  { census := "CapstonePathAudit", pin := "expectedSummary", field := "on-via", goal := .zero, move := .hold, component := true,
    serves := "ON positions supplied through a `VIA` lemma", moves := "none today; one appearing needs the owner's word", basis := "item 439" },
  { census := "CapstonePathAudit", pin := "expectedSummary", field := "on-conclusion", goal := .zero, move := .hold, component := true,
    serves := "ON conclusions `Or.inr trivial` proves", moves := "none today", basis := "item 439" },
  { census := "CapstonePathAudit", pin := "expectedSummary", field := "off-unread", goal := .zero, move := .shrinkOnly, component := true,
    serves := "OFF positions whose alternative no consumer reads", moves := "delete the alternative where it stands (nothing spends it)", basis := "item 439" },
  { census := "CapstonePathAudit", pin := "expectedSummary", field := "off-conclusion", goal := .zero, move := .shrinkOnly, component := true,
    serves := "OFF conclusions", moves := "narrow to the residue (`lake run restate -- narrow-conclusion` prices the relay damage first)", basis := "items 228 / 439" },
  { census := "CapstonePathAudit", pin := "expectedSummary", field := "off-honest", goal := .zero, move := .shrinkOnly, component := true,
    serves := "OFF positions with an honest decline today", moves := "each paid by its own item after ON closes", basis := "item 439" },
  -- OrTrueAudit by alternative and by depth (components of `positions`), and its own holds.
  { census := "OrTrueAudit", pin := "expectedSummary", field := "True", goal := .zero, move := .shrinkOnly, component := true,
    serves := "positions whose alternative is the literal `True`", moves := "as `positions`", basis := "item 395" },
  { census := "OrTrueAudit", pin := "expectedSummary", field := "top", goal := .zero, move := .shrinkOnly, component := true,
    serves := "top-level `∨` positions", moves := "as `positions`", basis := "item 395" },
  { census := "OrTrueAudit", pin := "expectedSummary", field := "nested", goal := .zero, move := .shrinkOnly, component := true,
    serves := "nested `∨` positions (inside `∀` / `∃` / `∧`)", moves := "as `positions`", basis := "item 395" },
  { census := "OrTrueAudit", pin := "expectedSummary", field := "unreadable", goal := .zero, move := .shrinkOnly,
    serves := "consumers the audit cannot read (instrument blindness)", moves := "teach the walker the shape (Rule 9 instrument item) — the owner's call whether this is owed", basis := "item 395 (`consumers: … unreadable=`)" },
  { census := "OrTrueAudit", pin := "expectedSummary", field := "declined-only", goal := .zero, move := .hold,
    serves := "a position every supplier declines", moves := "the guard keeps it at 0", basis := "item 395" },
  { census := "OrTrueAudit", pin := "expectedSummary", field := "never-supplied", goal := .zero, move := .hold,
    serves := "a position no caller supplies", moves := "the guard keeps it at 0 (item 396 deleted the last)", basis := "items 395 / 396" },
  { census := "OrTrueAudit", pin := "expectedSummary", field := "unused", goal := .zero, move := .hold,
    serves := "a consumer that takes the alternative and never reads it", moves := "the guard keeps it at 0", basis := "item 395" },
  -- The pack flip (the residue's twin, taken by flipping `PackAlt` to `False`).
  { census := "BlockDeferralClasses", pin := "expectedPackFlip", field := "decline", goal := .zero, move := .shrinkOnly, component := true,
    serves := "the pack flip: sites that decline the pack", moves := "as `expectedPackResidue.decline` — \"this line is what each lane drives down\"", basis := "items 312 / 340" },
  { census := "BlockDeferralClasses", pin := "expectedPackFlip", field := "uncond", goal := .zero, move := .shrinkOnly, component := true,
    serves := "the pack flip: roots to make unconditional", moves := "as `expectedPackResidue.uncond`", basis := "items 312 / 340" },
  { census := "BlockDeferralClasses", pin := "expectedPackFlip", field := "relay", goal := .zero, move := .hold,
    serves := "the pack flip: relays of a `PackAlt` the `False` flip still sees", moves := "the flip keeps it at 0", basis := "items 312 / 340" },
  { census := "BlockDeferralClasses", pin := "expectedPackResidue", field := "relayState", goal := .zero, move := .shrinkOnly,
    serves := "the residue's transports", moves := "as `expectedPackFlip.relayState`", basis := "item 357" },
  { census := "BlockDeferralClasses", pin := "expectedInlineArms", field := "apps", goal := .zero, move := .shrinkOnly,
    serves := "step 12.3: the inline escape's remaining applications (two `noKeyContext` arms and the dead one)", moves := "empty the escape's domain: each input that reaches it takes a named arm", basis := "items 286 / 297" },
  { census := "BlockDeferralClasses", pin := "expectedInlineCensus", field := "nokey", goal := .zero, move := .hold,
    serves := "accepted inputs the inline class keys nothing for", moves := "the census keeps it at 0", basis := "item 286" },
  -- The openers' optional contexts.
  { census := "OpenerFallbackReach", pin := "expectedSummary", field := "open", goal := .zero, move := .shrinkOnly,
    serves := "the five openers' `_ ∨ True` optional contexts (`h_res_land`, `h_sfx_land`, `h_nodoc_land`, `h_mk_land`, `h_pr_land`, …)", moves := "Row 19's step (3) explicit-only narrowing (item 494's 13 sites) and R12's (2b) fixpoint; each context made plain at its producers", basis := "items 375 / 494" },
  -- Conclusions.
  { census := "ConclusionObligationCensus", pin := "expectedLedgerTally", field := "res", goal := .zero, move := .shrinkOnly,
    serves := "`Or.inr trivial` written in the ledger lemmas' conclusions", moves := "narrow each conclusion to its residue (item 228: price the relay damage first; `res` 123 → 58 was the lane's own direction)", basis := "items 227 / 228" },
  { census := "ConclusionObligationCensus", pin := "expectedResidueProbe", field := "byTrivial", goal := .zero, move := .hold,
    serves := "a narrowed residue that `trivial` still proves", moves := "the probe keeps it at 0", basis := "item 228 §2b" },
  { census := "NarrowingWorthCensus", pin := "expectedNoopTally", field := "byElab", goal := .zero, move := .shrinkOnly,
    serves := "theorems whose conclusion is a no-op (provable without its hypotheses, §8)", moves := "restate or delete each (16 stand; none added since item 227)", basis := "item 227 (`expectedNoopTally`)" },
  { census := "NarrowingWorthCensus", pin := "expectedHiddenTally", field := "hiddenOnly", goal := .zero, move := .shrinkOnly,
    serves := "optional binders hidden behind a definition the syntactic selector misses", moves := "unfold the definition at the selector (instrument) or restate the binder", basis := "item 227 §6" },
  { census := "NarrowingWorthCensus", pin := "expectedWorthTally", field := "chainSplits", goal := .zero, move := .hold,
    serves := "arms a narrowing would collapse on a premise still unconditionally inhabited (a narrowing that buys nothing)", moves := "the census keeps it at 0", basis := "item 227 §5" },
  -- β.5's bill, the remaining counts.
  { census := "DropDependents", pin := "expectedCensus", field := "capstonesInT", goal := .zero, move := .shrinkOnly, component := true,
    serves := "capstones whose proofs run through `scannerDrop`", moves := "β.5: the two capstones reproved without the arm", basis := "item 238" },
  { census := "DropDependents", pin := "expectedCensus", field := "S", goal := .zero, move := .hold,
    serves := "statements that NAME the arm", moves := "the census keeps it at 0 (a name appearing would make the deletion a restatement)", basis := "item 238" },
  { census := "DropDependents", pin := "expectedWideCensus", field := "T", goal := .zero, move := .shrinkOnly, component := true,
    serves := "the whole-tree twin of `T` (`lake run drop-sweep`)", moves := "as `expectedCensus.T`", basis := "item 238" },
  { census := "ParkBill", pin := "expectedBill", field := "Tp", goal := .zero, move := .shrinkOnly,
    serves := "β.5's park bill: proofs running through `PendingNode.pendingFlow`", moves := "retire the park with the arm; each reproved", basis := "item 240 / `ParkBill`" },
  { census := "ParkBill", pin := "expectedBill", field := "Dp", goal := .zero, move := .shrinkOnly, component := true,
    serves := "direct constructions of the park", moves := "as `Tp`", basis := "item 240" },
  { census := "ParkBill", pin := "expectedBill", field := "capstonesInTp", goal := .zero, move := .shrinkOnly, component := true,
    serves := "capstones riding the park", moves := "as `Tp`", basis := "item 240" },
  { census := "ParkBill", pin := "expectedBill", field := "Sp", goal := .zero, move := .hold,
    serves := "statements that name the park (the twin of `S=0`)", moves := "the census keeps it at 0", basis := "item 240" },
  { census := "ParkBill", pin := "expectedFixpoint", field := "carried", goal := .zero, move := .shrinkOnly,
    serves := "sorries the retire flip carries through its waves", moves := "as `sorried`", basis := "`ParkBill.expectedFixpoint`" },
  { census := "ParkBill", pin := "expectedFixpoint", field := "refused", goal := .zero, move := .hold,
    serves := "patches the flip refused", moves := "the flip keeps it at 0", basis := "`ParkBill.expectedFixpoint`" },
  -- Supply leaves.
  { census := "RelaySupplyCensus", pin := "expectedSplitLanding", field := "DECLINE", goal := .zero, move := .shrinkOnly,
    serves := "the leaves of `SPLIT` edges that decline (not counted by `expectedTally.DECLINE`, which reads top-level edges)", moves := "pay each leaf or hand its hypothesis back; falls with the `PackAlt` positions", basis := "item 216" },
  { census := "RelaySupplyCensus", pin := "expectedSplitBranch", field := "DECLINE-closed", goal := .zero, move := .shrinkOnly, component := true,
    serves := "declines closed with `trivial`", moves := "pay or hand the hypothesis back (`DECLINE-free`), then pay", basis := "item 314" },
  { census := "RelaySupplyCensus", pin := "expectedSplitBranch", field := "DECLINE-free", goal := .zero, move := .shrinkOnly, component := true,
    serves := "declines that hand their hypothesis back (relays of a `PackAlt`)", moves := "falls with the `PackAlt` positions", basis := "item 314" },
  { census := "RelaySupplyCensus", pin := "expectedSplitBranch", field := "disagree", goal := .zero, move := .hold,
    serves := "the two split readings disagree", moves := "the census keeps it at 0", basis := "item 216" },
  { census := "RelaySupplyCensus", pin := "expectedDeclineReach", field := "dead", goal := .zero, move := .hold,
    serves := "decline pairs no live split reaches", moves := "the census keeps it at 0", basis := "item 217" },
  -- Holds the guards' text names as the number kept at zero / the check kept true.
  { census := "SurfaceSpanCensus", pin := "expectedRefuters", field := "elsewhere", goal := .zero, move := .hold,
    serves := "`BreakBetween` mentions outside the two residue modules", moves := "\"the number this section exists to keep at zero\"", basis := "item 229 §4" },
  { census := "SurfaceSpanCensus", pin := "expectedLeafSplit", field := "blocked", goal := .zero, move := .hold,
    serves := "dead leaf sites with no route", moves := "the census keeps it at 0", basis := "item 229 §5" },
  { census := "SurfaceSpanCensus", pin := "expectedMotiveExport", field := "trueOnly", goal := .zero, move := .hold,
    serves := "recursor motives exporting only `True`", moves := "the census keeps it at 0", basis := "items 231 / 232" },
  { census := "ColumnAdvanceCensus", pin := "expectedCoverage", field := "blind", goal := .zero, move := .hold,
    serves := "arms the column census could not relate (a census reporting no violation must see its population)", moves := "the census keeps it at 0", basis := "item 234" },
  { census := "ColumnAdvanceCensus", pin := "expectedConsumeAllUsers", field := "value", goal := .zero, move := .hold,
    serves := "applications of `GConsumeAll` outside its generated machinery (the arm that could break the column law)", moves := "the guard keeps it at 0", basis := "item 234 §4" },
  { census := "ColumnWalkPrice", pin := "expectedSupply", field := "documentLayerMissing", goal := .const 1, move := .hold,
    serves := "`[211]`'s missing document-layer suffix lemma (the statement is false)", moves := "β.5 (see `SuffixGapAudit.refuted`)", basis := "items 235 / 236" },
  { census := "ProducerDerivation", pin := "expectedCensus", field := "free", goal := .zero, move := .hold,
    serves := "correspondence hypotheses that are free", moves := "the census keeps it at 0", basis := "item 241" },
  { census := "StreamCompositions", pin := "expectedLine", field := "viaSites", goal := .zero, move := .hold,
    serves := "build points reached only through a `VIA`", moves := "the census keeps it at 0", basis := "item 249" },
  { census := "CarrierArmPrice", pin := "expectedSpend", field := "drop", goal := .flag "false", move := .hold,
    serves := "non-circularity: the closing lemma routes through no escape", moves := "the check keeps it `false`", basis := "items 242–245" },
  { census := "ParkGapCensus", pin := "expectedSpend", field := "drop", goal := .flag "false", move := .hold,
    serves := "non-circularity of the connected-drop closure", moves := "the check keeps it `false`", basis := "item 243" },
  { census := "ParkGapWidth", pin := "expectedSpend", field := "drop", goal := .flag "false", move := .hold,
    serves := "non-circularity of the width proofs", moves := "the check keeps it `false`", basis := "item 244" },
  { census := "ParkGapProduction", pin := "expectedSpend", field := "drop", goal := .flag "false", move := .hold,
    serves := "non-circularity of the literal's production", moves := "the check keeps it `false`", basis := "item 245" },
  { census := "DispatchPrice", pin := "expectedWeak", field := "drop", goal := .flag "false", move := .hold,
    serves := "the weak repair's statement routes through no escape", moves := "the check keeps it `false`", basis := "item 242" }
]

/-! ## Readings -/

/-- A pin as read: `census.pin` and its literal. -/
structure Pin where
  census : String
  name : String
  literal : String
  deriving Repr, Inhabited

/-- Every `def expected…` of one guard file, with its literal (pins whose literal is not a string
    or a `Nat` — `List String`, `List Name` — are skipped). -/
def readPins (census text : String) : Array Pin :=
  (pinNames text).filterMap fun n => (pinLiteral? text n).map fun lit => { census, name := n, literal := lit }

#guard (readPins "X" "def expectedA : String :=\n  \"k=1\"\ndef expectedL : List String := [\"a\"]\n").map (·.name) == #["expectedA"]

/-- `(now, goal)` of a target against its pin's fields; `none` when the pin or the field is missing
    or not a count (the `--check` failure). -/
def resolve (pins : Array Pin) (t : Target) : Except String (String × Nat × Nat) := do
  let some p := pins.find? (fun p => p.census == t.census && p.name == t.pin)
    | throw s!"{t.census}.{t.pin}: no such pin"
  let fs := pinFields p.literal
  let some (_, v) := fs.find? (·.1 == t.field) | throw s!"{t.census}.{t.pin}: no field `{t.field}`"
  if let .flag want := t.goal then
    return (v, if v == want then 0 else 1, 0)
  let some now := count? v | throw s!"{t.census}.{t.pin}.{t.field}: `{v}` is not a count"
  let goal ← match t.goal with
    | .zero => pure 0
    | .const n => pure n
    | .field g =>
      let some (_, gv) := fs.find? (·.1 == g) | throw s!"{t.census}.{t.pin}: no bound field `{g}`"
      let some n := count? gv | throw s!"{t.census}.{t.pin}.{g}: `{gv}` is not a count"
      pure n
    | .flag _ => pure 0
  return (v, now, goal)

def distance (now goal : Nat) : Nat := if now ≥ goal then now - goal else goal - now

/-- One resolved row. -/
structure Row where
  target : Target
  /-- the reading as the pin spells it (`false`, `7+2`, `10/24`) -/
  nowText : String
  now : Nat
  goal : Nat
  deriving Repr, Inhabited

def Row.left (r : Row) : Nat := distance r.now r.goal

def Row.goalText (r : Row) : String :=
  match r.target.goal with
  | .zero => "0"
  | .const n => s!"{n}"
  | .field g => s!"{r.goal} (= `{g}`)"
  | .flag v => s!"`{v}`"

def Row.status (r : Row) : String :=
  if r.left == 0 then (if r.target.move == .hold then "HOLD" else "DONE") else "OPEN"

/-- Resolve the roster: the rows that resolve and the errors for those that do not. -/
def resolveAll (pins : Array Pin) : Array Row × Array String := Id.run do
  let mut rows := #[]
  let mut errs := #[]
  for t in roster do
    match resolve pins t with
    | .ok (nowText, now, goal) => rows := rows.push { target := t, nowText, now, goal }
    | .error e => errs := errs.push e
  return (rows, errs)

/-- `|` and line breaks made safe inside a Markdown cell. -/
def cell (s : String) : String :=
  (s.replace "|" "\\|").replace "\n" " "

/-- The directed table. -/
def renderRows (rows : Array Row) : Array String := Id.run do
  let mut out := #["| census | field | now | goal | left | move | status | serves | what moves it | basis |",
                   "|---|---|---:|---:|---:|---|---|---|---|---|"]
  for r in rows do
    let field := if r.target.component then s!"`{r.target.field}` ⊂" else s!"`{r.target.field}`"
    out := out.push s!"| `{r.target.census}` | {field} | {r.nowText} | {r.goalText} | {r.left} | {r.target.move.render} | {r.status} | {cell r.target.serves} | {cell r.target.moves} | {cell r.target.basis} |"
  return out

/-- The census-level distance: open rows and the sum of what is left (holds excluded). -/
def totals (rows : Array Row) : String :=
  let comps := rows.filter (·.target.component)
  let rows := rows.filter (!·.target.component)
  let work := rows.filter (·.target.move != .hold)
  let open_ := work.filter (·.left != 0)
  let left := open_.foldl (fun acc r => acc + r.left) 0
  s!"directed={rows.size} work={work.size} open={open_.size} done={work.size - open_.size} holds={rows.size - work.size} left={left} components={comps.size} (shown, not summed)"

/-- Every field of every pin not named by the roster, one line per pin; a `Nat` pin reads `value=N`. -/
def renderReadings (pins : Array Pin) : Array String := Id.run do
  let mut out := #[]
  for p in pins do
    let fs := pinFields p.literal
    let fs := fs.filter fun (k, v) => (count? v).isSome &&
      !(roster.any fun t => t.census == p.census && t.pin == p.name && t.field == k)
    if fs.isEmpty then continue
    let body := " ".intercalate (fs.map (fun (k, v) => s!"{k}={v}")).toList
    out := out.push s!"- `{p.census}.{p.name}`: {body}"
  return out

/-! ## Moves between two trees (`--diff REF`, DOCS item 523)

A PR moves pins; the reviewer's question is which of those moves are DIRECTED (a roster field, with
a goal — so the move is toward it or away from it) and which are POPULATION readings (the size of a
dependent set, a holder count, a thread length — one more consumer lemma is one more; no direction).
`directedMoves` / `populationMoves` answer it from the pins of the base tree and of this one. -/

/-- One directed field that moved: `left` before and after, and the verdict against its `move`. -/
structure DirMove where
  census : String
  field : String
  before : Nat
  after : Nat
  /-- the goal as the BASE tree resolved it (a `.field` goal moves with its pin) -/
  goalBefore : Nat
  goal : Nat
  move : Move
  deriving Repr, BEq, Inhabited

def DirMove.leftBefore (m : DirMove) : Nat := distance m.before m.goalBefore
def DirMove.leftAfter (m : DirMove) : Nat := distance m.after m.goal

/-- `toward` / `away` by the distance to the goal; a `hold` field that moves at all is `BROKEN`;
    `away` on a shrink-only / grow-only field is what needs the owner's word. -/
def DirMove.verdict (m : DirMove) : String :=
  match m.move with
  | .hold => "BROKEN (hold)"
  | _ => if m.leftAfter < m.leftBefore then "toward"
         else if m.leftAfter > m.leftBefore then "AWAY (owner's word)"
         else "lateral"

/-- Every roster field whose reading differs between `base` and `cur`; a field that resolves on one
    side only is reported with the side it has (`none` on the other) by `directedUnresolved`. -/
def directedMoves (base cur : Array Pin) : Array DirMove := Id.run do
  let mut out := #[]
  for t in roster do
    match resolve base t, resolve cur t with
    | .ok (_, b, gb), .ok (_, a, g) =>
      if b != a || gb != g then
        out := out.push { census := t.census, field := t.field, before := b, after := a, goalBefore := gb, goal := g, move := t.move }
    | _, _ => pure ()
  return out

/-- Roster fields that resolve on exactly one side (a pin or field born or deleted by the change). -/
def directedUnresolved (base cur : Array Pin) : Array String := Id.run do
  let mut out := #[]
  for t in roster do
    match resolve base t, resolve cur t with
    | .ok _, .error e => out := out.push s!"`{t.census}.{t.field}`: gone in this tree ({e})"
    | .error e, .ok _ => out := out.push s!"`{t.census}.{t.field}`: new in this tree ({e} on the base)"
    | _, _ => pure ()
  return out

/-- One population field that moved: `census.pin field before → after`. -/
structure PopMove where
  census : String
  pin : String
  field : String
  before : String
  after : String
  deriving Repr, BEq, Inhabited

def isRosterField (census pin field : String) : Bool :=
  roster.any fun t => t.census == census && t.pin == pin && t.field == field

/-- Every field of every pin present on both sides whose value differs and that no roster row names;
    a pin present on one side only contributes each of its fields with `∅` on the missing side. -/
def populationMoves (base cur : Array Pin) : Array PopMove := Id.run do
  let mut out := #[]
  let find (ps : Array Pin) (c n : String) : Option Pin := ps.find? fun p => p.census == c && p.name == n
  for p in cur do
    let fa := pinFields p.literal
    match find base p.census p.name with
    | some q =>
      let fb := pinFields q.literal
      for (k, v) in fa do
        if !isRosterField p.census p.name k then
          match fb.find? (·.1 == k) with
          | some (_, w) => if v != w then out := out.push { census := p.census, pin := p.name, field := k, before := w, after := v }
          | none => out := out.push { census := p.census, pin := p.name, field := k, before := "∅", after := v }
      for (k, w) in fb do
        if !isRosterField p.census p.name k && (fa.find? (·.1 == k)).isNone then
          out := out.push { census := p.census, pin := p.name, field := k, before := w, after := "∅" }
    | none =>
      for (k, v) in fa do
        if !isRosterField p.census p.name k then
          out := out.push { census := p.census, pin := p.name, field := k, before := "∅", after := v }
  for q in base do
    if (find cur q.census q.name).isNone then
      for (k, w) in pinFields q.literal do
        if !isRosterField q.census q.name k then
          out := out.push { census := q.census, pin := q.name, field := k, before := w, after := "∅" }
  return out

#guard (populationMoves
  #[{ census := "X", name := "expectedA", literal := "a=1 b=2" }]
  #[{ census := "X", name := "expectedA", literal := "a=1 b=3 c=4" }]).map (fun m => (m.field, m.before, m.after))
  == #[("b", "2", "3"), ("c", "∅", "4")]
#guard (populationMoves
  #[{ census := "X", name := "expectedA", literal := "7" }]
  #[{ census := "X", name := "expectedA", literal := "8" }]).map (fun m => (m.field, m.before, m.after))
  == #[("value", "7", "8")]
#guard (directedMoves
  #[{ census := "OrTrueAudit", name := "expectedSummary", literal := "positions=10 inrTrivial=5" }]
  #[{ census := "OrTrueAudit", name := "expectedSummary", literal := "positions=8 inrTrivial=5" }]).map
    (fun m => (m.field, m.before, m.after, m.verdict))
  == #[("positions", 10, 8, "toward")]
-- a `.field` goal: `covered` 72/77 → 74/79 is 5 → 5 left, lateral — not 7 → 5
#guard (directedMoves
  #[{ census := "SurfaceSpanCensus", name := "expectedCoverage", literal := "closure=77 covered=72" }]
  #[{ census := "SurfaceSpanCensus", name := "expectedCoverage", literal := "closure=79 covered=74" }]).map
    (fun m => (m.field, m.leftBefore, m.leftAfter, m.verdict))
  == #[("covered", 5, 5, "lateral")]
#guard (directedMoves
  #[{ census := "OrTrueAudit", name := "expectedSummary", literal := "positions=10" }]
  #[{ census := "OrTrueAudit", name := "expectedSummary", literal := "positions=12" }]).map (·.verdict)
  == #["AWAY (owner's word)"]
#guard (populationMoves
  #[{ census := "OrTrueAudit", name := "expectedSummary", literal := "positions=10" }]
  #[{ census := "OrTrueAudit", name := "expectedSummary", literal := "positions=12" }]).size == 0

/-- The Markdown of the moves: the two-row summary a PR body opens with, then the directed table
    (goal distance before → after, verdict), then the population list. -/
def renderMoves (ref : String) (dir : Array DirMove) (unres : Array String) (pop : Array PopMove) : Array String := Id.run do
  let mut out : Array String := #[]
  out := out.push s!"## Pins moved against `{ref}`"
  out := out.push ""
  out := out.push "| kind | moved | reading |"
  out := out.push "|---|---:|---|"
  let toward := (dir.filter (·.verdict == "toward")).size
  let away := dir.size - toward
  out := out.push s!"| directed (roster fields with a goal) | {dir.size} | toward {toward}, not toward {away}{if unres.isEmpty then "" else s!", born/gone {unres.size}"} |"
  out := out.push s!"| population (readings without a target) | {pop.size} | consumer-set sizes, holder counts, thread lengths — no direction |"
  if !dir.isEmpty || !unres.isEmpty then
    out := out.push ""
    out := out.push "| census | field | before → after | goal | left before → after | move | verdict |"
    out := out.push "|---|---|---|---:|---|---|---|"
    for m in dir do
      out := out.push s!"| `{m.census}` | `{m.field}` | {m.before} → {m.after} | {if m.goalBefore == m.goal then toString m.goal else s!"{m.goalBefore} → {m.goal}"} | {m.leftBefore} → {m.leftAfter} | {m.move.render} | {m.verdict} |"
    for u in unres do out := out.push s!"- {u}"
  if !pop.isEmpty then
    out := out.push ""
    out := out.push "<details><summary>population moves</summary>"
    out := out.push ""
    for m in pop do
      out := out.push s!"- `{m.census}.{m.pin}` {m.field} {m.before} → {m.after}"
    out := out.push ""
    out := out.push "</details>"
  return out

end Scripts.Census.Dashboard
