module

public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Parser.TokenGrammar
public import L4YAML.Proofs.Serialization.TokenEvents
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Parser.TokenGrammar
public meta import L4YAML.Proofs.Serialization.TokenEvents
public meta import L4YAML.Proofs.Serialization.SerializationWellFormed

/-! # The two token-event extractors disagree (Rule 2, S5 slice 2)

S5(←) (EVENTSOF-CONCEPT §9) was to connect `TokenStateOk ts :=
SerializationWellFormed (tokenEventsOf ts)` — `TokenGrammar.lean`'s own
extractor, the premise of `parseStream_accepts` — to the serialization layer's
`checkFrom {} (tokenEvents ts)` (S2's `TokenEvents.tokenEvents`), ideally by
the equality tokenEventsOf ts = tokenEvents ts.  The Rule-2 grid refutes that equality,
on scanner output and on hand-built arrays, so this file pins the gap instead
of a proof around it (capstone 7.7 `parse_iff_grammar` via S5; the connecting
lemma is blocked on the owner's ruling).

The seam is the `%TAG` handle rule:

* `tokEvents` declares every `%TAG` handle that is not a builtin
  (`¬ BuiltinTagHandle h`), immediately, and begins the document at the first
  directive;
* `tokenEvents` declares only `isNamedHandle` handles (`!word!`) and flushes
  them at the `---`, never if no `---` follows.

The **parser** registers every `%TAG` handle `prepareDocumentState` sees
(`ParseState.tagHandles`), whether or not a `---` follows — the `tokEvents`
reading.  Four shapes:

1. `"%TAG !h tag:x,2000:\n--- !h x"` — SCANNER-REACHABLE.  The scanner copies
   the `%TAG` handle `!h` without checking its closing `!`, the parser
   registers `!h`, `tokEvents` declares it, `tokenEvents` does not.  Both
   checkers accept (`!h x` scans as the non-specific tag `!` plus a scalar, so
   the handle is never used), but the traces differ:
   `[beginDocument, declareTag "!h", useTag "!"]` vs `[beginDocument, useTag "!"]`.
2. A `%TAG !h` whose handle IS used (`.tag "!h" …` — not scanner-reachable):
   parser ok, the retired checkTokenState true, `checkFrom {} (tokenEvents ts)` false.
3. A directive run with no `---` (not scanner-reachable, `directiveWithoutDocument`):
   the parser and `tokEvents` begin the document at the directive and register
   the handle; `tokenEvents` keeps it pending until `---` (never) or end of input.
4. `%TAG !a_b!` (malformed named handle, scanner-refused): `¬ BuiltinTagHandle`
   but not `isNamedHandle` — declared by one extractor, not the other.

What DOES hold on the grid — on the listed rows only (`agreeing` below), no claim is
made beyond them: the two extractors agree on each of these scanner-shaped inputs,
whose `%TAG` handles are builtin or `!word!` and whose directive runs end at `---` — `%TAG` before `---`, two `%TAG`s, a duplicated `%TAG`, a handle
redeclared after `...`, `%YAML` + `%TAG` in either order (pinned below as the
strongest true statement the grid supports). 
HISTORICAL RECORD (S5 slice 2 landed): the per-token extractor and its checker are retired —
`TokenStateOk ts := SerializationWellFormed (tokenEvents ts)` and `TG.DocStart` requires `---`
after a non-empty directive run (spec [209]).  The rows below keep the surviving extractor's
side as checks; the retired side survives as literals in comments, and the R1/R3 rows now pin
that the grammar EXCLUDES the seam (`checkTokenGrammar = false`) instead of the refutation.
-/

namespace L4YAML.Tests.Guards.TokenEventExtractors

open L4YAML L4YAML.Scanner L4YAML.TokenParser
open L4YAML.Proofs.Serialization.SerializationWellFormed

/-- S2's extractor. -/
def ev₂ (ts : Array (Positioned YamlToken)) : List Event := L4YAML.Proofs.Serialization.TokenEvents.tokenEvents ts

def scanOr (s : String) : Array (Positioned YamlToken) :=
  match scanFiltered s with | .ok ts => ts | .error _ => #[]

def parserOk (ts : Array (Positioned YamlToken)) : Bool :=
  match parseStream ts with | .ok _ => true | .error _ => false

/-- The handles the parser registers for the first document. -/
def parserHandles (ts : Array (Positioned YamlToken)) : List String :=
  match prepareDocumentState { tokens := ts, pos := 1 } with
  | .ok (_, ps) => ps.tagHandles.toList.map (·.1)
  | .error _ => []

def mk (t : YamlToken) : Positioned YamlToken := { val := t, pos := { offset := 0, line := 0, col := 0 } }

/-! ## Shape 1 — scanner-reachable: the traces differ, both checkers accept -/

def s1 : String := "%TAG !h tag:x,2000:\n--- !h x"

/- The scanner accepts `s1` and the parser accepts its tokens.
Capstone 7.7 via S5 (slice 2's refutation). -/
#guard (scanFiltered s1).isOk = true ∧ parserOk (scanOr s1) = true

/- The parser registers the unclosed handle `!h`. -/
#guard parserHandles (scanOr s1) = ["!h"]

/- `tokEvents` declares it, `tokenEvents` does not: tokenEventsOf ≠ tokenEvents
on scanner output.  Capstone 7.7 via S5 — refutes slice 2's the equality tokenEventsOf ts = tokenEvents ts. -/
#guard
    -- the retired `TokenGrammar` extractor read `[.beginDocument, .declareTag "!h", .useTag "!"]`
    ev₂ (scanOr s1) = [.beginDocument, .useTag "!"]

/- Both checkers nevertheless accept `s1` (the handle is never used). -/
#guard
    checkFrom {} (ev₂ (scanOr s1)) = true

/-! ## Shapes 2–4 — token level: verdicts differ -/

def tsA : Array (Positioned YamlToken) :=
  #[mk .streamStart, mk (.tagDirective "!h" "p"), mk .documentStart, mk (.tag "!h" "x"), mk .streamEnd]
def tsD : Array (Positioned YamlToken) :=
  #[mk .streamStart, mk (.tagDirective "!t!" "p"), mk (.tag "!t!" "x"), mk .streamEnd]
def tsD' : Array (Positioned YamlToken) :=
  #[mk .streamStart, mk (.tagDirective "!t!" "p"), mk .streamEnd]
def tsE : Array (Positioned YamlToken) :=
  #[mk .streamStart, mk (.tagDirective "!a_b!" "p"), mk .documentStart, mk (.tag "!a_b!" "x"), mk .streamEnd]

/- On A, D, E the parser and the retired checkTokenState accept and `checkFrom {} (tokenEvents ts)`
rejects: `TokenStateOk ts ↔ checkFrom {} (tokenEvents ts) = true` is false on token
arrays.  Capstone 7.7 via S5. -/
#guard
    (parserOk tsA && !checkFrom {} (ev₂ tsA)) = true ∧
    (parserOk tsD && !checkFrom {} (ev₂ tsD)) = true ∧
    (parserOk tsE && !checkFrom {} (ev₂ tsE)) = true

/- On D' both accept but `tokEvents` has begun a document before
declaring the handle while `tokenEvents` flushes the pending handle at the end of input
with no `beginDocument`. -/
#guard
    -- the retired extractor read `[.beginDocument, .declareTag "!t!"]` and accepted it too
    ev₂ tsD' = [.declareTag "!t!"] ∧ checkFrom {} (ev₂ tsD') = true

/- The parser's registration follows `tokEvents` on all four shapes. -/
#guard
    parserHandles tsA = ["!h"] ∧ parserHandles tsD = ["!t!"] ∧ parserHandles tsD' = ["!t!"] ∧
    parserHandles tsE = ["!a_b!"]

/-! ## The strongest true statement the grid supports -/

def agreeing : List String :=
  [ "", "a", "--- a\n", "--- a\n...\n--- b\n", "a\n---\nb",
    "%TAG !t! tag:x,2000:\n--- !t!a b",
    "%TAG !t! tag:x,2000:\n%TAG !u! tag:y,2000:\n--- !u!a b",
    "%TAG !t! tag:x,2000:\n%TAG !t! tag:y,2000:\n--- !t!a b",
    "%YAML 1.2\n%TAG !t! tag:x,2000:\n--- !t!a b",
    "%TAG !t! tag:x,2000:\n%YAML 1.2\n--- !t!a b",
    "%TAG !t! tag:x,2000:\n--- !t!a b\n...\n%TAG !t! tag:y,2000:\n--- !t!c d",
    "%TAG !t! tag:x,2000:\n--- !t!a b\n...\n--- !t!c d",
    "%TAG !t! tag:x,2000:\n--- a\n--- !t!b",
    "%TAG !t! tag:x,2000:\n--- !t!a\n...\n!t!b",
    "%TAG !! tag:x,2000:\n--- !!a b", "%TAG ! tag:x,2000:\n--- !a b",
    "%TAG !t! tag:x,2000:\n--- a", "--- !t!a b", "!!str a", "! a", "!<tag:x> a", "!a b",
    "&x a", "[&x a, *x]", "&x [*x]", "{&x a: *x}", "--- &x a\n...\n--- &x b", "--- &x a\n--- &x b",
    "? a", "a: !t!x", "%TAG !t! tag:x,2000:\n---\n...\n--- !t!a",
    "%TAG !t! tag:x,2000:\n--- !t!a\n---\n!t!b" ]

/- On the `%TAG`-before-`---`, duplicate-directive and redeclared-handle rows
(and the anchor/alias rows) the two extractors agree, so `TokenStateOk` and
`checkFrom {} (tokenEvents ts)` coincide there.  Capstone 7.7 via S5. -/
#guard
    agreeing.all (fun s => (scanFiltered s).isOk && (checkFrom {} (ev₂ (scanOr s)) == parserOk (scanOr s))) = true


/-! ## Ruling (c) as stated — refuted under the old `TG.DocStart`, closed by narrowing it

Restating `TokenStateOk ts := SerializationWellFormed (tokenEvents ts)` under the OLD grammar made
`parseStream_accepts` false: `TG.DocStart` admitted a directive run with no `---`, `tokenEvents`
emits `beginDocument` only at `---` and so never reset that document's anchors — the parser does.
S5 slice 2 narrowed `DocStart` to spec [209]; R1/R3 below now pin that the grammar EXCLUDES the
shape (`checkTokenGrammar = false`) while the surviving state verdict still accepts it and the
parser still refuses it — the shape is token-level only (the scanner refuses `---`-less runs). -/

def tsR1 : Array (Positioned YamlToken) :=
  #[mk .streamStart, mk .documentStart, mk (.anchor "x"), mk (.scalar "a" .plain),
    mk (.tagDirective "!t!" "p"), mk (.alias "x"), mk .streamEnd]
def tsR3 : Array (Positioned YamlToken) :=
  #[mk .streamStart, mk .documentStart, mk (.anchor "x"), mk (.scalar "a" .plain),
    mk (.versionDirective 1 2), mk (.alias "x"), mk .streamEnd]

/- R1/R3 after S5 slice 2: `checkFrom {} (tokenEvents ts)` is true and the parser refuses, but
`TokenGrammar` is now FALSE on both — `TG.DocStart` requires `---` after a non-empty directive run
(spec [209]), so the shape that refuted the restated `parseStream_accepts` under the old grammar is
outside the grammar and the lemma's premises never meet it.  (History: under the old `DocStart` both
rows had `TokenGrammar` true, and the retired per-token checker refused them.)  Capstone 7.7 via S5. -/
#guard
    (!L4YAML.Proofs.TokenGrammar.checkTokenGrammar tsR1 && checkFrom {} (ev₂ tsR1) && !parserOk tsR1) = true ∧
    (!L4YAML.Proofs.TokenGrammar.checkTokenGrammar tsR3 && checkFrom {} (ev₂ tsR3) && !parserOk tsR3) = true

/-- With `...` before the directive run (R2) or `---` after it (R4) both checkers
refuse with the parser: the seam is exactly the `---`-less directive run. -/
def tsR2 : Array (Positioned YamlToken) :=
  #[mk .streamStart, mk .documentStart, mk (.anchor "x"), mk (.scalar "a" .plain), mk .documentEnd,
    mk (.tagDirective "!t!" "p"), mk (.alias "x"), mk .streamEnd]
def tsR4 : Array (Positioned YamlToken) :=
  #[mk .streamStart, mk (.anchor "x"), mk (.scalar "a" .plain), mk (.tagDirective "!t!" "p"),
    mk .documentStart, mk (.alias "x"), mk .streamEnd]
#guard
    (!parserOk tsR2 && !checkFrom {} (ev₂ tsR2)) = true ∧
    (!parserOk tsR4 && !checkFrom {} (ev₂ tsR4)) = true

end L4YAML.Tests.Guards.TokenEventExtractors
