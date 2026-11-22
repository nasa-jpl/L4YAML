module

public import L4YAML.Scanner.Scanner

public meta import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch
public meta import L4YAML.Scanner.IndexedDispatch
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
public meta import L4YAML.Token.Token
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The completed root document, refused at the scanner (DOCS item 132)

§9.2 `[211] l-yaml-stream` admits a bare document as the stream's first or after
a `...`, and nowhere else.  A ROOT node that is already complete, followed by
content on a LATER line with no marker between them, is a second bare document
and has no derivation.  Item 119 measured that the refusal lived in the PARSER
(`StreamState.validNextToken`) and named the migration M1; this is the landing.

`scanNextToken_checkBareDocument` runs after the structural dispatch — so
`---`, `...` and directives are reached first and stay legal — and asks three
questions of the state the dispatch is about to read:

* the indent stack is the sentinel alone, so the completed node is the
  DOCUMENT's rather than an entry inside a still-open block collection (the
  dangler at an open level's own column is M2's, and §5 keeps its pins);
* the last real token COMPLETES a node — `YamlToken.completesFlowValue`, the
  set `scanNextToken_checkFlowAdjacency` already reads;
* `simpleKeyAllowed` is up.

**The third conjunct is the item's one measurement.**  "A break was crossed
since the node ended" cannot be read off the completing TOKEN: `endPos` is
populated only for the indicator tokens, so a scalar's is its own start, and a
multi-line scalar (`"a⏎b"`, `|⏎  x`) would compare as if it ended on its first
line.  The flag says it exactly: every completing scan clears
`simpleKeyAllowed` and only a line break re-arms it — which is the same reading
item 47's check makes with the flag DOWN, one dispatcher later.  §3's same-line
family is what the flag keeps out.

§1 types the check and its four passing shapes.  §2 is the refused family, by
root style and by landing kind.  §3 is the boundary — the same-line implicit
key, the plain scalar's own continuation, a property run, a marker, a comment.
§4 pins that the refusal is the SCANNER's and that its message and position are
what the parser produced.  §5 is what M1 does not reach. -/

namespace L4YAML.Tests.Guards.ScannerBareDocumentRefusal

open L4YAML L4YAML.Scanner

/-! ## §1  The check, and the four ways it stands aside -/

/-- Inside a flow collection there is no document boundary to police. -/
example (s : ScannerState) (h : s.inFlow = true) :
    scanNextToken_checkBareDocument s = .ok () := by
  simp only [scanNextToken_checkBareDocument, h, Bool.not_true, Bool.false_and,
             Bool.false_eq_true, ↓reduceIte]

/-- Resting ON an open level the completed node is an ENTRY's, not the
    document's — M2's question, not this one.  Item 145 made this the check's
    first conjunct: a block collection merely being OPEN is not enough, because
    a landing right of every level (`k:⏎␣␣"x"⏎␣␣b: 2`) is refused here. -/
example (s : ScannerState)
    (h : (s.indents.any fun e => e.column == (s.col : Int)) = true) :
    scanNextToken_checkBareDocument s = .ok () := by
  simp only [scanNextToken_checkBareDocument, h, Bool.not_true, Bool.and_false,
             Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- On the completed node's OWN line the flag is down — this is where the node
    is still readable as an implicit key. -/
example (s : ScannerState) (h : s.simpleKeyAllowed = false) :
    scanNextToken_checkBareDocument s = .ok () := by
  simp only [scanNextToken_checkBareDocument, h, Bool.and_false, Bool.false_and,
             Bool.false_eq_true, ↓reduceIte]

/-- …and with nothing completed behind the cursor there is no first document to
    have ended: properties, indicators and the markers are all excluded. -/
example (s : ScannerState)
    (h : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false) :
    scanNextToken_checkBareDocument s = .ok () := by
  unfold scanNextToken_checkBareDocument
  cases hx : lastRealTokenVal? s.tokens with
  | none => simp
  | some t => simp [h t hx]

/-- The positive shape, in full: all three conjuncts and the error is the
    parser's own, at the cursor. -/
example (s : ScannerState) (t : YamlToken)
    (h_flow : s.inFlow = false) (h_ska : s.simpleKeyAllowed = true)
    (h_ind : (s.indents.any fun e => e.column == (s.col : Int)) = false)
    (h_last : lastRealTokenVal? s.tokens = some t)
    (h_cmp : t.completesFlowValue = true) :
    scanNextToken_checkBareDocument s
      = .error (.invalidBareDocument s.line s.col) := by
  simp only [scanNextToken_checkBareDocument, h_flow, h_ska, h_ind, h_last, h_cmp,
             Bool.not_false, Bool.and_self, ↓reduceIte]

/-! ## §2  The family the check refuses -/

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok _, .ok _ => true
  | _, _ => false

/-- Both SCANNERS refuse, and so do both pipelines. -/
private def scannerRefuses (input : String) : Bool :=
  (match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
   | .error _, .error _ => true
   | _, _ => false) &&
  (match Events.streamToEvents input, Events.streamToEventsIx input with
   | .error _, .error _ => true
   | _, _ => false)

-- Every root style that can COMPLETE, against one landing.
#guard scannerRefuses "[1, 2]\nx\n"          -- flow sequence close
#guard scannerRefuses "{a: b}\nx\n"          -- flow mapping close
#guard scannerRefuses "\"q\"\nx\n"           -- double-quoted
#guard scannerRefuses "'q'\nx\n"             -- single-quoted
#guard scannerRefuses "|\n  y\nx\n"          -- literal block scalar
#guard scannerRefuses ">\n  y\nx\n"          -- folded block scalar
#guard scannerRefuses "hello\n# c\nx\n"      -- plain, stopped by a comment
#guard scannerRefuses "&p [1]\nx\n"          -- a property run does not stop it

-- …and every landing kind, against one root.
#guard scannerRefuses "[1, 2]\nx\n"
#guard scannerRefuses "[1, 2]\nx: 1\n"
#guard scannerRefuses "[1, 2]\n- y\n"
#guard scannerRefuses "[1, 2]\n? k\n"
#guard scannerRefuses "[1, 2]\n: v\n"
#guard scannerRefuses "[1, 2]\n[3]\n"
#guard scannerRefuses "[1, 2]\n{a: b}\n"
#guard scannerRefuses "[1, 2]\n\"q\"\n"
#guard scannerRefuses "[1, 2]\n|\n  x\n"
#guard scannerRefuses "[1, 2]\n&p a\n"
#guard scannerRefuses "[1, 2]\n!t x\n"
#guard scannerRefuses "[1, 2]\n  a\n"        -- indentation is no exemption

-- The completed node may span lines; the flag, not a position, decides.
#guard scannerRefuses "[1,\n 2]\nx\n"
#guard scannerRefuses "\"a\nb\"\nx\n"
#guard scannerRefuses "|\n  a\n  b\nx\n"

-- A `...` between them is what makes the second document legal, and the
-- check is what refuses the stream that omits it.
#guard accepts "[1, 2]\n...\nx\n"
#guard accepts "[1, 2]\n--- x\n"
#guard scannerRefuses "[1, 2]\n...\n[3]\nx\n"

/-! ## §3  The boundary the check must not cross -/

-- The completed node on its own line is an implicit KEY: the flag is down.
#guard emits "[1, 2]: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ",
   "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard accepts "\"x\": 1\nb: 2\n"
#guard accepts "'x': 1\n"
#guard emits "? \"x\"\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"x", "=VAL :v", "-MAP", "-DOC", "-STR"]

-- A plain scalar absorbs its own continuation lines, so it is not complete.
#guard accepts "hello\nworld\n"
#guard emits "hello\n[1]\n"
  ["+STR", "+DOC", "=VAL :hello [1]", "-DOC", "-STR"]
#guard accepts "--- a\nb\n"

-- Properties precede a node rather than completing one.
#guard emits "&p 1\nx\n"
  ["+STR", "+DOC", "=VAL &p :1 x", "-DOC", "-STR"]
#guard emits "&p\nc: 2\n"
  ["+STR", "+DOC", "+MAP &p", "=VAL :c", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "!!str\nx\n"
  ["+STR", "+DOC", "=VAL <tag:yaml.org,2002:str> :x", "-DOC", "-STR"]

-- Markers reach the structural dispatch first, and comments and the end of
-- input are not content at all.
#guard accepts "[1, 2]\n# c\n"
#guard accepts "\"x\"\n\n"
#guard accepts "|\n  y\n"
#guard accepts "[1, 2]\n...\n"

/-! ## §4  The refusal is the SCANNER's, and it says what the parser said -/

private def scanErr (input : String) : Option String :=
  match Scanner.scan input with
  | .error e => some (toString e)
  | .ok _ => none

private def scanErrIx (input : String) : Option String :=
  match Indexed.ScannerStateIx.scanIx input with
  | .error e => some (toString e)
  | .ok _ => none

private def pipeErr (input : String) : Option String :=
  match Events.streamToEvents input with
  | .error e => some (toString e)
  | .ok _ => none

private def pipeErrIx (input : String) : Option String :=
  match Events.streamToEventsIx input with
  | .error e => some (toString e)
  | .ok _ => none

/-- One message, at one position, from all four. -/
private def saysAlike (input : String) (line col : Nat) : Bool :=
  let m := some (toString (ScanError.invalidBareDocument line col))
  scanErr input == m && scanErrIx input == m
    && pipeErr input == m && pipeErrIx input == m

#guard saysAlike "[1, 2]\na\n" 1 0
#guard saysAlike "\"x\"\na\n" 1 0
#guard saysAlike "|\n  x\na\n" 2 0
#guard saysAlike "hello\n# c\nworld\n" 2 0
#guard saysAlike "[1,\n 2]\na\n" 2 0
#guard saysAlike "[1, 2]\n  a\n" 1 2
#guard saysAlike "--- \"x\"\na\n" 1 0

/-! ## §5  What M1 does not reach

    The discriminator between M1 and M2 is the indent stack: a dangler at an
    OPEN level's column has a level on it, so M1's check stands aside on every
    input below (§1's second shape).  M2 landed at item 133 and M3 at item 134,
    so all of them are the scanner's now — they stay here because they are what
    distinguishes the mechanisms, and §1's second shape is why M1 stands aside
    on every one. -/

-- M2: the dangling node at an open level's own column (item 133).
#guard scannerRefuses "a: 1\nb\n"
#guard scannerRefuses "- a\nb\n"
#guard scannerRefuses "---\na: 1\nb\n"
#guard scannerRefuses "k: [1, 2]\nb\n"
-- M3: the `-` at a mapping top's own column with the entry complete
-- (item 134) — the token behind it is an INDICATOR, not a node body, so M2
-- stands aside on these exactly as M1 does.
#guard scannerRefuses "a: 1\n- y\n"
#guard scannerRefuses "? k\n- y\n"

end L4YAML.Tests.Guards.ScannerBareDocumentRefusal

end Blanket
