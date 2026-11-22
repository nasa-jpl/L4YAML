module

public import L4YAML.Proofs.Production.Acceptance.Quoted
public import L4YAML.Proofs.Production.Acceptance.FlowIndicators
public import L4YAML.Proofs.Production.Acceptance.BlockIndicators

public meta import L4YAML.Scanner.Scanner
public meta import L4YAML.Proofs.Production.Acceptance.Quoted
public meta import L4YAML.Proofs.Production.Acceptance.Properties
public meta import L4YAML.Proofs.Production.Acceptance.FlowIndicators
public meta import L4YAML.Proofs.Production.Acceptance.BlockIndicators
@[expose] public section Blanket

/-! Rule-2 instantiations of the quoted-scalar acceptance lemmas: the scanner's landing
    (`content`, byte offset, column) on inputs that `SCDoubleQuotedOk` / `SCSingleQuotedOk`
    derive, and the refuting inputs the unnarrowed converse would wrongly admit. -/

namespace L4YAML.Proofs.Acceptance.Probes

open L4YAML
open L4YAML.Scanner
open L4YAML.Proofs.Acceptance

def quotedAt (scan : ScannerState → Except ScanError ScannerState) (style : ScalarStyle)
    (s : String) (flow : Bool) : Option (String × Nat × Nat) :=
  match scan { ScannerState.mk' s with flowLevel := if flow then 1 else 0 } with
  | .ok s' =>
    match s'.tokens.back? with
    | some t =>
      match t.val with
      | .scalar c st => if st == style then some (c, s'.offset, s'.col) else none
      | _ => none
    | none => none
  | .error _ => none

def dq (s : String) (flow : Bool := false) := quotedAt scanDoubleQuoted .doubleQuoted s flow
def sq (s : String) (flow : Bool := false) := quotedAt scanSingleQuoted .singleQuoted s flow

-- Double-quoted, accepted (offset = bytes consumed, col = chars consumed)
#guard dq "\"abc\"" == some ("abc", 5, 5)
#guard dq "\"\"" == some ("", 2, 2)
#guard dq "\"a b\tc\"" == some ("a b\tc", 7, 7)
#guard dq "\"\\t\\n\\\\\\\"\"" == some ("\t\n\\\"", 10, 10)
#guard dq "\"\\x41\\u00e9\\U0001F600\"" == some ("Aé😀", 22, 22)
#guard dq "\"é\"" == some ("é", 4, 3)
#guard dq "\"a\"  # c" == some ("a", 3, 3)
#guard dq "\"a\": b" == some ("a", 3, 3)
#guard dq "\"a\"\nb" == some ("a", 3, 3)
#guard dq "\"a\" \t" == some ("a", 3, 3)
#guard dq "\"a\"b" true == some ("a", 3, 3)
#guard dq "\"\\ \\/\\_\\N\\L\\P\"" == some (" /\u00A0\u0085\u2028\u2029", 14, 14)
-- Double-quoted refuters of the unnarrowed converse
#guard dq "\"\x01\"" == none          -- [107] admits C0; scanner: invalidControlChar
#guard dq "\"\\uD800\"" == none        -- [60] digits only; scanner: unicodeOutOfRange
#guard dq "\"\\UFFFFFFFF\"" == none    -- [61] digits only; scanner: unicodeOutOfRange
#guard dq "\"a\"b" == none             -- block context: trailingContent

-- Single-quoted, accepted
#guard sq "'abc'" == some ("abc", 5, 5)
#guard sq "''" == some ("", 2, 2)
#guard sq "'a''b'" == some ("a'b", 6, 6)
#guard sq "'a\"b\\c'" == some ("a\"b\\c", 7, 7)
#guard sq "'é'" == some ("é", 4, 3)
#guard sq "'a' #x" == some ("a", 3, 3)
#guard sq "'a': b" == some ("a", 3, 3)
#guard sq "'a'\nb" == some ("a", 3, 3)
#guard sq "'a'b" true == some ("a", 3, 3)
#guard sq "'a b\tc'" == some ("a b\tc", 7, 7)
#guard sq "''''''" == some ("''", 6, 6)
#guard sq "'a' \t" == some ("a", 3, 3)
-- Single-quoted refuters of the unnarrowed converse
#guard sq "'\x01'" == none             -- [118] admits C0; scanner: invalidControlChar
#guard sq "'a'b" == none               -- block context: trailingContent
#guard sq "'''''" == none              -- quote-quote greed: unterminatedScalar
#guard sq "''''" == some ("'", 4, 4)   -- [120] derives `''` at offset 2; scanner lands at 4

-- The block-context trailing hypothesis
#guard TrailingOk "  # c".toList
#guard TrailingOk ": b".toList
#guard TrailingOk "\nb".toList
#guard TrailingOk " \t".toList
#guard TrailingOk "".toList
#guard !TrailingOk "b".toList
#guard !TrailingOk " x".toList

-- Multi-line: `quotedAtInd` sets the block indentation floor the scanner folds against.
def quotedAtInd (scan : ScannerState → Except ScanError ScannerState) (style : ScalarStyle)
    (s : String) (flow : Bool) (indent : Int) : Option (String × Nat × Nat) :=
  let base := ScannerState.mk' s
  let entry : IndentEntry := { column := indent, isSequence := false }
  match scan { base with flowLevel := if flow then 1 else 0, indents := base.indents.push entry } with
  | .ok s' =>
    match s'.tokens.back? with
    | some t =>
      match t.val with
      | .scalar c st => if st == style then some (c, s'.offset, s'.col) else none
      | _ => none
    | none => none
  | .error _ => none

def dqi (s : String) (indent : Int) (flow : Bool := false) :=
  quotedAtInd scanDoubleQuoted .doubleQuoted s flow indent
def sqi (s : String) (indent : Int) (flow : Bool := false) :=
  quotedAtInd scanSingleQuoted .singleQuoted s flow indent

-- Double-quoted multi-line, accepted (`SCDoubleQuotedMultiOk n`, `n` above the floor)
#guard dq "\"a\nb\"" == some ("a b", 5, 2)
#guard dq "\"a\n\nb\"" == some ("a\nb", 6, 2)
#guard dq "\"a\n  \n\t\n b\"" == some ("a\n\nb", 11, 3)
#guard dq "\"a \n  b\"" == some ("a b", 8, 4)
#guard dq "\"a\\\n  b\"" == some ("ab", 8, 4)
#guard dq "\"a\\\n\n  b\"" == some ("a\nb", 9, 4)
#guard dq "\"a\n...\"" == some ("a ...", 7, 4)
#guard dq "\"a\r\nb\"" == some ("a b", 6, 2)
#guard dq "\"a\rb\"" == some ("a b", 5, 2)
#guard dqi "\"a\n  b\"" 1 == some ("a b", 7, 4)
#guard dqi "\"a\n \tb\"" 0 == some ("a b", 7, 4)
#guard dqi "\"a\n\n  b\"" 0 true == some ("a\nb", 8, 4)
-- Double-quoted multi-line, refuted without the narrowing
#guard dq "\"a\n---\nb\"" == none        -- document marker at the landing
#guard dqi "\"a\nb\"" 0 == none            -- continuation does not clear the floor
#guard dqi "\"a\n\tb\"" 1 == none          -- tab in indentation under the floor
#guard dqi "\"a\n\nb\"" 0 true == none      -- same floor in flow context

-- Single-quoted multi-line, accepted (`SCSingleQuotedMultiOk n`)
#guard sq "'a\nb'" == some ("a b", 5, 2)
#guard sq "'a\n\nb'" == some ("a\nb", 6, 2)
#guard sq "'a\n  \n\t\n b'" == some ("a\n\nb", 11, 3)
#guard sq "'a \n  b'" == some ("a b", 8, 4)
#guard sq "'a\n...'" == some ("a ...", 7, 4)
#guard sq "'a\r\nb'" == some ("a b", 6, 2)
#guard sq "'a\rb'" == some ("a b", 5, 2)
#guard sq "'a\n b''c'" == some ("a b'c", 9, 6)
#guard sqi "'a\n  b'" 1 == some ("a b", 7, 4)
#guard sqi "'a\n \tb'" 0 == some ("a b", 7, 4)
#guard sqi "'a\n\n  b'" 0 true == some ("a\nb", 8, 4)
-- Single-quoted multi-line, refuted without the narrowing
#guard sq "'a\n---\nb'" == none
#guard sqi "'a\nb'" 0 == none
#guard sqi "'a\n\tb'" 1 == none
#guard sqi "'a\n\nb'" 0 true == none

/-! ## Plain scalars, one line (`Acceptance/Plain.lean`)

`pln s` is the scanner's landing `(content, offset, col)`; `scanPlainScalar` never fails in
block context, it stops. Accepted inputs land at the end of the derivation's trailing white
run with the trimmed content; the refuters show where `[133]` derives further. -/
def pln (s : String) (flow : Bool := false) := quotedAt scanPlainScalar .plain s flow

#guard pln "a b" == some ("a b", 3, 3)
#guard pln "a#c" == some ("a#c", 3, 3)
#guard pln "a:b" == some ("a:b", 3, 3)
#guard pln "a,b" == some ("a,b", 3, 3)
#guard pln "a\t b" == some ("a\t b", 4, 4)
#guard pln "-a" == some ("-a", 2, 2)
#guard pln "- a" == some ("- a", 3, 3)
#guard pln ":a" == some (":a", 2, 2)
#guard pln "? a" == some ("? a", 3, 3)
#guard pln "a :b" == some ("a :b", 4, 4)
#guard pln "a: b" == some ("a", 1, 1)
#guard pln "a,b" true == some ("a", 1, 1)
#guard pln "a]b" true == some ("a", 1, 1)
-- Trailing whites are consumed and trimmed: the landing is after the white run.
#guard pln "a  " == some ("a", 3, 3)
#guard pln "a \t" == some ("a", 3, 3)
-- `[132]`'s `hash` entry needs an empty `s-white*`: ` #` is a comment for grammar and scanner alike.
#guard pln "a #b" == some ("a", 2, 2)
#guard pln "a #c" == some ("a", 2, 2)
-- `[130]` via `isNsChar` and the scanner agree on C0: both stop before `\x01`.
#guard pln "a\x01b" == some ("a", 1, 1)
-- Refuter: `[126] dashSafe` derives `---`; at col 0 the scanner sees a document marker
-- (`atDocumentBoundary`) and emits an empty plain scalar without moving.
#guard pln "---" == some ("", 0, 0)
#guard pln "--- x" == some ("", 0, 0)
#guard pln "... x" == some ("", 0, 0)
#guard pln "---x" == some ("---x", 4, 4)

/-! ## Plain scalars, multi-line (`scanPlainScalar_accepts_multi`)

Block-context `[134]`/`[135]` folds: a single break folds to a space, `k` blank lines to `k`
line feeds; trailing whites before the break are dropped; the landing after the break is a
maximal white run and may use tabs.  Refuters: `#` on the continuation line (`[130]` admits it
after the `[69]` prefix; the scanner rolls back to the break), a document marker, a landing
below the content indent, and a break with nothing after it (the scanner rolls back). -/

def plnI (s : String) (indent : Int) (flow : Bool := false) :=
  quotedAtInd scanPlainScalar .plain s flow indent

#guard pln "a\n b" == some ("a b", 4, 2)
#guard pln "a\nb" == some ("a b", 3, 1)
#guard pln "a\n\n b" == some ("a\nb", 5, 2)
#guard pln "a\n b\n c" == some ("a b c", 7, 2)
#guard pln "a\n  b\n c" == some ("a b c", 8, 2)
#guard pln "a \n b" == some ("a b", 5, 2)
#guard pln "a\t\n b" == some ("a b", 5, 2)
#guard pln "a\r\n b" == some ("a b", 5, 2)
#guard pln "a\n \n b" == some ("a\nb", 6, 2)
#guard pln "a\n b\n\n\n c" == some ("a b\n\nc", 9, 2)
#guard pln "a\n\tb" == some ("a b", 4, 2)
#guard pln "a\n \tb" == some ("a b", 5, 3)
#guard pln "a\n b: c" == some ("a b", 4, 2)
#guard pln "a\n b #c" == some ("a b", 5, 3)
#guard pln "a\n- b" == some ("a - b", 5, 3)
#guard pln "a\n -b" == some ("a -b", 5, 3)
#guard pln "a\n---x" == some ("a ---x", 6, 4)
#guard plnI "a\n  b" 1 == some ("a b", 5, 3)
#guard plnI "a\n b" 0 == some ("a b", 4, 2)
-- Refuters: `#` after the fold, document markers, under-indentation, nothing after the break.
#guard pln "a\n #c\n b" == some ("a", 1, 1)
#guard pln "a\n---\nb" == some ("a", 1, 1)
#guard pln "a\n--- \nb" == some ("a", 1, 1)
#guard pln "a\n...\nb" == some ("a", 1, 1)
#guard plnI "a\n b" 1 == some ("a", 1, 1)
#guard pln "a\n" == some ("a", 1, 1)
#guard pln "a\n  " == some ("a", 1, 1)
#guard pln "a\n b\n " == some ("a b", 4, 2)

/-! ## Plain scalars, break-terminated (`PlainBreakStopOk`)

The scanner tries the fold at every break and rolls back to the break when the next line is
under-indented, a document marker, or adds no content (EOF, `#`, `: `, an unsafe character). -/

#guard pln "a \n" == some ("a", 2, 2)
#guard pln "a\n: b" == some ("a", 1, 1)
#guard pln "a\n:" == some ("a", 1, 1)
#guard pln "a\n\x01" == some ("a", 1, 1)
#guard pln "a\n #c" == some ("a", 1, 1)
#guard pln "a\n\n#c" == some ("a", 1, 1)
#guard pln "a\n\n" == some ("a", 1, 1)
#guard pln "a\n \n" == some ("a", 1, 1)
#guard pln "a\n---" == some ("a", 1, 1)
#guard pln "a\n..." == some ("a", 1, 1)
#guard pln "a b\n#c" == some ("a b", 3, 3)
#guard plnI "a\nb" 0 == some ("a", 1, 1)
#guard plnI "a\n \tb" 1 == some ("a", 1, 1)
#guard plnI "a\n  b\n c" 1 == some ("a b", 5, 3)

/-! ## Plain scalars, multi-line in flow context (`PlainNextLineOk true`, `PlainFlowBreakStopOk`)

Same folds as block context, but under-indentation is a hard `underIndentedScalar` error (and a
tab in the indentation `tabInIndentation`), so those inputs scan to `none`; `#`, a flow
indicator, `: `, EOF or a document marker after the fold roll back to the break. -/

#guard pln "a\n b" true == some ("a b", 4, 2)
#guard pln "a\nb" true == some ("a b", 3, 1)
#guard plnI "a\n b" 0 true == some ("a b", 4, 2)
#guard plnI "a\n  b" 1 true == some ("a b", 5, 3)
#guard pln "a\n\n b" true == some ("a\nb", 5, 2)
#guard pln "a \n b" true == some ("a b", 5, 2)
#guard pln "a\n \n b" true == some ("a\nb", 6, 2)
#guard pln "a\r\n b" true == some ("a b", 5, 2)
#guard pln "a\n b," true == some ("a b", 4, 2)
#guard pln "a\n b]" true == some ("a b", 4, 2)
#guard pln "a\n b: c" true == some ("a b", 4, 2)
#guard pln "a\n\tb" true == some ("a b", 4, 2)
-- Rollbacks to the break.
#guard pln "a\n #c" true == some ("a", 1, 1)
#guard pln "a\n" true == some ("a", 1, 1)
#guard pln "a\n  " true == some ("a", 1, 1)
#guard pln "a\n," true == some ("a", 1, 1)
#guard pln "a\n]" true == some ("a", 1, 1)
#guard pln "a\n: b" true == some ("a", 1, 1)
#guard pln "a\n---\nb" true == some ("a", 1, 1)
#guard pln "a\n--- b" true == some ("a", 1, 1)
-- Hard errors (no refusal arm): the converse needs the floor hypothesis.
#guard plnI "a\nb" 0 true == none
#guard plnI "a\n b" 1 true == none
#guard plnI "a\n\tb" 0 true == none

/-! ### Node properties (`scanAnchorOrAlias_accepts`, `scanTag_accepts`) -/

def propAt (scan : ScannerState → Except ScanError ScannerState) (s : String) :
    Option (String × String × Nat × Nat) :=
  match scan (ScannerState.mk' s) with
  | .ok s' =>
    match s'.tokens.back? with
    | some t =>
      match t.val with
      | .anchor n => some ("&", n, s'.offset, s'.col)
      | .alias n => some ("*", n, s'.offset, s'.col)
      | .tag h suf => some (h, suf, s'.offset, s'.col)
      | _ => none
    | none => none
  | .error _ => none

def anc (s : String) := propAt (scanAnchorOrAlias · true) s
def ali (s : String) := propAt (scanAnchorOrAlias · false) s
def tg (s : String) := propAt scanTag s

-- Anchors: a maximal `[102] ns-anchor-char` run; `[23]` flow indicators stop it in any context.
#guard anc "&a b" == some ("&", "a", 2, 2)
#guard anc "&abc" == some ("&", "abc", 4, 4)
#guard anc "&a-b_c.d" == some ("&", "a-b_c.d", 8, 8)
#guard anc "&a,b" == some ("&", "a", 2, 2)
#guard anc "&a]b" == some ("&", "a", 2, 2)
#guard anc "&a{b" == some ("&", "a", 2, 2)
#guard anc "&a\tb" == some ("&", "a", 2, 2)
#guard anc "&a\nb" == some ("&", "a", 2, 2)
#guard anc "&a\rb" == some ("&", "a", 2, 2)
#guard anc "&é b" == some ("&", "é", 3, 2)
#guard anc "&a:b" == some ("&", "a:b", 4, 4)
#guard anc "&a#b" == some ("&", "a#b", 4, 4)
-- Non-printable and BOM stop the run (`isPrintableBool`, `c != '\uFEFF'`).
#guard anc "&a\x01b" == some ("&", "a", 2, 2)
#guard anc "&a\uFEFFb" == some ("&", "a", 2, 2)
-- Refuter of the unnarrowed `GStar`: an empty name is `emptyAnchorName`.
#guard anc "& b" == none
#guard anc "&" == none
#guard anc "&,x" == none
-- Aliases share the collector.
#guard ali "*a b" == some ("*", "a", 2, 2)
#guard ali "*abc" == some ("*", "abc", 4, 4)
#guard ali "*a,b" == some ("*", "a", 2, 2)
#guard ali "*a}b" == some ("*", "a", 2, 2)
#guard ali "*a b" == some ("*", "a", 2, 2)
#guard ali "*é" == some ("*", "é", 3, 2)
#guard ali "*a\nb" == some ("*", "a", 2, 2)
#guard ali "* b" == none
#guard ali "*" == none
#guard ali "*[a" == none

-- Tags, verbatim `[98]`: `!<` uri+ `>`; `>` is consumed.
#guard tg "!<tag:x> b" == some ("", "tag:x", 8, 8)
#guard tg "!<tag:x>b" == some ("", "tag:x", 8, 8)
#guard tg "!<a,b>" == some ("", "a,b", 6, 6)
#guard tg "!<%21>" == some ("", "%21", 6, 6)
#guard tg "!<> b" == none
#guard tg "!<tag:x" == none
#guard tg "!<tag x>" == none
-- Secondary `[91]`: `!!` then a maximal `[40] ns-tag-char` run (`,`/`[`/`]`/`{`/`}` excluded).
#guard tg "!!str b" == some ("!!", "str", 5, 5)
#guard tg "!!" == some ("!!", "", 2, 2)
#guard tg "!!a:b" == some ("!!", "a:b", 5, 5)
#guard tg "!!a,b" == some ("!!", "a", 3, 3)
#guard tg "!!%21" == some ("!!", "%21", 5, 5)
-- Named `[92]`: `!` word+ `!` then a tag-char run.
#guard tg "!e!x b" == some ("!e!", "x", 4, 4)
#guard tg "!e! b" == some ("!e!", "", 3, 3)
#guard tg "!e!a:b" == some ("!e!", "a:b", 6, 6)
#guard tg "!e!a,b" == some ("!e!", "a", 4, 4)
#guard tg "!a-b!x" == some ("!a-b!", "x", 6, 6)
-- Primary `[90]` / non-specific `[100]`: the scanner reads only `[38] ns-word-char`s here.
#guard tg "!a b" == some ("!", "a", 2, 2)
#guard tg "! b" == some ("!", "", 1, 1)
#guard tg "!" == some ("!", "", 1, 1)
#guard tg "!a,b" == some ("!", "a", 2, 2)
#guard tg "!a-b" == some ("!", "a-b", 4, 4)
-- N1b: the scanner now collects the full `[40] ns-tag-char*` suffix after the word-char
-- handle run (`%`, `:` included), as `SCNsTagProperty.primary` admits; `TagOk.primary` mirrors
-- both loops.  These three used to be refuters (the scanner stopped at `%` and `:`).
#guard tg "!%21 b" == some ("!", "%21", 4, 4)
#guard tg "!a:b" == some ("!", "a:b", 4, 4)
#guard tg "!a%21" == some ("!", "a%21", 5, 5)

/-! Flow indicators: the landing (offset, column) and the emitted token's name, with the
    token array `prev` already scanned (the `,` guard reads `lastRealTokenVal?`). -/

def tokName : YamlToken → String
  | .flowSequenceStart => "[" | .flowSequenceEnd => "]"
  | .flowMappingStart => "{" | .flowMappingEnd => "}"
  | .flowEntry => "," | _ => "?"

def indAt (scan : ScannerState → Except ScanError ScannerState) (s : String)
    (prev : Array YamlToken := #[]) : Option (String × Nat × Nat) :=
  let toks : Array (Positioned YamlToken) := prev.map (fun t => { pos := default, val := t })
  let sc : ScannerState := { ScannerState.mk' s with flowLevel := 1, tokens := toks }
  match scan sc with
  | .ok s' =>
    match s'.tokens.back? with
    | some t => if s'.tokens.size == prev.size + 1 then some (tokName t.val, s'.offset, s'.col) else none
    | none => none
  | .error _ => none

def fsq (s : String) := indAt (fun sc => .ok (scanFlowSequenceStart sc)) s
def fsqE (s : String) := indAt (fun sc => .ok (scanFlowSequenceEnd sc)) s
def fmp (s : String) := indAt (fun sc => .ok (scanFlowMappingStart sc)) s
def fmpE (s : String) := indAt (fun sc => .ok (scanFlowMappingEnd sc)) s
def fen (s : String) (prev : Array YamlToken := #[.scalar "a" .plain]) := indAt scanFlowEntry s prev

-- Brackets: total, one char, column +1
#guard fsq "[" == some ("[", 1, 1)
#guard fsq "[a, b]" == some ("[", 1, 1)
#guard fsq "[[" == some ("[", 1, 1)
#guard fsqE "]" == some ("]", 1, 1)
#guard fsqE "]]" == some ("]", 1, 1)
#guard fsqE "] # c" == some ("]", 1, 1)
#guard fmp "{" == some ("{", 1, 1)
#guard fmp "{a: b}" == some ("{", 1, 1)
#guard fmpE "}" == some ("}", 1, 1)
#guard fmpE "}\n" == some ("}", 1, 1)
-- Flow entry after a node: accepted
#guard fen "," == some (",", 1, 1)
#guard fen ", b" == some (",", 1, 1)
#guard fen ",]" == some (",", 1, 1)
#guard fen "," #[.flowSequenceEnd] == some (",", 1, 1)
#guard fen "," #[.flowMappingEnd] == some (",", 1, 1)
#guard fen "," #[.scalar "a" .doubleQuoted] == some (",", 1, 1)
#guard fen "," #[.alias "x"] == some (",", 1, 1)
#guard fen "," #[.value] == some (",", 1, 1)
#guard fen "," #[.anchor "x"] == some (",", 1, 1)
#guard fen "," #[] == some (",", 1, 1)
-- REFUTERS of the unnarrowed converse (`GLit ','` derives them; `invalidFlowEntry`)
#guard fen "," #[.flowSequenceStart] == none          -- `[,`
#guard fen "," #[.flowMappingStart] == none           -- `{,`
#guard fen "," #[.scalar "a" .plain, .flowEntry] == none  -- `[a,,`
#guard fen "," #[.flowSequenceStart, .placeholder] == none  -- placeholders are skipped
#guard fen "," #[.flowEntry, .placeholder, .placeholder] == none

/-! Block indicators `-` / `?` / `:`: the landing (offset, column), the tokens pushed (as
    names) — `scanBlockEntry`/`scanKey` may first push a virtual collection start — on a
    state at byte `off` of `s` with the given indent stack, tokens and simple-key register. -/

def blkName : YamlToken → String
  | .blockEntry => "-" | .key => "?" | .value => ":"
  | .blockSequenceStart => "[seq" | .blockMappingStart => "[map" | _ => "?"

def blkAt (scan : ScannerState → Except ScanError ScannerState) (s : String)
    (off : Nat := 0) (flow : Bool := false) (indents : Array IndentEntry := #[])
    (prev : Array YamlToken := #[]) (key : SimpleKeyState := {}) :
    Option (List String × Nat × Nat) :=
  let toks : Array (Positioned YamlToken) := prev.map (fun t => { pos := default, val := t })
  let fl : Nat := if flow then 1 else 0
  let sc : ScannerState := { ScannerState.mk' s with
    offset := off, col := off, flowLevel := fl, indents := indents, tokens := toks, simpleKey := key }
  match scan sc with
  | .ok s' => some ((s'.tokens.extract prev.size s'.tokens.size).toList.map (blkName ·.val),
      s'.offset, s'.col)
  | .error _ => none

def seqAt (c : Int) : IndentEntry := { column := c, isSequence := true }
def mapAt (c : Int) : IndentEntry := { column := c, isSequence := false }

-- `-`: block context pushes the sequence level first; flow context is bare
#guard blkAt scanBlockEntry "- a" == some (["[seq", "-"], 1, 1)
#guard blkAt scanBlockEntry "-" == some (["[seq", "-"], 1, 1)
#guard blkAt scanBlockEntry "  - a" 2 (indents := #[mapAt 0]) == some (["[seq", "-"], 3, 3)
#guard blkAt scanBlockEntry "- a" 0 (indents := #[seqAt 0]) == some (["-"], 1, 1)
#guard blkAt scanBlockEntry "- a" (flow := true) == some (["-"], 1, 1)
#guard blkAt scanBlockEntry "-\n" == some (["[seq", "-"], 1, 1)
-- REFUTERS of the bare `GLit '-'` converse (state-side hypotheses of `scanBlockEntry_accepts`)
#guard blkAt scanBlockEntry "\t- a" 1 == none                        -- §6.1 tab before `-`
#guard blkAt scanBlockEntry "\t- a" 1 (flow := true) == some (["-"], 2, 2)
#guard blkAt scanBlockEntry "- a" 0 (indents := #[mapAt 0])
    (prev := #[.blockMappingStart, .key, .scalar "k" .plain, .value, .scalar "v" .plain]) == none
                                                                    -- `invalidBareDocument`
-- `?`
#guard blkAt scanKey "? a" == some (["[map", "?"], 1, 1)
#guard blkAt scanKey "?" == some (["[map", "?"], 1, 1)
#guard blkAt scanKey "? a" 0 (indents := #[mapAt 0]) == some (["?"], 1, 1)
#guard blkAt scanKey "? a" (flow := true) == some (["?"], 1, 1)
#guard blkAt scanKey "?\tb" (flow := true) == some (["?"], 1, 1)
-- REFUTERS (`scanKeyValidate`, post-`?` tab)
#guard blkAt scanKey "\t? a" 1 == none                               -- §6.1 tab before `?`
#guard blkAt scanKey "?\tb" == none                                  -- §6.1 tab after `?`
#guard blkAt scanKey "? a" 0 (indents := #[seqAt 0]) == none         -- `trailingContent`
-- `:`
#guard blkAt scanValue ": a" == some (["[map", ":"], 1, 1)
#guard blkAt scanValue ":" (indents := #[mapAt 0]) == some ([":"], 1, 1)
#guard blkAt scanValue ": a" (flow := true) == some ([":"], 1, 1)
#guard blkAt scanValue "a: b" 1 (prev := #[.placeholder, .placeholder, .scalar "a" .plain])
    (key := { possible := true, tokenIndex := 0, pos := { line := 0, col := 0, offset := 0 } })
    == some ([":"], 2, 2)                                           -- implicit key: placeholders rewritten
#guard blkAt scanValue ":\tb" == some (["[map", ":"], 1, 1)        -- `:` above the indent: tab is `[66]`
-- REFUTERS (`scanValueValidate`, `scanValueIndentTabCheck`, `scanValueTabCheck`)
#guard blkAt scanValue ":\tb" (indents := #[mapAt 0]) == none        -- §6.1 tab after `:` at indent
#guard blkAt scanValue "\t: b" 1 == none                             -- tab in the entry's indent
#guard blkAt scanValue ": b" 0 (prev := #[.scalar "a" .plain])
    (key := { possible := true, tokenIndex := 0, pos := { line := 5, col := 0, offset := 0 } })
    == none                                                         -- key on an earlier line

/-! Block scalars: content, landing (offset, column) of `scanBlockScalar` at `indent`. -/

def blkScalar (s : String) (indent : Int := -1) : Option (String × Nat × Nat) :=
  match scanBlockScalar { ScannerState.mk' s with indents := if indent < 0 then #[] else #[{ column := indent, isSequence := false }] } with
  | .ok s' =>
    match s'.tokens.back? with
    | some t =>
      match t.val with
      | .scalar c _ => some (c, s'.offset, s'.col)
      | _ => none
    | none => none
  | .error _ => none

#guard blkScalar "|\n a\n b\n" == some ("a\nb\n", 8, 0)
#guard blkScalar "|\n a\n b" == some ("a\nb", 7, 2)  -- EOF after content
#guard blkScalar "|\n  a\n b\n" == some ("a\n", 6, 0)  -- REFUTER: [171] at n=1 derives both lines; detected indent 2 stops at ` b`
#guard blkScalar "|2\n  a\n" == some (" a\n", 7, 0)  -- explicit `2` is relative: n = max 0 (-1 + 2)
#guard blkScalar "|-\n a\n\n" == some ("a", 7, 0)  -- strip
#guard blkScalar "|+\n a\n\n" == some ("a\n\n", 7, 0)  -- keep
#guard blkScalar "|\n\n a\n" == some ("\na\n", 6, 0)  -- leading empty line
#guard blkScalar "| # c\n a\n" == some ("a\n", 9, 0)  -- comment after white
#guard blkScalar "|#c\n a\n" == none  -- REFUTER: `#` without preceding white (`expectedNewline`)
#guard blkScalar "|x\n a\n" == none  -- REFUTER: header junk (`expectedNewline`)
#guard blkScalar "|\n\ta\n" == some ("\ta\n", 5, 0)  -- tab is content at n = 0
#guard blkScalar "|\na\n---\nb" == some ("a\n", 4, 0)  -- REFUTER: [171] at n=0 derives `---`; scanner stops at the document marker
#guard blkScalar "|\n a\n# c\n" == some ("a\n", 5, 0)  -- trail comment at < n: scanner stops BEFORE it
#guard blkScalar "|\n a\n  # c\n" == some ("a\n # c\n", 11, 0)  -- comment at ≥ n is content
#guard blkScalar "|\n a\n   b\n" == some ("a\n  b\n", 10, 0)  -- more-indented line kept verbatim
#guard blkScalar "|\n a\n " == some ("a\n", 6, 1)  -- partial indent at EOF
#guard blkScalar "|\n a\n\n\n" == some ("a\n", 7, 0)  -- clip
#guard blkScalar ">\n a\n b\n" == some ("a b\n", 8, 0)  -- folded
#guard blkScalar "|\n a\n" 0 == some ("a\n", 5, 0)
#guard blkScalar "|\n  a\n b\n" 0 == some ("a\n", 6, 0)
#guard blkScalar "|\n a\n  b\n\tc\n" == none  -- REFUTER: tab where `s-indent(n)` is required (`tabInIndentation`)
#guard blkScalar "|\n  a\n\n b\n" == some ("a\n", 7, 0)  -- stop after an empty line
#guard blkScalar "|1-\n a\n" == some (" a", 7, 0)  -- explicit `1` → n = 0, strip
#guard blkScalar "|-1\n a\n" == some (" a", 7, 0)  -- indicators in either order
#guard blkScalar "|--\n a\n" == none  -- REFUTER: repeated chomping indicator
#guard blkScalar "|" == some ("", 1, 1)
#guard blkScalar "|\n" == some ("", 2, 0)
-- Header (`HeaderIndicatorsOk`/`HeaderTailOk`) and auto-detect (`AutoIndentOk`) probes.
#guard blkScalar "|\n   \n a\n" == none  -- REFUTER: blank wider than the content indent (`blockScalarIndentMismatch`)
#guard blkScalar "|\n \n  a\n" == some ("\na\n", 8, 0)  -- narrower blank is fine
#guard blkScalar "|\n\ta\n" 0 == none  -- REFUTER: tab below the minimum content indent
#guard blkScalar "|\n\n\n" == some ("\n", 4, 0)  -- all blank: clip keeps one break
#guard blkScalar "|\n  \n" == some ("\n", 5, 0)  -- all blank: indent is the widest blank
#guard blkScalar "|+\n  \n" == some ("\n", 6, 0)
#guard blkScalar "| #c\n a\n" == some ("a\n", 8, 0)  -- comment text need not be separated from `#`
#guard blkScalar "|\t\n a\n" == some ("a\n", 6, 0)  -- tab is header white
#guard blkScalar "|9\n a\n" == some ("", 3, 0)  -- explicit indent above the content: stops at once
#guard blkScalar "|0\n a\n" == none  -- REFUTER: `0` is not an indentation indicator
#guard blkScalar "|1+\n a\n" == some (" a\n", 7, 0)
#guard blkScalar ">-\n a\n b\n\n c\n" == some ("a b\nc", 13, 0)

end L4YAML.Proofs.Acceptance.Probes
