/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Serialization.EventsOf

public meta import L4YAML.Proofs.Serialization.EventsOf
public meta import L4YAML.Proofs.Serialization.SerializationWellFormed
public meta import L4YAML.Proofs.Serialization.SourceEvents

@[expose] public section Blanket

/-!
# `refLex` — the executable twin of `Skeleton` (Step 5a(iii), slice 2)

A reference lexer over `List Char`, written in the shape of the grammar and
independent of `Scanner`/`IndexedScanner`: it finds where the event lexemes
(`&`, `*`, `!`, `%TAG`, `---`, `...`) are, treating quoted scalars, comments,
block-scalar bodies and plain scalars as opaque.  `eventsOf input :=
(refLex input).map eventsOfSegs`.  Soundness against `Skeleton` and the corpus
census against `parseYaml` live beside it (`EVENTSOF-CONCEPT.md` §7).
-/

namespace L4YAML.Proofs.Serialization.EventsOf

open L4YAML
open L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.SourceEvents

/-- Lexer state: column, flow depth, whether a node may start here, the
directive lines waiting for their `---`, the pending `other` run, and the
segments emitted so far. -/
structure Lx where
  col : Nat := 0
  flow : Nat := 0
  nodeStart : Bool := true
  dirs : List (List Char) := []
  other : List Char := []
  segs : Array Seg := #[]

def Lx.flush (s : Lx) : Lx :=
  if s.other.isEmpty then s
  else { s with other := [], segs := s.segs.push (.other s.other.reverse) }

def Lx.emit (s : Lx) (seg : Seg) : Lx :=
  let s := s.flush
  { s with segs := s.segs.push seg, col := colAfter s.col seg.text }

def Lx.push (s : Lx) (c : Char) : Lx :=
  { s with other := c :: s.other, col := if c = '\n' ∨ c = '\r' then 0 else s.col + 1 }

def isBreakOrEnd : List Char → Bool
  | [] => true
  | c :: _ => c = '\n' || c = '\r'

def isSpaceBreakOrEnd : List Char → Bool
  | [] => true
  | c :: _ => c = ' ' || c = '\t' || c = '\n' || c = '\r'

/-- Characters up to (not including) the end of the line. -/
def toEol : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if c = '\n' || c = '\r' then ([], c :: cs)
      else let (a, b) := toEol cs; (c :: a, b)

/-- A quoted scalar from its opening quote; `none` if unterminated. -/
def quoted (q : Char) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs =>
    if q = '"' ∧ c = '\\' then
      match cs with
      | [] => none
      | d :: ds => (quoted q ds).map fun (a, b) => (c :: d :: a, b)
    else if c = q then
      match q, cs with
      | '\'', '\'' :: ds => (quoted q ds).map fun (a, b) => (c :: c :: a, b)
      | _, _ => some ([c], cs)
    else (quoted q cs).map fun (a, b) => (c :: a, b)

/-- Indentation of a line. -/
def indentOf : List Char → Nat
  | ' ' :: cs => indentOf cs + 1
  | _ => 0

/-- Split off one line break: `\r\n`, `\r` or `\n`. -/
def splitBreak : List Char → Option (List Char × List Char)
  | '\r' :: '\n' :: rest => some (['\r', '\n'], rest)
  | '\n' :: rest => some (['\n'], rest)
  | '\r' :: rest => some (['\r'], rest)
  | _ => none

/-- Block-scalar body: following lines that are blank or indented at least
`n` (the first non-blank line fixes `n` when it is not given). -/
def blockBody (n? : Option Nat) (cs : List Char) : Nat → List Char × List Char
  | 0 => ([], cs)
  | fuel + 1 =>
    match splitBreak cs with
    | some (brk, rest) =>
      let (line, after) := toEol rest
      let blank := line.all (fun c => c = ' ' || c = '\t')
      let ind := indentOf line
      let go (n' : Option Nat) :=
        let (a, b) := blockBody n' after fuel
        (brk ++ line ++ a, b)
      if blank then go n?
      else match n? with
        | none => if ind = 0 then ([], cs) else go (some ind)
        | some n => if ind < n then ([], cs) else go (some n)
    | none => ([], cs)

/-- A plain scalar from a non-indicator first character: to the end of the
line, a `: `/`:⏎`, a ` #`, or (in flow) a flow indicator or `:` before one. -/
def plain (flow : Nat) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if c = '\n' || c = '\r' then ([], c :: cs)
    else if c = ':' ∧ (isSpaceBreakOrEnd cs ∨ (flow > 0 ∧ (cs.head?.any isFlowIndicatorBool))) then ([], c :: cs)
    else if (c = ' ' ∨ c = '\t') ∧ cs.head? = some '#' then ([], c :: cs)
    else if flow > 0 ∧ isFlowIndicatorBool c then ([], c :: cs)
    else let (a, b) := plain flow cs; (c :: a, b)

def isIndicatorStart (c : Char) : Bool :=
  c ∈ ['-', '?', ':', ',', '[', ']', '{', '}', '#', '&', '*', '!', '|', '>', '\'', '"', '%', '@', '`']

def anchorName (cs : List Char) : List Char × List Char := spanWhile isAnchorCharBool cs

def tagChars (flow : Nat) (cs : List Char) : List Char × List Char :=
  spanWhile (fun c => !(c = ' ' || c = '\t' || c = '\n' || c = '\r' || (flow > 0 && isFlowIndicatorBool c))) cs

/-- The line `cs` starts with is blank or a comment: `[79] s-l-comments` lets a
directive absorb it, so these lines ride the directive text up to `---`. -/
def isCommentLine (cs : List Char) : Bool :=
  match (cs.dropWhile fun c => c = ' ' || c = '\t') with
  | [] => false
  | c :: _ => c = '#' || c = '\n' || c = '\r'

/-- Split off one line together with its break (`\r\n` counted as one);
`none` when the line is not terminated. -/
def lineWithBreak (cs : List Char) : Option (List Char × List Char) :=
  let (line, after) := toEol cs
  match after with
  | '\r' :: '\n' :: rest => some (line ++ ['\r', '\n'], rest)
  | b :: rest => some (line ++ [b], rest)
  | [] => none

/-- Absorb the blank and comment lines following a directive line. -/
def commentLines (cs : List Char) : Nat → List Char × List Char
  | 0 => ([], cs)
  | fuel + 1 =>
    if isCommentLine cs then
      match lineWithBreak cs with
      | some (line, rest) =>
          let (more, rest') := commentLines rest fuel
          (line ++ more, rest')
      | none => ([], cs)
    else ([], cs)

/-- One step; `none` on an input the skeleton cannot describe. -/
def step (s : Lx) : List Char → Option (Lx × List Char)
  | [] => some (s, [])
  | c :: cs =>
    -- document markers and directives at column 0
    if s.col = 0 ∧ c = '-' ∧ cs.take 2 = ['-', '-'] ∧ isSpaceBreakOrEnd (cs.drop 2) then
      let s := (s.flush).emit (.docStart s.dirs.reverse)
      some ({ s with dirs := [], nodeStart := true }, cs.drop 2)
    else if s.col = 0 ∧ c = '.' ∧ cs.take 2 = ['.', '.'] ∧ isSpaceBreakOrEnd (cs.drop 2) then
      some ({ (s.flush).emit .docEnd with nodeStart := true }, cs.drop 2)
    else if s.col = 0 ∧ c = '%' then
      match lineWithBreak (c :: cs) with
      | some (line, rest) =>
          let (more, rest') := commentLines rest rest.length
          some ({ s.flush with dirs := (line ++ more) :: s.dirs, col := 0 }, rest')
      | none => none
    -- comments
    else if c = '#' ∧ (s.nodeStart ∨ s.other.head?.any (fun d => d = ' ' || d = '\t' || d = '\n')) then
      let (line, after) := toEol (c :: cs)
      some ({ s.emit (.opaque line) with nodeStart := false }, after)
    -- quoted scalars
    else if c = '"' ∨ c = '\'' then
      match quoted c cs with
      | none => none
      | some (body, after) => some ({ s.emit (.opaque (c :: body)) with nodeStart := false }, after)
    -- node properties and aliases at a node start
    else if s.nodeStart ∧ c = '&' then
      let (name, after) := anchorName cs
      if name.isEmpty then none
      else some ({ s.emit (.anchor (String.ofList name)) with nodeStart := true }, after)
    else if s.nodeStart ∧ c = '*' then
      let (name, after) := anchorName cs
      if name.isEmpty then none
      else some ({ s.emit (.alias (String.ofList name)) with nodeStart := false }, after)
    -- a verbatim tag `!<…>` names no handle: opaque, no event (concept §6 Q4)
    else if s.nodeStart ∧ c = '!' ∧ cs.head? = some '<' then
      match cs.findIdx? (· = '>') with
      | some i =>
          let uri := cs.take (i + 1)
          if uri.any (fun d => d = ' ' ∨ d = '\t' ∨ isBreak d) then none
          else some ({ s.emit (.opaque (c :: uri)) with nodeStart := true }, cs.drop (i + 1))
      | none => none
    else if s.nodeStart ∧ c = '!' then
      let (body, after) := tagChars s.flow cs
      let chars := c :: body
      some ({ s.emit (.tagUse (handleOf chars) chars) with nodeStart := true }, after)
    -- block scalars
    else if s.nodeStart ∧ (c = '|' ∨ c = '>') then
      let (header, after) := toEol cs
      let (body, after') := blockBody none after after.length
      some ({ s.emit (.opaque (c :: header ++ body)) with nodeStart := false }, after')
    -- flow brackets and indicators
    else if c = '[' ∨ c = '{' then
      some ({ s.push c with flow := s.flow + 1, nodeStart := true }, cs)
    else if c = ']' ∨ c = '}' then
      some ({ s.push c with flow := s.flow - 1, nodeStart := false }, cs)
    else if c = ',' then some ({ s.push c with nodeStart := true }, cs)
    else if (c = '-' ∨ c = '?' ∨ c = ':') ∧ isSpaceBreakOrEnd cs then
      some ({ s.push c with nodeStart := true }, cs)
    -- in flow, `:` before `,` `]` `}` is the value indicator of an empty value ([148]'s `e-node`
    -- arm; `plain` above already ends a plain there) — item 466: `{a:}`, `[a:, b]`, `[:]` were refused
    else if c = ':' ∧ s.flow > 0 ∧ cs.head?.any isFlowIndicatorBool then
      some ({ s.push c with nodeStart := true }, cs)
    else if c = '\n' ∨ c = '\r' then some ({ s.push c with nodeStart := true }, cs)
    else if c = ' ' ∨ c = '\t' then some (s.push c, cs)
    -- plain scalars
    else if s.nodeStart ∧ (c = '%' ∨ c = '@' ∨ c = '`') then none
    else
      let (body, after) := plain s.flow (c :: cs)
      if body.isEmpty then none
      else some ({ s.emit (.opaque body) with nodeStart := false }, after)

def loop (s : Lx) (cs : List Char) (fuel : Nat) : Option (List Seg) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match cs with
    | [] => if s.dirs.isEmpty then some (s.flush).segs.toList else none
    | _ => match step s cs with
      | none => none
      | some (s', cs') => loop s' cs' fuel

def refLex (input : String) : Option (List Seg) :=
  loop {} input.toList (input.length + 1)

def eventsOf (input : String) : List Event :=
  ((refLex input).map eventsOfSegs).getD []

def wellFormedB (input : String) : Bool :=
  match refLex input with
  | some segs => checkFrom {} (eventsOfSegs segs)
  | none => false

/-! ## Rule-2 instantiations -/

#guard eventsOf "&x [*x]" = [.defineAnchor "x", .useAlias "x"]
#guard wellFormedB "&x [*x]" = true
#guard wellFormedB "&x {a: *x}" = true
#guard wellFormedB "&x\n- *x" = true
#guard wellFormedB "*x" = false
#guard wellFormedB "[*x]" = false
#guard eventsOf "\"&x\"" = []
#guard eventsOf "'*x'" = []
#guard eventsOf "# *x" = []
#guard eventsOf "a*b" = []
#guard eventsOf "a: b &c" = []
#guard eventsOf "&a*b x" = [.defineAnchor "a*b"]
#guard eventsOf "|\n *x\n" = []
#guard eventsOf ">\n  &x\n" = []
#guard eventsOf "- |\n  *x\n- *y" = [.useAlias "y"]
#guard eventsOf "--- &x 1\n--- *x" = [.beginDocument, .defineAnchor "x", .beginDocument, .useAlias "x"]
#guard wellFormedB "--- &x 1\n--- *x" = false
#guard wellFormedB "a: &x 1\n...\nb: *x" = false
#guard wellFormedB "a: &x 1\nb: *x" = true
#guard eventsOf "%TAG !h! tag:e,2026:\n--- !h!item value" = [.beginDocument, .declareTag "!h!", .useTag "!h!"]
#guard wellFormedB "%TAG !h! tag:e,2026:\n--- !h!item value" = true
#guard wellFormedB "%TAG !h! tag:e,2026:\r\n--- !h!item value" = true
#guard eventsOf "a\r---\r*x" = [.beginDocument, .useAlias "x"]
#guard eventsOf "&ab b" = [.defineAnchor "ab"]
#guard wellFormedB "!h!item value" = false
#guard wellFormedB "!!str a" = true
#guard wellFormedB "%TAG !h! x" = false
#guard eventsOf "a: !!str &x b" = [.useTag "!!", .defineAnchor "x"]
#guard eventsOf "? &k a\n: *k" = [.defineAnchor "k", .useAlias "k"]
#guard eventsOf "{&a x: *a, b: \"*a\"}" = [.defineAnchor "a", .useAlias "a"]
#guard eventsOf "a: b # &x\n" = []
#guard eventsOf "- a\n- &b c\n- *b" = [.defineAnchor "b", .useAlias "b"]
#guard refLex "\"abc" = none
#guard (refLex "a: &x b\n").map List.length = some 6

end L4YAML.Proofs.Serialization.EventsOf

end Blanket
