/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Surface.Combinators
public import L4YAML.Spec.Types
public import L4YAML.Spec.CharPredicates

@[expose] public section Blanket

/-!
# Basic Surface Syntax Productions — Chapters 5–6

Character-level, line break, white space, indentation, comment, separation,
and directive productions for YAML 1.2.2.

## Productions Covered

- **Line breaks**: [24]-[31] b-line-feed, b-carriage-return, b-char, b-break,
  b-as-line-feed, b-non-content
- **White space**: [31]-[34] s-space, s-tab, s-white, nb-char, ns-char
- **Indentation**: [63]-[65] s-indent(n), s-indent(<n), s-indent(≤n)
- **Line prefixes**: [67]-[70] l-empty, s-line-prefix, s-flow-line-prefix
- **Comments**: [75]-[81] c-nb-comment-text, s-b-comment, b-comment,
  l-comment, s-l-comments
- **Separation**: [66]-[70] s-separate-in-line, s-separate(n,c),
  s-separate-lines(n)
- **Directives**: [82]-[93] simplified as % + non-break chars + comments
-/

set_option autoImplicit false

namespace L4YAML.Surface

open L4YAML.CharPredicates
open L4YAML (YamlContext)

/-! ## Helper Character Predicates -/

/-- [27] nb-char: non-break character
    (`c-printable - b-char - c-byte-order-mark`). -/
def isNbChar (c : Char) : Prop :=
  ¬isLineBreakProp c ∧ isPrintableProp c ∧ c ≠ '﻿'

/-- [34] ns-char: non-space character
    (`c-printable - b-char - c-byte-order-mark - s-white`). -/
def isNsChar (c : Char) : Prop :=
  ¬isLineBreakProp c ∧ ¬isWhiteSpaceProp c ∧ isPrintableProp c ∧ c ≠ '﻿'

/-- ns-dec-digit: ASCII decimal digit 0–9. -/
def isNsDecDigit (c : Char) : Prop := c ≥ '0' ∧ c ≤ '9'

/-- ns-hex-digit: ASCII hex digit. -/
def isNsHexDigit (c : Char) : Prop :=
  (c ≥ '0' ∧ c ≤ '9') ∨ (c ≥ 'a' ∧ c ≤ 'f') ∨ (c ≥ 'A' ∧ c ≤ 'F')

/-- ns-anchor-char [103]: ns-char minus flow indicators. -/
def isNsAnchorChar (c : Char) : Prop := isNsChar c ∧ ¬isFlowIndicatorProp c

/-! ## §1 Line Break Productions [24]–[31] -/

/-- [28] b-break: line break (CR+LF, CR alone, or LF). Resets column to 0.
    CRLF is preferred over bare CR per spec. -/
inductive SBBreak : SurfPos → SurfPos → Prop where
  | crLf (rest : List Char) (col : Nat) :
      SBBreak ⟨'\r' :: '\n' :: rest, col⟩ ⟨rest, 0⟩
  | cr (rest : List Char) (col : Nat) :
      SBBreak ⟨'\r' :: rest, col⟩ ⟨rest, 0⟩
  | lf (rest : List Char) (col : Nat) :
      SBBreak ⟨'\n' :: rest, col⟩ ⟨rest, 0⟩

/-- [27] b-as-line-feed: same as b-break (line break normalized to LF). -/
abbrev SBAsLineFeed := SBBreak

/-- [30] b-non-content: same as b-break (consumed as non-content). -/
abbrev SBNonContent := SBBreak

/-- [77] b-comment: line break or end of input (end of comment context). -/
inductive SBComment : SurfPos → SurfPos → Prop where
  | break (s s' : SurfPos) : SBBreak s s' → SBComment s s'
  | eof (col : Nat) : SBComment ⟨[], col⟩ ⟨[], col⟩

/-! ## §2 White Space Productions [31]–[34] -/

/-- [33] s-white: space or tab character. -/
inductive SSWhite : SurfPos → SurfPos → Prop where
  | space (rest : List Char) (col : Nat) :
      SSWhite ⟨' ' :: rest, col⟩ ⟨rest, col + 1⟩
  | tab (rest : List Char) (col : Nat) :
      SSWhite ⟨'\t' :: rest, col⟩ ⟨rest, col + 1⟩

/-- [27] nb-char: non-break character. Column increments by 1. -/
abbrev SNbChar : SurfPos → SurfPos → Prop := GChar isNbChar

/-- Comment / directive-trailing body character: any non-break character.
    **Deliberately looser than [27] nb-char** (no printable-range or BOM
    check): comment and directive trailing text is stripped without
    semantic effect, so the scanner accepts — and this grammar records —
    any non-break character there. A spec-strict processor would reject
    non-printables everywhere; recorded in DOCS.md § Other open items. -/
def isCommentTextChar (c : Char) : Prop := ¬isLineBreakProp c

/-- Comment / directive-trailing body character step. -/
abbrev SCommentChar : SurfPos → SurfPos → Prop := GChar isCommentTextChar

/-- ns-char: non-space character (non-break, non-whitespace). -/
abbrev SNsChar : SurfPos → SurfPos → Prop := GChar isNsChar

/-! ## §3 Indentation [63]–[65] -/

/-- [63] s-indent(n): exactly n space characters.
    Indentation must start at column 0 (enforced structurally by appearing
    after line breaks in the grammar). -/
inductive SIndent : Nat → SurfPos → SurfPos → Prop where
  | zero (s : SurfPos) : SIndent 0 s s
  | succ (n : Nat) (rest : List Char) (col : Nat) (s' : SurfPos) :
      SIndent n ⟨rest, col + 1⟩ s' →
      SIndent (n + 1) ⟨' ' :: rest, col⟩ s'

/-- [64] s-indent(<n): fewer than n indentation spaces. -/
def SIndentLt (n : Nat) (s s' : SurfPos) : Prop :=
  ∃ m : Nat, m < n ∧ SIndent m s s'

/-- [65] s-indent(≤n): at most n indentation spaces. -/
def SIndentLe (n : Nat) (s s' : SurfPos) : Prop :=
  ∃ m : Nat, m ≤ n ∧ SIndent m s s'

/-! ## §4 Line Prefixes [67]–[73] -/

/-- [66] s-separate-in-line: one or more whitespace chars, or start of line.
    Start of line is the zero-width match at column 0 and nowhere else, as the
    spec has it.  The scanner's BOM transparency (§5.2) needs no extra arm:
    `ScannerState.consumeBOM` advances past the BOM and puts the column back to
    0, and it runs only at stream start, so every position after a BOM that a
    separator is spent at already has `col = 0`. -/
inductive SSeparateInLine : SurfPos → SurfPos → Prop where
  | whites (s s' : SurfPos) : GPlus SSWhite s s' → SSeparateInLine s s'
  | startOfLine (chars : List Char) : SSeparateInLine ⟨chars, 0⟩ ⟨chars, 0⟩

/-- `startOfLine` at a position known to sit at column 0. -/
lemma SSeparateInLine.startOfLine_of_col0 {s : SurfPos} (h : s.col = 0) :
    SSeparateInLine s s := by
  obtain ⟨chars, col⟩ := s
  simp only at h; subst h
  exact .startOfLine chars

/-- [71] s-flow-line-prefix(n): indent + optional inline separation. -/
inductive SFlowLinePrefix : Nat → SurfPos → SurfPos → Prop where
  | mk (n : Nat) (s s₁ s' : SurfPos) :
      SIndent n s s₁ → GOpt SSeparateInLine s₁ s' →
      SFlowLinePrefix n s s'

/-- [68] s-block-line-prefix(n): just indent. -/
abbrev SBlockLinePrefix (n : Nat) : SurfPos → SurfPos → Prop := SIndent n

/-- [67] l-empty(n,c): empty line = indent + line break. -/
inductive SLEmpty : Nat → YamlContext → SurfPos → SurfPos → Prop where
  | block (n : Nat) (s s₁ s' : SurfPos)
      (c : YamlContext) (hc : c = .blockOut ∨ c = .blockIn) :
      GOpt (SIndentLe n) s s₁ → SBAsLineFeed s₁ s' →
      SLEmpty n c s s'
  | flow (n : Nat) (s s₁ s' : SurfPos)
      (c : YamlContext) (hc : c = .flowOut ∨ c = .flowIn) :
      GOpt (SFlowLinePrefix n) s s₁ → SBAsLineFeed s₁ s' →
      SLEmpty n c s s'
  | flowLt (n : Nat) (s s₁ s' : SurfPos)
      (c : YamlContext) (hc : c = .flowOut ∨ c = .flowIn) :
      SIndentLt n s s₁ → SBAsLineFeed s₁ s' →
      SLEmpty n c s s'

/-! ## §5 Comments [75]–[81] -/

/-- [75] c-nb-comment-text: '#' followed by comment-text chars.
    Uses the deliberately loose `SCommentChar` (any non-break) rather than
    strict nb-char [27]; see `isCommentTextChar`. -/
inductive SCNbCommentText : SurfPos → SurfPos → Prop where
  | mk (rest : List Char) (col : Nat) (s' : SurfPos) :
      GStar SCommentChar ⟨rest, col + 1⟩ s' →
      SCNbCommentText ⟨'#' :: rest, col⟩ s'

/-- [76] s-b-comment: optional (separation + optional comment) + b-comment. -/
inductive SSBComment : SurfPos → SurfPos → Prop where
  | withSep (s s₁ s₂ s' : SurfPos) :
      SSeparateInLine s s₁ → GOpt SCNbCommentText s₁ s₂ → SBComment s₂ s' →
      SSBComment s s'
  | noSep (s s' : SurfPos) :
      SBComment s s' → SSBComment s s'

/-- [78] l-comment: full-line comment = separation + optional text + break. -/
inductive SLComment : SurfPos → SurfPos → Prop where
  | mk (s s₁ s₂ s' : SurfPos) :
      SSeparateInLine s s₁ → GOpt SCNbCommentText s₁ s₂ → SBComment s₂ s' →
      SLComment s s'

/-- [79] s-l-comments: start-of-comment context (after s-b-comment or start of line)
    followed by zero or more line comments. -/
inductive SSLComments : SurfPos → SurfPos → Prop where
  | withComment (s s₁ s' : SurfPos) :
      SSBComment s s₁ → GStar SLComment s₁ s' → SSLComments s s'
  | startOfLine (chars : List Char) (s' : SurfPos) :
      GStar SLComment ⟨chars, 0⟩ s' → SSLComments ⟨chars, 0⟩ s'

/-! ## §6 Separation [69]–[70] -/

/-- [70] s-separate-lines(n): comment-delimited or inline separation. -/
inductive SSeparateLines : Nat → SurfPos → SurfPos → Prop where
  | commented (n : Nat) (s s₁ s' : SurfPos) :
      SSLComments s s₁ → SFlowLinePrefix n s₁ s' →
      SSeparateLines n s s'
  | inline (n : Nat) (s s' : SurfPos) :
      SSeparateInLine s s' → SSeparateLines n s s'

/-- [69] s-separate(n,c): context-dependent separation.
    Block/flow content uses separate-lines; key contexts use inline only. -/
def SSeparate (n : Nat) (c : YamlContext) : SurfPos → SurfPos → Prop :=
  match c with
  | .blockOut | .blockIn | .flowOut | .flowIn => SSeparateLines n
  | .blockKey | .flowKey => SSeparateInLine

/-! ## §7 Directives [82]–[93] (Simplified)

Rather than encoding the full directive grammar (YAML version, tag handles,
reserved directives), we capture the essential structure: a directive line
starts with '%' at the beginning of a line, followed by non-break content,
and ends with comments. The detailed directive validation is handled by
the scanner/parser — the surface syntax just needs to recognize the shape. -/

/-- [82] l-directive, stated as the scanner reads it (`scanDirective`, item 367).
    `'%'` then the directive NAME (a maximal run of ns-chars, `collectDirectiveNameLoop`),
    then one of three bodies:
    * `yaml` — name `YAML`: whites, `[86] ns-yaml-version` = digits `.` digits (both runs
      non-empty), then `[79] s-l-comments` (a `#` needs a white before it: the scanner's
      `directiveTrailingContent` check);
    * `tag` — name `TAG`: whites, `[89] c-tag-handle` chars (word chars and `!`, a maximal run —
      the scanner's handle loop stops only at a non-handle character), whites, the prefix
      (`[39] ns-uri-char`s), then `s-l-comments`;
    * `reserved` — any other name (`[83]`; the empty name included, as the scanner accepts
      `%` alone), stated as the maximal ns-char run that is neither `YAML` nor `TAG`: the rest
      of the line unvalidated (`skipToEndOfLine`), then `s-l-comments`.
    Before item 367 the production was `'%'` + any non-break run + `s-l-comments`, wider than
    the scanner on every `%YAML`/`%TAG` line. -/
inductive SLDirective : SurfPos → SurfPos → Prop where
  | yaml (rest : List Char) (col : Nat) (s₁ s₂ s₃ s₄ s' : SurfPos) :
      GNot (GChar isNsChar) ⟨rest, col + 5⟩ →
      GStar SSWhite ⟨rest, col + 5⟩ s₁ →
      GPlus (GChar isNsDecDigit) s₁ s₂ →
      GLit '.' s₂ s₃ →
      GPlus (GChar isNsDecDigit) s₃ s₄ →
      SSLComments s₄ s' →
      SLDirective ⟨'%' :: 'Y' :: 'A' :: 'M' :: 'L' :: rest, col⟩ s'
  | tag (rest : List Char) (col : Nat) (s₁ s₂ s₃ s₄ s' : SurfPos) :
      GNot (GChar isNsChar) ⟨rest, col + 4⟩ →
      GStar SSWhite ⟨rest, col + 4⟩ s₁ →
      GStar (GChar (fun c => isWordCharProp c ∨ c = '!')) s₁ s₂ →
      GNot (GChar (fun c => isWordCharProp c ∨ c = '!')) s₂ →
      GStar SSWhite s₂ s₃ →
      GStar (GChar isUriCharProp) s₃ s₄ →
      SSLComments s₄ s' →
      SLDirective ⟨'%' :: 'T' :: 'A' :: 'G' :: rest, col⟩ s'
  | reserved (rest : List Char) (col : Nat) (s₀ s₁ s' : SurfPos) :
      GStar (GChar isNsChar) ⟨rest, col + 1⟩ s₀ →
      GNot (GChar isNsChar) s₀ →
      rest ≠ 'Y' :: 'A' :: 'M' :: 'L' :: s₀.chars →
      rest ≠ 'T' :: 'A' :: 'G' :: s₀.chars →
      GStar SCommentChar s₀ s₁ →
      SSLComments s₁ s' →
      SLDirective ⟨'%' :: rest, col⟩ s'

/-! ## §8 Node Properties [94]–[104] (Simplified)

Tag and anchor properties. The full tag grammar has verbatim (`!<uri>`),
shorthand (`!!type`, `!handle!suffix`), and non-specific (`!`) forms.
Anchors have `&name` syntax. We encode the common patterns. -/

/-- [97] c-ns-tag-property: tag starting with '!'.
    [99] c-ns-shorthand-tag is `c-tag-handle ns-tag-char+`, so the `primary`
    suffix is non-empty and the bare `!` is only `nonSpecific` ([100]).
    Every arm ends with the MAXIMAL `[40] ns-tag-char` run (`GNot` lookahead):
    `!t` is the primary tag `!t`, never `!` followed by `t`. -/
inductive SCNsTagProperty : SurfPos → SurfPos → Prop where
  | verbatim (rest : List Char) (col : Nat) (s₁ s₂ s' : SurfPos) :
      GLit '<' ⟨rest, col + 1⟩ s₁ →
      GPlus (GChar isUriCharProp) s₁ s₂ →
      GLit '>' s₂ s' →
      SCNsTagProperty ⟨'!' :: rest, col⟩ s'
  | secondary (srest : List Char) (col : Nat) (s' : SurfPos) :
      GStar (GChar isTagCharProp) ⟨srest, col + 2⟩ s' →
      GNot (GChar isTagCharProp) s' →
      SCNsTagProperty ⟨'!' :: '!' :: srest, col⟩ s'
  | named (rest : List Char) (col : Nat) (s₁ s₂ s' : SurfPos) :
      GPlus (GChar isWordCharProp) ⟨rest, col + 1⟩ s₁ →
      GLit '!' s₁ s₂ →
      GStar (GChar isTagCharProp) s₂ s' →
      GNot (GChar isTagCharProp) s' →
      SCNsTagProperty ⟨'!' :: rest, col⟩ s'
  | nonSpecific (rest : List Char) (col : Nat) :
      GNot (GChar isTagCharProp) ⟨rest, col + 1⟩ →
      SCNsTagProperty ⟨'!' :: rest, col⟩ ⟨rest, col + 1⟩
  | primary (rest : List Char) (col : Nat) (s' : SurfPos) :
      GPlus (GChar isTagCharProp) ⟨rest, col + 1⟩ s' →
      GNot (GChar isTagCharProp) s' →
      SCNsTagProperty ⟨'!' :: rest, col⟩ s'

/-- [101] c-ns-anchor-property: '&' followed by the MAXIMAL run of
    `ns-anchor-char` ([102] `ns-anchor-name` is `ns-anchor-char+`; the name
    cannot stop in front of another anchor char, so `&xa` is the anchor `xa`
    and never the anchor `x` followed by `a`). -/
inductive SCNsAnchorProperty : SurfPos → SurfPos → Prop where
  | mk (rest : List Char) (col : Nat) (s' : SurfPos) :
      GPlus (GChar isNsAnchorChar) ⟨rest, col + 1⟩ s' →
      GNot (GChar isNsAnchorChar) s' →
      SCNsAnchorProperty ⟨'&' :: rest, col⟩ s'

/-- [96] c-ns-properties(n,c): tag + optional (sep + anchor), or
    anchor + optional (sep + tag). -/
inductive SCNsProperties : Nat → YamlContext → SurfPos → SurfPos → Prop where
  | tagFirst (n : Nat) (c : YamlContext) (s s₁ s' : SurfPos) :
      SCNsTagProperty s s₁ →
      GOpt (GSeq (SSeparate n c) SCNsAnchorProperty) s₁ s' →
      SCNsProperties n c s s'
  | anchorFirst (n : Nat) (c : YamlContext) (s s₁ s' : SurfPos) :
      SCNsAnchorProperty s s₁ →
      GOpt (GSeq (SSeparate n c) SCNsTagProperty) s₁ s' →
      SCNsProperties n c s s'

/-! ## §9 Context Helpers -/

/-- [155] in-flow(c): flow context transition. -/
def inFlowCtx (c : YamlContext) : YamlContext :=
  match c with
  | .flowOut => .flowIn
  | .flowIn => .flowIn
  | .blockKey => .flowKey
  | .flowKey => .flowKey
  | .blockOut => .flowIn
  | .blockIn => .flowIn

/-- [192] seq-spaces(n,c): indentation for block sequences. -/
def seqSpaces (n : Nat) (c : YamlContext) : Nat :=
  match c with
  | .blockOut => n - 1
  | _ => n

/-- [72] e-node: empty node (zero-width match). -/
abbrev SENode : SurfPos → SurfPos → Prop := GEps

end L4YAML.Surface

end Blanket
