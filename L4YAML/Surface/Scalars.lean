/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Surface.Basic
import L4YAML.Spec.Grammar

/-!
# Scalar Surface Syntax — Chapters 7.3 & 8.1

Surface syntax predicates for YAML scalar styles: double-quoted, single-quoted,
plain, literal block, and folded block scalars.

## Productions Covered

- **Double-quoted**: c-double-quoted, nb-double-text,
  nb-double-char, nb-double-one-line, s-double-escaped, s-double-break,
  nb-double-multi-line
- **Single-quoted**: c-single-quoted, nb-single-text,
  nb-single-char, nb-single-one-line, nb-single-multi-line
- **Plain scalars**: ns-plain, ns-plain-first, ns-plain-safe,
  ns-plain-char, ns-plain-one-line, s-ns-plain-next-line, ns-plain-multi-line
- **Block scalars**: c-l+literal, c-l+folded, l-nb-literal-text,
  b-nb-literal-next, l-literal-content, s-nb-folded-text, etc.
-/

set_option autoImplicit false

namespace L4YAML.Surface

open L4YAML.CharPredicates

/-! ## §1 Double-Quoted Scalars -/

/-- [107] nb-double-char: content character inside double-quoted scalar.
    Either a regular non-break character (not '\' or '"') or an escape sequence. -/
@[yaml_spec "7.3.1" 107 "nb-double-char disjunct (nb-json - c-escape - c-double-quote)"]
inductive SNbDoubleChar : SurfPos → SurfPos → Prop where
  | plain (c : Char) (rest : List Char) (col : Nat)
      (hNotBreak : ¬isLineBreakProp c) (hNotBs : c ≠ '\\') (hNotDq : c ≠ '"') :
      SNbDoubleChar ⟨c :: rest, col⟩ ⟨rest, col + 1⟩
  | escape (ec : Char) (rest : List Char) (col : Nat)
      (hValid : L4YAML.Grammar.isNamedEscapeChar ec) :
      SNbDoubleChar ⟨'\\' :: ec :: rest, col⟩ ⟨rest, col + 2⟩
  | hexEscape2 (rest : List Char) (col : Nat) (h1 h2 : Char)
      (hHex1 : isNsHexDigit h1) (hHex2 : isNsHexDigit h2) :
      SNbDoubleChar ⟨'\\' :: 'x' :: h1 :: h2 :: rest, col⟩ ⟨rest, col + 4⟩
  | hexEscape4 (rest : List Char) (col : Nat) (h1 h2 h3 h4 : Char)
      (hHex1 : isNsHexDigit h1) (hHex2 : isNsHexDigit h2)
      (hHex3 : isNsHexDigit h3) (hHex4 : isNsHexDigit h4) :
      SNbDoubleChar ⟨'\\' :: 'u' :: h1 :: h2 :: h3 :: h4 :: rest, col⟩ ⟨rest, col + 6⟩
  | hexEscape8 (rest : List Char) (col : Nat) (h1 h2 h3 h4 h5 h6 h7 h8 : Char)
      (hHex1 : isNsHexDigit h1) (hHex2 : isNsHexDigit h2)
      (hHex3 : isNsHexDigit h3) (hHex4 : isNsHexDigit h4)
      (hHex5 : isNsHexDigit h5) (hHex6 : isNsHexDigit h6)
      (hHex7 : isNsHexDigit h7) (hHex8 : isNsHexDigit h8) :
      SNbDoubleChar ⟨'\\' :: 'U' :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: h8 :: rest, col⟩
        ⟨rest, col + 10⟩

attribute [
    yaml_spec "7.3.1" 107 "nb-double-char disjunct (nb-json - c-escape - c-double-quote)",
    yaml_spec "5.1" 2 "nb-json"
    ] SNbDoubleChar.plain

attribute [
    yaml_spec "7.3.1" 107 "nb-double-char disjunct (c-ns-esc-char - ns-esc-8-bit - ns-esc-16-bit - ns-esc-32-bit)",
    yaml_spec "5.7" 42 "ns-esc-null",
    yaml_spec "5.7" 43 "ns-esc-bell",
    yaml_spec "5.7" 44 "ns-esc-backspace",
    yaml_spec "5.7" 45 "ns-esc-horizontal-tab",
    yaml_spec "5.7" 45 "ns-esc-horizontal-tab (literal)",
    yaml_spec "5.7" 46 "ns-esc-line-feed",
    yaml_spec "5.7" 47 "ns-esc-vertical-tab",
    yaml_spec "5.7" 48 "ns-esc-form-feed",
    yaml_spec "5.7" 49 "ns-esc-carriage-return",
    yaml_spec "5.7" 50 "ns-esc-escape",
    yaml_spec "5.7" 51 "ns-esc-space",
    yaml_spec "5.7" 52 "ns-esc-double-quote",
    yaml_spec "5.7" 53 "ns-esc-slash",
    yaml_spec "5.7" 54 "ns-esc-backslash",
    yaml_spec "5.7" 55 "ns-esc-next-line",
    yaml_spec "5.7" 56 "ns-esc-non-breaking-space",
    yaml_spec "5.7" 57 "ns-esc-line-separator",
    yaml_spec "5.7" 58 "ns-esc-paragraph-separator"
    ] SNbDoubleChar.escape

attribute [
    yaml_spec "7.3.1" 107 "nb-double-char and ns-esc-8-bit",
    yaml_spec "5.7" 50 "ns-esc-8-bit"
    ] SNbDoubleChar.hexEscape2

attribute [
    yaml_spec "7.3.1" 107 "nb-double-char and ns-esc-16-bit",
    yaml_spec "5.7" 60 "ns-esc-16-bit"
    ] SNbDoubleChar.hexEscape4

attribute [
    yaml_spec "7.3.1" 107 "nb-double-char and ns-esc-32-bit",
    yaml_spec "5.7" 61 "ns-esc-32-bit"
    ] SNbDoubleChar.hexEscape8


/-- [112] s-double-escaped(n): escaped line break in double-quoted scalar.
    Optional white space + '\' + b-non-content + optional empty lines +
    flow line prefix (indent + optional whitespace). -/
@[yaml_spec "7.3.1" 112 "s-double-escaped(n)"]
inductive SSDoubleEscaped : Nat → SurfPos → SurfPos → Prop where
  | mk (n : Nat) (s s₁ s₂ s₃ s₄ s' : SurfPos) :
      GStar SSWhite s s₁ →
      GLit '\\' s₁ s₂ →
      SBNonContent s₂ s₃ →
      GStar (SLEmpty n .flowIn) s₃ s₄ →
      SFlowLinePrefix n s₄ s' →
      SSDoubleEscaped n s s'

/-- [113] s-double-break(n): line break in double-quoted scalar.
    Either an escaped break or a flow-folded break. -/
@[yaml_spec "7.3.1" 113 "s-double-break(n)"]
inductive SSDoubleBreak : Nat → SurfPos → SurfPos → Prop where
  | escaped (n : Nat) (s s' : SurfPos) :
      SSDoubleEscaped n s s' → SSDoubleBreak n s s'
  | flowFold (n : Nat) (s s₁ s₂ s' : SurfPos) :
      SBBreak s s₁ →
      GStar (SLEmpty n .flowIn) s₁ s₂ →
      SFlowLinePrefix n s₂ s' →
      SSDoubleBreak n s s'

/-- [111] nb-double-one-line: double-quoted content on a single line. -/
@[yaml_spec "7.3.1" 111 "nb-double-one-line"]
abbrev SNbDoubleOneLine : SurfPos → SurfPos → Prop := GStar SNbDoubleChar

/-- [116] nb-double-multi-line(n): multi-line double-quoted content. -/
@[yaml_spec "7.3.1" 116 "nb-double-multi-line(n)"]
inductive SNbDoubleMultiLine : Nat → SurfPos → SurfPos → Prop where
  | single (n : Nat) (s s' : SurfPos) :
      SNbDoubleOneLine s s' → SNbDoubleMultiLine n s s'
  | multi (n : Nat) (s s₁ s₂ s₃ s' : SurfPos) :
      SNbDoubleOneLine s s₁ →
      SSDoubleBreak n s₁ s₂ →
      SNbDoubleMultiLine n s₂ s' →
      SNbDoubleMultiLine n s s'

/-- [110] nb-double-text(n,c): double-quoted body text.
    Spec defines this only for the four contexts in which [107] c-double-quoted
    is invoked; blockOut/blockIn are unreachable here and grouped with the
    multi-line case to satisfy totality. -/
@[yaml_spec "7.3.1" 110 "nb-double-text(n,c)"]
def SNbDoubleText (n : Nat) (c : L4YAML.YamlContext) : SurfPos → SurfPos → Prop :=
  match c with
  | .flowOut  | .flowIn  => SNbDoubleMultiLine n
  | .blockKey | .flowKey => SNbDoubleOneLine
  | .blockOut | .blockIn => SNbDoubleMultiLine n

/-- [109] c-double-quoted(n,c): complete double-quoted scalar. -/
@[yaml_spec "7.3.1" 109 "c-double-quoted(n,c)"]
inductive SCDoubleQuoted : Nat → L4YAML.YamlContext → SurfPos → SurfPos → Prop where
  | mk (n : Nat) (c : L4YAML.YamlContext) (s s₁ s₂ s' : SurfPos) :
      GLit '"' s s₁ →
      SNbDoubleText n c s₁ s₂ →
      GLit '"' s₂ s' →
      SCDoubleQuoted n c s s'

/-! ## §2 Single-Quoted Scalars -/

/-- [118] nb-single-char: content character inside single-quoted scalar.
    Any non-break character except single quote, or escaped quote (''). -/
@[yaml_spec "7.3.2" 118 "nb-single-char disjunct (nb-json - c-single-quote)"]
inductive SNbSingleChar : SurfPos → SurfPos → Prop where
  | plain (c : Char) (rest : List Char) (col : Nat)
      (hNotBreak : ¬isLineBreakProp c) (hNotSq : c ≠ '\'') :
      SNbSingleChar ⟨c :: rest, col⟩ ⟨rest, col + 1⟩
  | escapedQuote (rest : List Char) (col : Nat) :
      SNbSingleChar ⟨'\'' :: '\'' :: rest, col⟩ ⟨rest, col + 2⟩

/-- [122] nb-single-one-line: single-quoted content on one line. -/
@[yaml_spec "7.3.2" 122 "nb-single-one-line"]
abbrev SNbSingleOneLine : SurfPos → SurfPos → Prop := GStar SNbSingleChar

/-- [125] nb-single-multi-line(n): multi-line single-quoted content. -/
@[yaml_spec "7.3.2" 125 "nb-single-multi-line(n)"]
inductive SNbSingleMultiLine : Nat → SurfPos → SurfPos → Prop where
  | single (n : Nat) (s s' : SurfPos) :
      SNbSingleOneLine s s' → SNbSingleMultiLine n s s'
  | multi (n : Nat) (s s₁ s₂ s₃ s₄ s' : SurfPos) :
      SNbSingleOneLine s s₁ →
      SBBreak s₁ s₂ →
      GStar (SLEmpty n .flowIn) s₂ s₃ →
      SFlowLinePrefix n s₃ s₄ →
      SNbSingleMultiLine n s₄ s' →
      SNbSingleMultiLine n s s'

/-- [121] nb-single-text(n,c): single-quoted body text.
    Spec defines this only for the four contexts in which [120] c-single-quoted
    is invoked; blockOut/blockIn are unreachable here and grouped with the
    multi-line case to satisfy totality. -/
@[yaml_spec "7.3.2" 121 "nb-single-text(n,c)"]
def SNbSingleText (n : Nat) (c : L4YAML.YamlContext) : SurfPos → SurfPos → Prop :=
  match c with
  | .flowOut  | .flowIn  => SNbSingleMultiLine n
  | .blockKey | .flowKey => SNbSingleOneLine
  | .blockOut | .blockIn => SNbSingleMultiLine n

/-- [120] c-single-quoted(n,c): complete single-quoted scalar. -/
@[yaml_spec "7.3.2" 120 "c-single-quoted(n,c)"]
inductive SCSingleQuoted : Nat → L4YAML.YamlContext → SurfPos → SurfPos → Prop where
  | mk (n : Nat) (c : L4YAML.YamlContext) (s s₁ s₂ s' : SurfPos) :
      GLit '\'' s s₁ →
      SNbSingleText n c s₁ s₂ →
      GLit '\'' s₂ s' →
      SCSingleQuoted n c s s'

/-! ## §3 Plain Scalars -/

/-- [127] ns-plain-safe(c): safe characters for plain scalars.
    In flow context, excludes flow indicators. -/
@[yaml_spec "7.3.3" 127 "ns-plain-safe(c)"]
def isNsPlainSafe (c : L4YAML.YamlContext) (ch : Char) : Prop :=
  match c with
  | .flowOut | .blockKey | .blockOut | .blockIn =>
      isNsChar ch
  | .flowIn | .flowKey =>
      isNsChar ch ∧ ¬isFlowIndicatorProp ch

/-- [126] ns-plain-first(c): first character of a plain scalar.
    Not an indicator, or an indicator followed by ns-plain-safe(c). -/
@[yaml_spec "7.3.3" 126 "ns-plain-first(c)"]
inductive SNsPlainFirst : L4YAML.YamlContext → SurfPos → SurfPos → Prop where
  | nonIndicator (c : L4YAML.YamlContext) (ch : Char) (rest : List Char) (col : Nat)
      (hSafe : isNsPlainSafe c ch) (hNotInd : ¬isIndicatorProp ch) :
      SNsPlainFirst c ⟨ch :: rest, col⟩ ⟨rest, col + 1⟩
  | dashSafe (c : L4YAML.YamlContext) (next : Char) (rest : List Char) (col : Nat)
      (hSafe : isNsPlainSafe c next) :
      SNsPlainFirst c ⟨'-' :: next :: rest, col⟩ ⟨next :: rest, col + 1⟩
  | colonSafe (c : L4YAML.YamlContext) (next : Char) (rest : List Char) (col : Nat)
      (hSafe : isNsPlainSafe c next) :
      SNsPlainFirst c ⟨':' :: next :: rest, col⟩ ⟨next :: rest, col + 1⟩
  | questionSafe (c : L4YAML.YamlContext) (next : Char) (rest : List Char) (col : Nat)
      (hSafe : isNsPlainSafe c next) :
      SNsPlainFirst c ⟨'?' :: next :: rest, col⟩ ⟨next :: rest, col + 1⟩

/-- [130] ns-plain-char(c): subsequent characters in a plain scalar.
    Safe chars except ':' and '#' have adjacency constraints. -/
@[yaml_spec "7.3.3" 130 "ns-plain-char(c)"]
inductive SNsPlainChar : L4YAML.YamlContext → SurfPos → SurfPos → Prop where
  | safe (c : L4YAML.YamlContext) (ch : Char) (rest : List Char) (col : Nat)
      (hSafe : isNsPlainSafe c ch)
      (hNotColon : ch ≠ ':') (hNotHash : ch ≠ '#') :
      SNsPlainChar c ⟨ch :: rest, col⟩ ⟨rest, col + 1⟩
  | colonSafe (c : L4YAML.YamlContext) (prev : Char) (next : Char)
      (rest : List Char) (col : Nat)
      (hSafe : isNsPlainSafe c next) :
      -- ':' followed by ns-plain-safe (not standalone)
      SNsPlainChar c ⟨':' :: next :: rest, col⟩ ⟨next :: rest, col + 1⟩
  | hashAfterNs (c : L4YAML.YamlContext) (rest : List Char) (col : Nat)
      (hColGt : col > 0) :
      -- '#' preceded by non-space (approximated by col > 0)
      SNsPlainChar c ⟨'#' :: rest, col⟩ ⟨rest, col + 1⟩

/-- [132] nb-ns-plain-in-line(c) entry: `s-white* ns-plain-char(c)`.
    One unit of the intra-line repetition: optional whitespace followed by a
    plain content character. -/
@[yaml_spec "7.3.3" 132 "nb-ns-plain-in-line(c)"]
inductive SNbNsPlainInLineEntry : L4YAML.YamlContext → SurfPos → SurfPos → Prop where
  | mk (c : L4YAML.YamlContext) (s s₁ s' : SurfPos) :
      GStar SSWhite s s₁ →
      SNsPlainChar c s₁ s' →
      SNbNsPlainInLineEntry c s s'

/-- [133] ns-plain-one-line(c): plain scalar content on a single line.
    `ns-plain-first(c) nb-ns-plain-in-line(c)` where
    `nb-ns-plain-in-line(c) = ( s-white* ns-plain-char(c) )*`. -/
@[yaml_spec "7.3.3" 133 "ns-plain-one-line(c)"]
inductive SNsPlainOneLine : L4YAML.YamlContext → SurfPos → SurfPos → Prop where
  | mk (c : L4YAML.YamlContext) (s s₁ s' : SurfPos) :
      SNsPlainFirst c s s₁ →
      GStar (SNbNsPlainInLineEntry c) s₁ s' →
      SNsPlainOneLine c s s'

/-- [134] s-ns-plain-next-line(n,c): continuation line in multi-line plain scalar.
    `s-flow-folded(n) ns-plain-char(c) nb-ns-plain-in-line(c)`.
    Includes leading `GStar SSWhite` for trailing whitespace from the previous
    line, matching YAML spec §6.8 `s-flow-folded(n)` which starts with
    `s-separate-in-line?` before the line break.  This enables proper chaining
    in `GStar (SSNsPlainNextLine n c)`.
    NOTE: `SLEmpty` uses `.flowIn` context per YAML spec §6.8 (`s-flow-folded`
    always uses `b-l-trimmed(n, flow-in)` regardless of outer context `c`).
    NOTE: Uses `GStar` instead of `GPlus` for entries. The YAML spec requires
    at least one `ns-plain-char`, which is enforced by the scanner's
    content-length check. TODO: strengthen to `GPlus` once proved. -/
@[yaml_spec "7.3.3" 134 "s-ns-plain-next-line(n,c)"]
inductive SSNsPlainNextLine : Nat → L4YAML.YamlContext → SurfPos → SurfPos → Prop where
  | mk (n : Nat) (c : L4YAML.YamlContext) (s s_ws s₁ s₂ s₃ s' : SurfPos) :
      GStar SSWhite s s_ws →
      SBBreak s_ws s₁ →
      GStar (SLEmpty n .flowIn) s₁ s₂ →
      SFlowLinePrefix n s₂ s₃ →
      GStar (SNbNsPlainInLineEntry c) s₃ s' →
      SSNsPlainNextLine n c s s'

/-- [135] ns-plain-multi-line(n,c): multi-line plain scalar. -/
@[yaml_spec "7.3.3" 135 "ns-plain-multi-line(n,c)"]
inductive SNsPlainMultiLine : Nat → L4YAML.YamlContext → SurfPos → SurfPos → Prop where
  | mk (n : Nat) (c : L4YAML.YamlContext) (s s₁ s' : SurfPos) :
      SNsPlainOneLine c s s₁ →
      GStar (SSNsPlainNextLine n c) s₁ s' →
      SNsPlainMultiLine n c s s'

/-- [131] ns-plain(n,c): complete plain scalar.
    In key contexts: single line only. Otherwise: multi-line.
    Spec defines this for the four contexts that invoke ns-plain (flow-out,
    flow-in, block-key, flow-key); blockOut/blockIn are unreachable here and
    grouped with the multi-line case to satisfy totality. -/
@[yaml_spec "7.3.3" 131 "ns-plain(n,c)"]
def SNsPlain (n : Nat) (c : L4YAML.YamlContext) : SurfPos → SurfPos → Prop :=
  match c with
  | .flowOut  | .flowIn  => SNsPlainMultiLine n c
  | .blockKey | .flowKey => SNsPlainOneLine c
  | .blockOut | .blockIn => SNsPlainMultiLine n c

/-! ## §4 Alias Node -/

/-- [104] c-ns-alias-node: '*' followed by anchor name. -/
@[yaml_spec "7.1" 104 "c-ns-alias-node"]
inductive SCNsAliasNode : SurfPos → SurfPos → Prop where
  | mk (rest : List Char) (col : Nat) (s' : SurfPos) :
      GPlus (GChar isNsAnchorChar) ⟨rest, col + 1⟩ s' →
      SCNsAliasNode ⟨'*' :: rest, col⟩ s'

/-! ## §5 Block Scalars

Block scalars are the most complex scalar form: a header line (with chomp and
indent indicators) followed by content lines at a detected indentation level.
The indentation auto-detection makes the grammar context-dependent in a way
that's naturally expressed as existential quantification over the indent value. -/

/-- [162] c-b-block-header: block scalar header (chomp + indent indicators).
    Matches a subset of `[-+0-9]` characters. -/
@[yaml_spec "8.1.1" 162 "c-b-block-header"]
inductive SCBBlockHeader : SurfPos → SurfPos → Prop where
  | mk (s s₁ s' : SurfPos) :
      GStar (GChar (fun c => L4YAML.Grammar.isBlockScalarHeaderChar c = true)) s s₁ →
      SSBComment s₁ s' →
      SCBBlockHeader s s'

/-- [171] l-nb-literal-text(n): one line of literal block scalar content.
    s-indent(n) followed by nb-char+. -/
@[yaml_spec "8.1.2" 171 "l-nb-literal-text(n)"]
inductive SLNbLiteralText : Nat → SurfPos → SurfPos → Prop where
  | mk (n : Nat) (s s₁ s' : SurfPos) :
      GStar (SLEmpty n .blockIn) s s₁ →
      GSeq (SIndent n) (GPlus SNbChar) s₁ s' →
      SLNbLiteralText n s s'

/-- [172] b-nb-literal-next(n): continuation line in literal scalar. -/
@[yaml_spec "8.1.2" 172 "b-nb-literal-next(n)"]
inductive SBNbLiteralNext : Nat → SurfPos → SurfPos → Prop where
  | mk (n : Nat) (s s₁ s' : SurfPos) :
      SBAsLineFeed s s₁ → SLNbLiteralText n s₁ s' →
      SBNbLiteralNext n s s'

/-- [173] l-literal-content(n,t): full literal scalar content.
    Optional first line + continuation lines + optional trailing break,
    plus l-chomped-empty(n,t): trailing empty lines + optional partial indent at EOF. -/
@[yaml_spec "8.1.2" 173 "l-literal-content(n,t)"]
inductive SLLiteralContent : Nat → SurfPos → SurfPos → Prop where
  | mk (n : Nat) (s s₁ s₂ s₃ s' : SurfPos) :
      GOpt (GSeq (SLNbLiteralText n) (GStar (SBNbLiteralNext n))) s s₁ →
      GOpt SBBreak s₁ s₂ →
      GStar (SLEmpty n .blockIn) s₂ s₃ →
      GOpt (SIndentLe n) s₃ s' →
      SLLiteralContent n s s'

/-- [170] c-l+literal(n): complete literal block scalar.
    '|' + header + content at auto-detected indent m.
    Note: YAML spec says m ≥ 1 relative to n = -1. Our Nat encoding uses n = 0
    (a +1 offset), so the correct constraint is m ≥ 0 (trivially true for Nat). -/
@[yaml_spec "8.1.2" 170 "c-l+literal(n)"]
inductive SCLLiteral : Nat → SurfPos → SurfPos → Prop where
  | mk (n : Nat) (m : Nat) (rest : List Char) (col : Nat) (s₁ s' : SurfPos) :
      SCBBlockHeader ⟨rest, col + 1⟩ s₁ →
      SLLiteralContent (n + m) s₁ s' →
      SCLLiteral n ⟨'|' :: rest, col⟩ s'

/-- [175] s-nb-folded-text(n): one line of folded content that's NOT blank. -/
@[yaml_spec "8.1.3" 175 "s-nb-folded-text(n)"]
inductive SSNbFoldedText : Nat → SurfPos → SurfPos → Prop where
  | mk (n : Nat) (s s₁ s' : SurfPos) :
      SIndent n s s₁ → GPlus SNsChar s₁ s' →
      SSNbFoldedText n s s'

/-- [176] l-nb-folded-lines(n): non-blank lines in folded scalar. -/
@[yaml_spec "8.1.3" 176 "l-nb-folded-lines(n)"]
inductive SLNbFoldedLines : Nat → SurfPos → SurfPos → Prop where
  | mk (n : Nat) (s s₁ s' : SurfPos) :
      SSNbFoldedText n s s₁ →
      GStar (GSeq SBBreak (SSNbFoldedText n)) s₁ s' →
      SLNbFoldedLines n s s'

/-- [174] c-l+folded(n): complete folded block scalar.
    '>' + header + content at auto-detected indent m.
    Content structure is complex (spaced/trimmed/folded sections);
    simplified here: the scanner uses the same `collectBlockScalarLoop` for both
    literal and folded, producing identical output structure. We use `SLLiteralContent`
    for both, deferring the literal-vs-folded distinction to semantic interpretation.
    Note: YAML spec says m ≥ 1 relative to n = -1. Our Nat encoding uses n = 0
    (a +1 offset), so the correct constraint is m ≥ 0 (trivially true for Nat). -/
@[yaml_spec "8.1.3" 174 "c-l+folded(n)"]
inductive SCLFolded : Nat → SurfPos → SurfPos → Prop where
  | mk (n : Nat) (m : Nat) (rest : List Char) (col : Nat) (s₁ s' : SurfPos) :
      SCBBlockHeader ⟨rest, col + 1⟩ s₁ →
      SLLiteralContent (n + m) s₁ s' →
      SCLFolded n ⟨'>' :: rest, col⟩ s'

end L4YAML.Surface
