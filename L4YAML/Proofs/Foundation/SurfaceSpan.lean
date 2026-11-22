/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Surface.Node

@[expose] public section Blanket

/-!
# Every surface production consumes a prefix (DOCS item 229)

A production `P s s'` relates two `SurfPos`es, and nothing in the encoding
says that `s'` is REACHED from `s`: `SurfPos` is a pair of a character list
and a column, so "the same characters" and "the same place" are different
statements.  What ties them is one sentence —

> the characters `s'` still holds are a suffix of the characters `s` held,

written `s'.chars <:+ s.chars` — and its consequence, which is the sentence
item 228 could not say: there is a list `pre` with `s.chars = pre ++ s'.chars`,
the characters LYING BETWEEN the two positions.  `Span` below names it.

## Why the file is this size

Item 228 priced this instrument by signatures, before a line of it existed,
at "69 constructor arms" — the arms of the 18-type mutual block in
`Surface/Node.lean`.  That is the price of §4 alone.  The arms cite leaf
productions — `[69] s-separate(n,c)`, `[96] c-ns-properties(n,c)`,
`[131] ns-plain(n,c)`, `[109] c-double-quoted(n,c)`, `[170] c-l+literal(n)` —
whose own suffix lemmas did not exist either, and the transitive closure is
**74 production types with 143 constructor arms**, of which the mutual block
is 18 types and 69 arms.  §1–§3 are the other 56 types.

## The recursion

§4 is one `mutual` block of eighteen lemmas.  The `induction` tactic refuses a
mutually inductive type outright, but the equation compiler does NOT: `lemma`
inside a `mutual` block is a macro in this repo (`L4YAML/Init.lean`) exactly so
that it reaches `elabMutual`, and structural recursion on a proof of a
mutually inductive `Prop` is accepted — on a STRICT SUBFAMILY too, through
each type's own `brecOn`, with the unused `below` motives supplied by the
elaborator (`Proofs.FlowKeyLift` covers the eight flow types and none of the
ten block ones).

The alternative is one application of the family's recursor with eighteen
motives.  It needs all 69 minor premises and hands back exactly one of the
eighteen conclusions, so the other seventeen are reachable only by inverting
that one.  The `mutual` block does not share the 69 between its lemmas: each
is its own fixpoint over the same arms, so it buys all eighteen conclusions at
eighteen times the recursor's price, not at one.  Both facts are measured on
this very family in `Tests/Guards/Proofs/SurfaceSpanCensus.lean` §§5 and 7.

The eighteen are three components rather than one cycle: a nine-type cycle
(`SBlockNode` and the block collections), an eight-type cycle (`SFlowNode` and
the flow collections), and `SImplicitKey`, which recurses into neither.  The
block cycle cites the flow cycle, so the flow cycle is the bottom, and a proof
over the family can be three blocks in that order rather than one of eighteen.
The decomposition — and what a SECOND conclusion over the same arms costs, which
is one citation per link for a pass carrying both and `2 * links +
(links - arms)` for two passes — is machine-checked in
`Tests/Guards/Proofs/ColumnWalkPrice.lean` §§3–4 (DOCS item 235).

This module's closure stops one layer below `Surface/Document.lean`, because
`Surface/Node.lean` imports `Surface/Scalars.lean` and not the document layer.
`L4YAML/Proofs/Foundation/SurfaceSpanSupply.lean` carries the fifteen lemmas
that finish the supply: the four remaining combinators, `[82] l-directive`,
two folded-scalar productions, and the eight two-position productions of the
document layer.  With those, every production of the surface grammar relates
its target to its source as a suffix except `[211] l-yaml-stream`, whose
`scannerDrop` arm makes the statement false —
`Tests/Guards/Proofs/SuffixGapAudit.lean` (DOCS item 236) reads the whole
grammar for arms that connect nothing to nothing and finds that one.

-/

set_option autoImplicit false

namespace L4YAML.Proofs.SurfaceSpan

open L4YAML (YamlContext)
open L4YAML.Surface
open L4YAML.CharPredicates (isLineBreakProp)

/-! ## §0 The span

`Span s s' pre` is the object the suffix statement buys: the characters
between two positions, as a list.  Every lemma below is stated as `<:+`
because that is what composes; `span_of_suffix` converts once, at the point
of use. -/

/-- The characters lying between two positions. -/
def Span (s s' : SurfPos) (pre : List Char) : Prop := s.chars = pre ++ s'.chars

/-- A suffix fact IS a span: this is the whole content of the instrument. -/
lemma span_of_suffix {s s' : SurfPos} (h : s'.chars <:+ s.chars) :
    ∃ pre, Span s s' pre := by
  obtain ⟨pre, hpre⟩ := h
  exact ⟨pre, hpre.symm⟩

/-- …and the span's length is how far the production advanced. -/
lemma span_length {s s' : SurfPos} {pre : List Char} (h : Span s s' pre) :
    s.chars.length = pre.length + s'.chars.length := by
  rw [h, List.length_append]

/-! ## §1 Combinators

Each generic combinator transports the suffix property of its parameter. -/

lemma gchar_suffix {p : Char → Prop} {a b : SurfPos} (h : GChar p a b) :
    b.chars <:+ a.chars := by
  cases h with
  | mk c rest col _ => exact List.suffix_cons c rest

lemma glit_suffix {ch : Char} {a b : SurfPos} (h : GLit ch a b) :
    b.chars <:+ a.chars := by
  cases h with
  | mk rest col => exact List.suffix_cons ch rest

lemma gstar_suffix {P : SurfPos → SurfPos → Prop} {s s' : SurfPos}
    (hP : ∀ a b, P a b → b.chars <:+ a.chars) (h : GStar P s s') :
    s'.chars <:+ s.chars := by
  induction h with
  | nil s => exact List.suffix_refl _
  | cons s₁ s₂ s₃ hp _ ih => exact ih.trans (hP _ _ hp)

lemma gplus_suffix {P : SurfPos → SurfPos → Prop} {s s' : SurfPos}
    (hP : ∀ a b, P a b → b.chars <:+ a.chars) (h : GPlus P s s') :
    s'.chars <:+ s.chars := by
  match h with
  | .mk _ _ _ hp hs => exact (gstar_suffix hP hs).trans (hP _ _ hp)

lemma gopt_suffix {P : SurfPos → SurfPos → Prop} {s s' : SurfPos}
    (hP : ∀ a b, P a b → b.chars <:+ a.chars) (h : GOpt P s s') :
    s'.chars <:+ s.chars := by
  match h with
  | .none _ => exact List.suffix_refl _
  | .some _ _ hp => exact hP _ _ hp

lemma gseq_suffix {P Q : SurfPos → SurfPos → Prop} {s s' : SurfPos}
    (hP : ∀ a b, P a b → b.chars <:+ a.chars)
    (hQ : ∀ a b, Q a b → b.chars <:+ a.chars) (h : GSeq P Q s s') :
    s'.chars <:+ s.chars := by
  match h with
  | .mk _ _ _ hp hq => exact (hQ _ _ hq).trans (hP _ _ hp)

/-! ## §2 Chapters 5–6: breaks, whites, indentation, comments, separation -/

lemma sbBreak_suffix {a b : SurfPos} (h : SBBreak a b) : b.chars <:+ a.chars := by
  match h with
  | .crLf rest _ => exact (List.suffix_cons '\n' rest).trans (List.suffix_cons '\r' _)
  | .cr rest _ => exact List.suffix_cons '\r' rest
  | .lf rest _ => exact List.suffix_cons '\n' rest

lemma sbComment_suffix {a b : SurfPos} (h : SBComment a b) : b.chars <:+ a.chars := by
  match h with
  | .break _ _ hb => exact sbBreak_suffix hb
  | .eof _ => exact List.suffix_refl _

lemma sswhite_suffix {a b : SurfPos} (h : SSWhite a b) : b.chars <:+ a.chars := by
  match h with
  | .space rest _ => exact List.suffix_cons ' ' rest
  | .tab rest _ => exact List.suffix_cons '\t' rest

lemma sIndent_suffix {n : Nat} {a b : SurfPos} (h : SIndent n a b) :
    b.chars <:+ a.chars := by
  induction h with
  | zero s => exact List.suffix_refl _
  | succ n rest col s' _ ih => exact ih.trans (List.suffix_cons ' ' rest)

lemma sIndentLt_suffix {n : Nat} {a b : SurfPos} (h : SIndentLt n a b) :
    b.chars <:+ a.chars := by
  obtain ⟨_, _, hi⟩ := h; exact sIndent_suffix hi

lemma sIndentLe_suffix {n : Nat} {a b : SurfPos} (h : SIndentLe n a b) :
    b.chars <:+ a.chars := by
  obtain ⟨_, _, hi⟩ := h; exact sIndent_suffix hi

lemma sSeparateInLine_suffix {a b : SurfPos} (h : SSeparateInLine a b) :
    b.chars <:+ a.chars := by
  match h with
  | .whites _ _ hp => exact gplus_suffix (fun _ _ => sswhite_suffix) hp
  | .startOfLine _ => exact List.suffix_refl _

lemma sFlowLinePrefix_suffix {n : Nat} {a b : SurfPos} (h : SFlowLinePrefix n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ hi ho =>
    exact (gopt_suffix (fun _ _ => sSeparateInLine_suffix) ho).trans (sIndent_suffix hi)

lemma sLEmpty_suffix {n : Nat} {c : YamlContext} {a b : SurfPos} (h : SLEmpty n c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .block _ _ _ _ _ _ ho hb =>
    exact (sbBreak_suffix hb).trans (gopt_suffix (fun _ _ => sIndentLe_suffix) ho)
  | .flow _ _ _ _ _ _ ho hb =>
    exact (sbBreak_suffix hb).trans (gopt_suffix (fun _ _ => sFlowLinePrefix_suffix) ho)
  | .flowLt _ _ _ _ _ _ hi hb =>
    exact (sbBreak_suffix hb).trans (sIndentLt_suffix hi)

lemma scNbCommentText_suffix {a b : SurfPos} (h : SCNbCommentText a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk rest _ _ hg =>
    exact (gstar_suffix (fun _ _ => gchar_suffix) hg).trans (List.suffix_cons '#' rest)

/-- The `s-separate-in-line` + optional `c-nb-comment-text` + `b-comment`
    shape both `[76] s-b-comment` and `[78] l-comment` are built from. -/
private lemma comment_body_suffix {s s₁ s₂ s' : SurfPos}
    (hsep : SSeparateInLine s s₁) (hopt : GOpt SCNbCommentText s₁ s₂)
    (hbc : SBComment s₂ s') : s'.chars <:+ s.chars :=
  ((sbComment_suffix hbc).trans
    (gopt_suffix (fun _ _ => scNbCommentText_suffix) hopt)).trans
      (sSeparateInLine_suffix hsep)

lemma ssbComment_suffix {a b : SurfPos} (h : SSBComment a b) : b.chars <:+ a.chars := by
  match h with
  | .withSep _ _ _ _ hsep hopt hbc => exact comment_body_suffix hsep hopt hbc
  | .noSep _ _ hbc => exact sbComment_suffix hbc

lemma slComment_suffix {a b : SurfPos} (h : SLComment a b) : b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ hsep hopt hbc => exact comment_body_suffix hsep hopt hbc

/-- **`[79] s-l-comments` consumes a prefix.**  The landing a step reaches is
    a position INSIDE the input, not merely a position whose characters happen
    to look like a tail of it. -/
lemma sslComments_suffix {a b : SurfPos} (h : SSLComments a b) : b.chars <:+ a.chars := by
  match h with
  | .withComment _ _ _ hsb hg =>
    exact (gstar_suffix (fun _ _ => slComment_suffix) hg).trans (ssbComment_suffix hsb)
  | .startOfLine _ _ hg => exact gstar_suffix (fun _ _ => slComment_suffix) hg

lemma sSeparateLines_suffix {n : Nat} {a b : SurfPos} (h : SSeparateLines n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .commented _ _ _ _ hc hp => exact (sFlowLinePrefix_suffix hp).trans (sslComments_suffix hc)
  | .inline _ _ _ hs => exact sSeparateInLine_suffix hs

/-- **`[69] s-separate(n,c)`**, all six contexts at once. -/
lemma sSeparate_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SSeparate n c a b) : b.chars <:+ a.chars := by
  unfold SSeparate at h
  cases c
  · exact sSeparateLines_suffix h    -- blockOut
  · exact sSeparateLines_suffix h    -- blockIn
  · exact sSeparateInLine_suffix h   -- blockKey
  · exact sSeparateLines_suffix h    -- flowOut
  · exact sSeparateLines_suffix h    -- flowIn
  · exact sSeparateInLine_suffix h   -- flowKey

lemma scNsTagProperty_suffix {a b : SurfPos} (h : SCNsTagProperty a b) :
    b.chars <:+ a.chars := by
  match h with
  | .verbatim rest _ _ _ _ hlt hp hgt =>
    exact (((glit_suffix hgt).trans (gplus_suffix (fun _ _ => gchar_suffix) hp)).trans
      (glit_suffix hlt)).trans (List.suffix_cons '!' rest)
  | .secondary srest _ _ hg _ =>
    exact (gstar_suffix (fun _ _ => gchar_suffix) hg).trans
      (List.suffix_append ['!', '!'] srest)
  | .named rest _ _ _ _ hp hl hg _ =>
    exact (((gstar_suffix (fun _ _ => gchar_suffix) hg).trans (glit_suffix hl)).trans
      (gplus_suffix (fun _ _ => gchar_suffix) hp)).trans (List.suffix_cons '!' rest)
  | .nonSpecific rest _ _ => exact List.suffix_cons '!' rest
  | .primary rest _ _ hg _ =>
    exact (gplus_suffix (fun _ _ => gchar_suffix) hg).trans (List.suffix_cons '!' rest)

lemma scNsAnchorProperty_suffix {a b : SurfPos} (h : SCNsAnchorProperty a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk rest _ _ hp _ =>
    exact (gplus_suffix (fun _ _ => gchar_suffix) hp).trans (List.suffix_cons '&' rest)

lemma scNsProperties_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SCNsProperties n c a b) : b.chars <:+ a.chars := by
  match h with
  | .tagFirst _ _ _ _ _ ht ho =>
    exact (gopt_suffix (fun _ _ h => gseq_suffix (fun _ _ => sSeparate_suffix)
      (fun _ _ => scNsAnchorProperty_suffix) h) ho).trans (scNsTagProperty_suffix ht)
  | .anchorFirst _ _ _ _ _ ha ho =>
    exact (gopt_suffix (fun _ _ h => gseq_suffix (fun _ _ => sSeparate_suffix)
      (fun _ _ => scNsTagProperty_suffix) h) ho).trans (scNsAnchorProperty_suffix ha)

/-! ## §3 Chapters 7.3 & 8.1: the scalar styles

`[109] c-double-quoted`, `[120] c-single-quoted`, `[131] ns-plain`,
`[170] c-l+literal` and `[174] c-l+folded` are the five leaves the mutual
block reaches through `[158] ns-flow-content`, and each is the root of its
own tree of productions. -/

lemma snbDoubleChar_suffix {a b : SurfPos} (h : SNbDoubleChar a b) :
    b.chars <:+ a.chars := by
  match h with
  | .plain c rest _ _ _ _ => exact List.suffix_cons c rest
  | .escape ec rest _ _ => exact List.suffix_append ['\\', ec] rest
  | .hexEscape2 rest _ h1 h2 _ _ => exact List.suffix_append ['\\', 'x', h1, h2] rest
  | .hexEscape4 rest _ h1 h2 h3 h4 _ _ _ _ =>
    exact List.suffix_append ['\\', 'u', h1, h2, h3, h4] rest
  | .hexEscape8 rest _ h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ _ _ _ =>
    exact List.suffix_append ['\\', 'U', h1, h2, h3, h4, h5, h6, h7, h8] rest

lemma ssDoubleEscaped_suffix {n : Nat} {a b : SurfPos} (h : SSDoubleEscaped n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ _ _ _ hw hl hb he hp =>
    exact ((((sFlowLinePrefix_suffix hp).trans
      (gstar_suffix (fun _ _ => sLEmpty_suffix) he)).trans (sbBreak_suffix hb)).trans
        (glit_suffix hl)).trans (gstar_suffix (fun _ _ => sswhite_suffix) hw)

lemma ssDoubleBreak_suffix {n : Nat} {a b : SurfPos} (h : SSDoubleBreak n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .escaped _ _ _ he => exact ssDoubleEscaped_suffix he
  | .flowFold _ _ _ _ _ hb he hp =>
    exact ((sFlowLinePrefix_suffix hp).trans
      (gstar_suffix (fun _ _ => sLEmpty_suffix) he)).trans (sbBreak_suffix hb)

lemma snbDoubleOneLine_suffix {a b : SurfPos} (h : SNbDoubleOneLine a b) :
    b.chars <:+ a.chars :=
  gstar_suffix (fun _ _ => snbDoubleChar_suffix) h

lemma snbDoubleMultiLine_suffix {n : Nat} {a b : SurfPos} (h : SNbDoubleMultiLine n a b) :
    b.chars <:+ a.chars := by
  induction h with
  | single _ _ ho => exact snbDoubleOneLine_suffix ho
  | multi _ _ _ _ _ ho hb _ ih =>
    exact ((ih.trans (ssDoubleBreak_suffix hb)).trans (snbDoubleOneLine_suffix ho))

lemma snbDoubleText_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SNbDoubleText n c a b) : b.chars <:+ a.chars := by
  unfold SNbDoubleText at h
  cases c
  · exact snbDoubleMultiLine_suffix h   -- blockOut
  · exact snbDoubleMultiLine_suffix h   -- blockIn
  · exact snbDoubleOneLine_suffix h     -- blockKey
  · exact snbDoubleMultiLine_suffix h   -- flowOut
  · exact snbDoubleMultiLine_suffix h   -- flowIn
  · exact snbDoubleOneLine_suffix h     -- flowKey

/-- **`[109] c-double-quoted(n,c)`**. -/
lemma scDoubleQuoted_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SCDoubleQuoted n c a b) : b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ _ _ hq1 ht hq2 =>
    exact ((glit_suffix hq2).trans (snbDoubleText_suffix ht)).trans (glit_suffix hq1)

lemma snbSingleChar_suffix {a b : SurfPos} (h : SNbSingleChar a b) :
    b.chars <:+ a.chars := by
  match h with
  | .plain c rest _ _ _ => exact List.suffix_cons c rest
  | .escapedQuote rest _ => exact List.suffix_append ['\'', '\''] rest

lemma snbSingleOneLine_suffix {a b : SurfPos} (h : SNbSingleOneLine a b) :
    b.chars <:+ a.chars :=
  gstar_suffix (fun _ _ => snbSingleChar_suffix) h

lemma snbSingleMultiLine_suffix {n : Nat} {a b : SurfPos} (h : SNbSingleMultiLine n a b) :
    b.chars <:+ a.chars := by
  induction h with
  | single _ _ ho => exact snbSingleOneLine_suffix ho
  | multi _ _ _ _ _ _ ho hb he hp _ ih =>
    exact ((((ih.trans (sFlowLinePrefix_suffix hp)).trans
      (gstar_suffix (fun _ _ => sLEmpty_suffix) he)).trans (sbBreak_suffix hb)).trans
        (snbSingleOneLine_suffix ho))

lemma snbSingleText_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SNbSingleText n c a b) : b.chars <:+ a.chars := by
  unfold SNbSingleText at h
  cases c
  · exact snbSingleMultiLine_suffix h   -- blockOut
  · exact snbSingleMultiLine_suffix h   -- blockIn
  · exact snbSingleOneLine_suffix h     -- blockKey
  · exact snbSingleMultiLine_suffix h   -- flowOut
  · exact snbSingleMultiLine_suffix h   -- flowIn
  · exact snbSingleOneLine_suffix h     -- flowKey

/-- **`[120] c-single-quoted(n,c)`**. -/
lemma scSingleQuoted_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SCSingleQuoted n c a b) : b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ _ _ hq1 ht hq2 =>
    exact ((glit_suffix hq2).trans (snbSingleText_suffix ht)).trans (glit_suffix hq1)

lemma snsPlainFirst_suffix {c : YamlContext} {a b : SurfPos} (h : SNsPlainFirst c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .nonIndicator _ ch rest _ _ _ => exact List.suffix_cons ch rest
  | .dashSafe _ next rest _ _ => exact List.suffix_cons '-' (next :: rest)
  | .colonSafe _ next rest _ _ => exact List.suffix_cons ':' (next :: rest)
  | .questionSafe _ next rest _ _ => exact List.suffix_cons '?' (next :: rest)

lemma snsPlainChar_suffix {c : YamlContext} {a b : SurfPos} (h : SNsPlainChar c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .safe _ ch rest _ _ _ _ => exact List.suffix_cons ch rest
  | .colonSafe _ _ next rest _ _ => exact List.suffix_cons ':' (next :: rest)

lemma snbNsPlainInLineEntry_suffix {c : YamlContext} {a b : SurfPos}
    (h : SNbNsPlainInLineEntry c a b) : b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ hw hc =>
    exact (snsPlainChar_suffix hc).trans (gstar_suffix (fun _ _ => sswhite_suffix) hw)
  | .hash _ _ _ hl => cases hl; exact List.suffix_cons '#' _

lemma snsPlainOneLine_suffix {c : YamlContext} {a b : SurfPos} (h : SNsPlainOneLine c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ hf hg =>
    exact (gstar_suffix (fun _ _ => snbNsPlainInLineEntry_suffix) hg).trans
      (snsPlainFirst_suffix hf)

lemma ssNsPlainNextLine_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SSNsPlainNextLine n c a b) : b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ _ _ _ _ _ hw hb he hp hc hg =>
    exact (((((gstar_suffix (fun _ _ => snbNsPlainInLineEntry_suffix) hg).trans
      (snsPlainChar_suffix hc)).trans
      (sFlowLinePrefix_suffix hp)).trans
        (gstar_suffix (fun _ _ => sLEmpty_suffix) he)).trans (sbBreak_suffix hb)).trans
          (gstar_suffix (fun _ _ => sswhite_suffix) hw)

lemma snsPlainMultiLine_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SNsPlainMultiLine n c a b) : b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ _ ho hg =>
    exact (gstar_suffix (fun _ _ => ssNsPlainNextLine_suffix) hg).trans
      (snsPlainOneLine_suffix ho)

/-- **`[131] ns-plain(n,c)`**. -/
lemma snsPlain_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SNsPlain n c a b) : b.chars <:+ a.chars := by
  unfold SNsPlain at h
  cases c
  · exact snsPlainMultiLine_suffix h   -- blockOut
  · exact snsPlainMultiLine_suffix h   -- blockIn
  · exact snsPlainOneLine_suffix h     -- blockKey
  · exact snsPlainMultiLine_suffix h   -- flowOut
  · exact snsPlainMultiLine_suffix h   -- flowIn
  · exact snsPlainOneLine_suffix h     -- flowKey

/-- **`[104] c-ns-alias-node`**. -/
lemma scNsAliasNode_suffix {a b : SurfPos} (h : SCNsAliasNode a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk rest _ _ hp _ =>
    exact (gplus_suffix (fun _ _ => gchar_suffix) hp).trans (List.suffix_cons '*' rest)

lemma scIndentationIndicator_suffix {a b : SurfPos} (h : SCIndentationIndicator a b) :
    b.chars <:+ a.chars := by
  match h with
  | .empty _ => exact List.suffix_refl _
  | .digit _ _ hg => exact gchar_suffix hg

lemma scChompingIndicator_suffix {a b : SurfPos} (h : SCChompingIndicator a b) :
    b.chars <:+ a.chars := by
  match h with
  | .empty _ => exact List.suffix_refl _
  | .strip _ _ hg => exact glit_suffix hg
  | .keep _ _ hg => exact glit_suffix hg

lemma scbBlockHeader_suffix {a b : SurfPos} (h : SCBBlockHeader a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ (.left _ _ hg) hc =>
    exact (ssbComment_suffix hc).trans (gseq_suffix
      (fun _ _ => scIndentationIndicator_suffix) (fun _ _ => scChompingIndicator_suffix) hg)
  | .mk _ _ _ (.right _ _ hg) hc =>
    exact (ssbComment_suffix hc).trans (gseq_suffix
      (fun _ _ => scChompingIndicator_suffix) (fun _ _ => scIndentationIndicator_suffix) hg)

lemma slNbLiteralText_suffix {n : Nat} {a b : SurfPos} (h : SLNbLiteralText n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ he hs =>
    exact (gseq_suffix (fun _ _ => sIndent_suffix)
      (fun _ _ h => gplus_suffix (fun _ _ => gchar_suffix) h) hs).trans
        (gstar_suffix (fun _ _ => sLEmpty_suffix) he)

lemma sbNbLiteralNext_suffix {n : Nat} {a b : SurfPos} (h : SBNbLiteralNext n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ hb ht => exact (slNbLiteralText_suffix ht).trans (sbBreak_suffix hb)

lemma slTrailComments_suffix {n : Nat} {a b : SurfPos} (h : SLTrailComments n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ _ _ hi ht hb hg =>
    exact (((gstar_suffix (fun _ _ => slComment_suffix) hg).trans (sbComment_suffix hb)).trans
      (scNbCommentText_suffix ht)).trans (sIndentLt_suffix hi)

lemma slLiteralContent_suffix {n : Nat} {a b : SurfPos} (h : SLLiteralContent n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ _ _ _ ho hbr he htc hie =>
    exact ((((gopt_suffix (fun _ _ h => sIndentLe_suffix h.1) hie).trans
      (gopt_suffix (fun _ _ => slTrailComments_suffix) htc)).trans
        (gstar_suffix (fun _ _ => sLEmpty_suffix) he)).trans
          (gopt_suffix (fun _ _ => sbBreak_suffix) hbr)).trans
            (gopt_suffix (fun _ _ h => gseq_suffix (fun _ _ => slNbLiteralText_suffix)
              (fun _ _ h => gstar_suffix (fun _ _ => sbNbLiteralNext_suffix) h) h) ho)

/-- **`[170] c-l+literal(n)`**. -/
lemma sclLiteral_suffix {n : Nat} {a b : SurfPos} (h : SCLLiteral n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ rest _ _ _ hh hc =>
    exact ((slLiteralContent_suffix hc).trans (scbBlockHeader_suffix hh)).trans
      (List.suffix_cons '|' rest)

/-- **`[174] c-l+folded(n)`**. -/
lemma sclFolded_suffix {n : Nat} {a b : SurfPos} (h : SCLFolded n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ rest _ _ _ hh hc =>
    exact ((slLiteralContent_suffix hc).trans (scbBlockHeader_suffix hh)).trans
      (List.suffix_cons '>' rest)

/-! ### Four shapes the node grammar repeats

Named once so §4's arms read as the productions they come from. -/

private lemma optSep_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : GOpt (SSeparate n c) a b) : b.chars <:+ a.chars :=
  gopt_suffix (fun _ _ => sSeparate_suffix) h

private lemma optSil_suffix {a b : SurfPos}
    (h : GOpt SSeparateInLine a b) : b.chars <:+ a.chars :=
  gopt_suffix (fun _ _ => sSeparateInLine_suffix) h

private lemma optPropsSep_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : GOpt (GSeq (SCNsProperties n c) (SSeparate n c)) a b) : b.chars <:+ a.chars :=
  gopt_suffix (fun _ _ h => gseq_suffix (fun _ _ => scNsProperties_suffix)
    (fun _ _ => sSeparate_suffix) h) h

private lemma optSepProps_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : GOpt (GSeq (SSeparate n c) (SCNsProperties n c)) a b) : b.chars <:+ a.chars :=
  gopt_suffix (fun _ _ h => gseq_suffix (fun _ _ => sSeparate_suffix)
    (fun _ _ => scNsProperties_suffix) h) h

/-! ## §4 The node grammar: eighteen types, sixty-nine arms

One `mutual` block, one lemma per type of the mutual inductive family in
`Surface/Node.lean`, by structural recursion on the derivation.  `GNot`
premises carry no arm: a negative lookahead constrains a single position and
advances nothing.

This is the price item 228 quoted, paid: 69 arms, and every one of them a
`.trans` chain over premises §1–§3 had to supply first. -/

mutual

lemma sBlockNode_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SBlockNode n c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .blockLiteral _ _ _ _ _ _ hsep hopt hlit =>
    exact (sclLiteral_suffix hlit).trans ((optPropsSep_suffix hopt).trans
      (sSeparate_suffix hsep))
  | .blockFolded _ _ _ _ _ _ hsep hopt hfold =>
    exact (sclFolded_suffix hfold).trans ((optPropsSep_suffix hopt).trans
      (sSeparate_suffix hsep))
  | .blockSeq _ _ _ _ _ _ _ hopt hcm hent =>
    exact (sBlockSeqEntries_suffix hent).trans ((sslComments_suffix hcm).trans
      (optSepProps_suffix hopt))
  | .blockMap _ _ _ _ _ _ _ hopt hcm hent =>
    exact (sBlockMapEntries_suffix hent).trans ((sslComments_suffix hcm).trans
      (optSepProps_suffix hopt))
  | .flowInBlock _ _ _ _ _ _ hsep hn hcm =>
    exact (sslComments_suffix hcm).trans ((sFlowNode_suffix hn).trans (sSeparate_suffix
      hsep))
  | .emptyNode _ _ _ _ hcm =>
    exact (sslComments_suffix hcm)

lemma sBlockIndented_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SBlockIndented n c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .compactSeq _ _ _ _ _ _ hi hs =>
    exact (sCompactSeq_suffix hs).trans (sIndent_suffix hi)
  | .compactMap _ _ _ _ _ _ hi hm =>
    exact (sCompactMap_suffix hm).trans (sIndent_suffix hi)
  | .node _ _ _ _ hn =>
    exact (sBlockNode_suffix hn)
  | .empty _ _ _ _ hcm =>
    exact (sslComments_suffix hcm)

lemma sBlockSeqEntries_suffix {n : Nat} {a b : SurfPos}
    (h : SBlockSeqEntries n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .single _ _ _ _ _ _ hi hl _ hb =>
    exact (sBlockIndented_suffix hb).trans ((glit_suffix hl).trans (sIndent_suffix hi))
  | .cons _ _ _ _ _ _ hi hl _ hb hr =>
    exact (sBlockSeqEntries_suffix hr).trans ((sBlockIndented_suffix hb).trans
      ((glit_suffix hl).trans (sIndent_suffix hi)))

lemma sBlockMapEntry_suffix {n : Nat} {a b : SurfPos}
    (h : SBlockMapEntry n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .explicit _ _ _ _ _ _ _ hq hk hi hc hv =>
    exact (sBlockIndented_suffix hv).trans ((glit_suffix hc).trans ((sIndent_suffix
      hi).trans ((sBlockIndented_suffix hk).trans (glit_suffix hq))))
  | .explicitEmpty _ _ _ _ hq hk =>
    exact (sBlockIndented_suffix hk).trans (glit_suffix hq)
  | .implicitKeyNode _ _ _ _ _ hk hc hv =>
    exact (sBlockNode_suffix hv).trans ((glit_suffix hc).trans (sImplicitKey_suffix hk))
  | .implicitKeyEmpty _ _ _ _ _ hk hc hcm =>
    exact (sslComments_suffix hcm).trans ((glit_suffix hc).trans (sImplicitKey_suffix
      hk))
  | .emptyKeyNode _ _ _ _ hc hv =>
    exact (sBlockNode_suffix hv).trans (glit_suffix hc)
  | .emptyKeyEmpty _ _ _ _ hc hcm =>
    exact (sslComments_suffix hcm).trans (glit_suffix hc)

lemma sBlockMapEntries_suffix {n : Nat} {a b : SurfPos}
    (h : SBlockMapEntries n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .single _ _ _ _ hi he =>
    exact (sBlockMapEntry_suffix he).trans (sIndent_suffix hi)
  | .cons _ _ _ _ _ hi he hr =>
    exact (sBlockMapEntries_suffix hr).trans ((sBlockMapEntry_suffix he).trans
      (sIndent_suffix hi))

lemma sCompactSeq_suffix {n : Nat} {a b : SurfPos}
    (h : SCompactSeq n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ _ hl _ hb ht =>
    exact (sCompactSeqTail_suffix ht).trans ((sBlockIndented_suffix hb).trans
      (glit_suffix hl))

lemma sCompactSeqTail_suffix {n : Nat} {a b : SurfPos}
    (h : SCompactSeqTail n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .nil _ _ =>
    exact List.suffix_refl _
  | .cons _ _ _ _ _ _ hi hl _ hb ht =>
    exact (sCompactSeqTail_suffix ht).trans ((sBlockIndented_suffix hb).trans
      ((glit_suffix hl).trans (sIndent_suffix hi)))

lemma sCompactMap_suffix {n : Nat} {a b : SurfPos}
    (h : SCompactMap n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ he ht =>
    exact (sCompactMapTail_suffix ht).trans (sBlockMapEntry_suffix he)

lemma sCompactMapTail_suffix {n : Nat} {a b : SurfPos}
    (h : SCompactMapTail n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .nil _ _ =>
    exact List.suffix_refl _
  | .cons _ _ _ _ _ hi he ht =>
    exact (sCompactMapTail_suffix ht).trans ((sBlockMapEntry_suffix he).trans
      (sIndent_suffix hi))

lemma sImplicitKey_suffix {a b : SurfPos}
    (h : SImplicitKey a b) :
    b.chars <:+ a.chars := by
  match h with
  | .jsonKey _ _ _ hn ho =>
    exact (optSil_suffix ho).trans (sFlowNode_suffix hn)
  | .yamlKey _ _ _ hp ho =>
    exact (optSil_suffix ho).trans (snsPlain_suffix hp)

lemma sFlowNode_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SFlowNode n c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .alias _ _ _ _ ha =>
    exact (scNsAliasNode_suffix ha)
  | .content _ _ _ _ hc =>
    exact (sFlowContent_suffix hc)
  | .propsContent _ _ _ _ _ _ hp hs hc =>
    exact (sFlowContent_suffix hc).trans ((sSeparate_suffix hs).trans
      (scNsProperties_suffix hp))
  | .propsEmpty _ _ _ _ hp =>
    exact (scNsProperties_suffix hp)

lemma sFlowContent_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SFlowContent n c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .plain _ _ _ _ hp =>
    exact (snsPlain_suffix hp)
  | .flowSeq _ _ _ _ hx =>
    exact (sFlowSequence_suffix hx)
  | .flowMap _ _ _ _ hx =>
    exact (sFlowMapping_suffix hx)
  | .singleQ _ _ _ _ hx =>
    exact (scSingleQuoted_suffix hx)
  | .doubleQ _ _ _ _ hx =>
    exact (scDoubleQuoted_suffix hx)

lemma scFlowJsonContent_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SCFlowJsonContent n c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .flowSeq _ _ _ _ hx =>
    exact (sFlowSequence_suffix hx)
  | .flowMap _ _ _ _ hx =>
    exact (sFlowMapping_suffix hx)
  | .singleQ _ _ _ _ hx =>
    exact (scSingleQuoted_suffix hx)
  | .doubleQ _ _ _ _ hx =>
    exact (scDoubleQuoted_suffix hx)

lemma scFlowJsonNode_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SCFlowJsonNode n c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .content _ _ _ _ hc =>
    exact (scFlowJsonContent_suffix hc)
  | .propsContent _ _ _ _ _ _ hp hs hc =>
    exact (scFlowJsonContent_suffix hc).trans ((sSeparate_suffix hs).trans
      (scNsProperties_suffix hp))

lemma sFlowSequence_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SFlowSequence n c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .empty _ _ _ _ _ _ hl ho hr =>
    exact (glit_suffix hr).trans ((optSep_suffix ho).trans (glit_suffix hl))
  | .nonempty _ _ _ _ _ _ _ hl ho he hr =>
    exact (glit_suffix hr).trans ((sFlowSeqEntries_suffix he).trans ((optSep_suffix
      ho).trans (glit_suffix hl)))

lemma sFlowSeqEntries_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SFlowSeqEntries n c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .single _ _ _ _ _ he ho =>
    exact (optSep_suffix ho).trans (sFlowSeqEntry_suffix he)
  | .consMore _ _ _ _ _ _ _ _ he ho hc ho2 hr =>
    exact (sFlowSeqEntries_suffix hr).trans ((optSep_suffix ho2).trans ((glit_suffix
      hc).trans ((optSep_suffix ho).trans (sFlowSeqEntry_suffix he))))
  | .consEnd _ _ _ _ _ _ _ he ho hc ho2 =>
    exact (optSep_suffix ho2).trans ((glit_suffix hc).trans ((optSep_suffix ho).trans
      (sFlowSeqEntry_suffix he)))

lemma sFlowSeqEntry_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SFlowSeqEntry n c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .node _ _ _ _ hn =>
    exact (sFlowNode_suffix hn)
  | .pairValue _ _ _ _ _ _ _ _ hk ho hc hs hv =>
    exact (sFlowNode_suffix hv).trans ((sSeparate_suffix hs).trans ((glit_suffix
      hc).trans ((optSep_suffix ho).trans (sFlowNode_suffix hk))))
  | .pairEmpty _ _ _ _ _ _ hk ho hc =>
    exact (glit_suffix hc).trans ((optSep_suffix ho).trans (sFlowNode_suffix hk))
  | .pairJsonAdjacentValue _ _ _ _ _ _ _ _ hk ho hc ho2 hv =>
    exact (sFlowNode_suffix hv).trans ((optSep_suffix ho2).trans ((glit_suffix
      hc).trans ((optSep_suffix ho).trans (scFlowJsonNode_suffix hk))))
  | .explicitPairJsonAdjacentValue _ _ _ _ _ _ _ _ _ _ hq hs1 hk ho hc ho2 hv =>
    exact (sFlowNode_suffix hv).trans ((optSep_suffix ho2).trans ((glit_suffix
      hc).trans ((optSep_suffix ho).trans ((scFlowJsonNode_suffix hk).trans
      ((sSeparate_suffix hs1).trans (glit_suffix hq))))))
  | .explicitPairValue _ _ _ _ _ _ _ _ _ _ hq hs1 hk ho hc hs2 hv =>
    exact (sFlowNode_suffix hv).trans ((sSeparate_suffix hs2).trans ((glit_suffix
      hc).trans ((optSep_suffix ho).trans ((sFlowNode_suffix hk).trans
      ((sSeparate_suffix hs1).trans (glit_suffix hq))))))
  | .explicitPairEmpty _ _ _ _ _ _ _ _ hq hs1 hk ho hc =>
    exact (glit_suffix hc).trans ((optSep_suffix ho).trans ((sFlowNode_suffix hk).trans
      ((sSeparate_suffix hs1).trans (glit_suffix hq))))
  | .explicitPairKeyOnly _ _ _ _ _ _ hq hs1 hk =>
    exact (sFlowNode_suffix hk).trans ((sSeparate_suffix hs1).trans (glit_suffix hq))
  | .explicitPairEmptyNodes _ _ _ _ _ hq hs1 =>
    exact (sSeparate_suffix hs1).trans (glit_suffix hq)
  | .emptyKeyValue _ _ _ _ _ _ hc hs hv =>
    exact (sFlowNode_suffix hv).trans ((sSeparate_suffix hs).trans (glit_suffix hc))
  | .emptyKeyEmpty _ _ _ _ hc =>
    exact (glit_suffix hc)
  | .explicitEmptyKeyValue _ _ _ _ _ _ _ _ hq hs1 hc hs2 hv =>
    exact (sFlowNode_suffix hv).trans ((sSeparate_suffix hs2).trans ((glit_suffix
      hc).trans ((sSeparate_suffix hs1).trans (glit_suffix hq))))
  | .explicitEmptyKeyEmpty _ _ _ _ _ _ hq hs1 hc =>
    exact (glit_suffix hc).trans ((sSeparate_suffix hs1).trans (glit_suffix hq))

lemma sFlowMapping_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SFlowMapping n c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .empty _ _ _ _ _ _ hl ho hr =>
    exact (glit_suffix hr).trans ((optSep_suffix ho).trans (glit_suffix hl))
  | .nonempty _ _ _ _ _ _ _ hl ho he hr =>
    exact (glit_suffix hr).trans ((sFlowMapEntries_suffix he).trans ((optSep_suffix
      ho).trans (glit_suffix hl)))

lemma sFlowMapEntries_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SFlowMapEntries n c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .single _ _ _ _ _ he ho =>
    exact (optSep_suffix ho).trans (sFlowMapEntry_suffix he)
  | .consMore _ _ _ _ _ _ _ _ he ho hc ho2 hr =>
    exact (sFlowMapEntries_suffix hr).trans ((optSep_suffix ho2).trans ((glit_suffix
      hc).trans ((optSep_suffix ho).trans (sFlowMapEntry_suffix he))))
  | .consEnd _ _ _ _ _ _ _ he ho hc ho2 =>
    exact (optSep_suffix ho2).trans ((glit_suffix hc).trans ((optSep_suffix ho).trans
      (sFlowMapEntry_suffix he)))

lemma sFlowMapEntry_suffix {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SFlowMapEntry n c a b) :
    b.chars <:+ a.chars := by
  match h with
  | .explicitValue _ _ _ _ _ _ _ _ _ _ hq hs1 hk ho hc hs2 hv =>
    exact (sFlowNode_suffix hv).trans ((sSeparate_suffix hs2).trans ((glit_suffix
      hc).trans ((optSep_suffix ho).trans ((sFlowNode_suffix hk).trans
      ((sSeparate_suffix hs1).trans (glit_suffix hq))))))
  | .explicitEmpty _ _ _ _ _ _ _ _ hq hs1 hk ho hc =>
    exact (glit_suffix hc).trans ((optSep_suffix ho).trans ((sFlowNode_suffix hk).trans
      ((sSeparate_suffix hs1).trans (glit_suffix hq))))
  | .explicitKeyOnly _ _ _ _ _ _ hq hs1 hk =>
    exact (sFlowNode_suffix hk).trans ((sSeparate_suffix hs1).trans (glit_suffix hq))
  | .implicitValue _ _ _ _ _ _ _ _ hk ho hc hs2 hv =>
    exact (sFlowNode_suffix hv).trans ((sSeparate_suffix hs2).trans ((glit_suffix
      hc).trans ((optSep_suffix ho).trans (sFlowNode_suffix hk))))
  | .implicitEmpty _ _ _ _ _ _ hk ho hc =>
    exact (glit_suffix hc).trans ((optSep_suffix ho).trans (sFlowNode_suffix hk))
  | .jsonKeyAdjacentValue _ _ _ _ _ _ _ _ hk ho hc ho2 hv =>
    exact (sFlowNode_suffix hv).trans ((optSep_suffix ho2).trans ((glit_suffix
      hc).trans ((optSep_suffix ho).trans (scFlowJsonNode_suffix hk))))
  | .explicitJsonKeyAdjacentValue _ _ _ _ _ _ _ _ _ _ hq hs1 hk ho hc ho2 hv =>
    exact (sFlowNode_suffix hv).trans ((optSep_suffix ho2).trans ((glit_suffix
      hc).trans ((optSep_suffix ho).trans ((scFlowJsonNode_suffix hk).trans
      ((sSeparate_suffix hs1).trans (glit_suffix hq))))))
  | .bareKey _ _ _ _ hk =>
    exact (sFlowNode_suffix hk)
  | .emptyKeyValue _ _ _ _ _ _ hc hs hv =>
    exact (sFlowNode_suffix hv).trans ((sSeparate_suffix hs).trans (glit_suffix hc))
  | .emptyKeyEmpty _ _ _ _ hc =>
    exact (glit_suffix hc)
  | .explicitEmptyNodes _ _ _ _ _ hq hs1 =>
    exact (sSeparate_suffix hs1).trans (glit_suffix hq)
  | .explicitEmptyKeyValue _ _ _ _ _ _ _ _ hq hs1 hc hs2 hv =>
    exact (sFlowNode_suffix hv).trans ((sSeparate_suffix hs2).trans ((glit_suffix
      hc).trans ((sSeparate_suffix hs1).trans (glit_suffix hq))))
  | .explicitEmptyKeyEmpty _ _ _ _ _ _ hq hs1 hc =>
    exact (glit_suffix hc).trans ((sSeparate_suffix hs1).trans (glit_suffix hq))
end

/-! ## §5 A break inside a span

The span is what makes "this derivation crossed a line" a statement about a
position pair rather than about a derivation, and `BreakBetween` is that
statement.  It is the half of item 228's UNSETTLED question that the suffix
lemma unlocks: a residue that carries a `[28] b-break` in one of its own
components carries a break in its whole span, because the span composes. -/

/-- The characters between two positions include a line break. -/
def BreakBetween (s s' : SurfPos) : Prop :=
  ∃ pre, Span s s' pre ∧ ∃ ch ∈ pre, isLineBreakProp ch

/-- `[28] b-break` puts one there. -/
lemma breakBetween_of_break {a b : SurfPos} (h : SBBreak a b) : BreakBetween a b := by
  match h with
  | .crLf rest _ => exact ⟨['\r', '\n'], rfl, '\r', by simp, by decide⟩
  | .cr rest _ => exact ⟨['\r'], rfl, '\r', by simp, by decide⟩
  | .lf rest _ => exact ⟨['\n'], rfl, '\n', by simp, by decide⟩

/-- Widening on the left keeps the break: the span only grows. -/
lemma breakBetween_extend_left {a b c : SurfPos} (hab : b.chars <:+ a.chars)
    (h : BreakBetween b c) : BreakBetween a c := by
  obtain ⟨pre, hspan, ch, hmem, hbr⟩ := h
  obtain ⟨q, hq⟩ := hab
  refine ⟨q ++ pre, ?_, ch, by simp [hmem], hbr⟩
  simp only [Span] at hspan ⊢
  rw [← hq, hspan, List.append_assoc]

/-- …and so does widening on the right. -/
lemma breakBetween_extend_right {a b c : SurfPos} (hbc : c.chars <:+ b.chars)
    (h : BreakBetween a b) : BreakBetween a c := by
  obtain ⟨pre, hspan, ch, hmem, hbr⟩ := h
  obtain ⟨q, hq⟩ := hbc
  refine ⟨pre ++ q, ?_, ch, by simp [hmem], hbr⟩
  simp only [Span] at hspan ⊢
  rw [hspan, ← hq, List.append_assoc]

/-- **`[113] s-double-break(n)`** crosses a line, on either alternative. -/
lemma ssDoubleBreak_break {n : Nat} {a b : SurfPos} (h : SSDoubleBreak n a b) :
    BreakBetween a b := by
  match h with
  | .escaped _ _ _ he =>
    match he with
    | .mk _ _ _ _ _ _ _ hw hl hb hem hp =>
      refine breakBetween_extend_right ?_ (breakBetween_extend_left ?_ (breakBetween_of_break hb))
      · exact (sFlowLinePrefix_suffix hp).trans (gstar_suffix (fun _ _ => sLEmpty_suffix) hem)
      · exact (glit_suffix hl).trans (gstar_suffix (fun _ _ => sswhite_suffix) hw)
  | .flowFold _ _ _ _ _ hb hem hp =>
    refine breakBetween_extend_right ?_ (breakBetween_of_break hb)
    exact (sFlowLinePrefix_suffix hp).trans (gstar_suffix (fun _ _ => sLEmpty_suffix) hem)

/-- **`[134] s-ns-plain-next-line(n,c)`** crosses a line. -/
lemma ssNsPlainNextLine_break {n : Nat} {c : YamlContext} {a b : SurfPos}
    (h : SSNsPlainNextLine n c a b) : BreakBetween a b := by
  match h with
  | .mk _ _ _ _ _ _ _ _ _ hw hb hem hp hc hg =>
    refine breakBetween_extend_right ?_ (breakBetween_extend_left ?_ (breakBetween_of_break hb))
    · exact (((gstar_suffix (fun _ _ => snbNsPlainInLineEntry_suffix) hg).trans
      (snsPlainChar_suffix hc)).trans
        (sFlowLinePrefix_suffix hp)).trans (gstar_suffix (fun _ _ => sLEmpty_suffix) hem)
    · exact gstar_suffix (fun _ _ => sswhite_suffix) hw

/-! ## §6 The separation trichotomy (DOCS item 230)

§5 gives a residue a consumer can refute WHEN the residue carries a break.
`[69] s-separate(n,c)`'s does not: item 229 exhibited two derivations of
`[70] s-separate-lines(n)`'s comment-delimited arm whose spans carry no break
at all — one empty, one the three characters `' '`, `'#'`, `'c'` — so no
predicate on the span separates that arm from a separation that is simply
inline.  The arm is therefore not a residue; it is an arm.

What IS a residue is read off `[77] b-comment`, which has exactly two ways to
end a comment: a `[28] b-break`, or the end of the input.  Every
comment-delimited separation passes through one of them, so every derivation
of `[70]` either is an inline separation, or crossed a line, or ran the input
out — and the third is refutable by the same consumer as the second, because
a key is followed by a `:` and so does not end the input.

The proof needs the separation grammar to be closed under concatenation,
which `[66] s-separate-in-line` is and the library did not say: `[66]` is
exactly `GStar SSWhite`, `[63] s-indent(n)` is `n` of them, and `[71]
s-flow-line-prefix(n)` is `[63]` followed by an optional `[66]`.  So the whole
second component of `[70]`'s comment-delimited arm is inline and contributes
no residue; the residue comes from `[79] s-l-comments` alone. -/

/-- `GStar` concatenates. -/
lemma gstar_append {P : SurfPos → SurfPos → Prop} {a b c : SurfPos}
    (h₁ : GStar P a b) : GStar P b c → GStar P a c := by
  induction h₁ with
  | nil _ => exact id
  | cons s₁ s₂ _ hx _ ih => exact fun h => GStar.cons s₁ s₂ c hx (ih h)

lemma gstar_of_gplus {P : SurfPos → SurfPos → Prop} {a b : SurfPos}
    (h : GPlus P a b) : GStar P a b := by
  match h with
  | .mk _ _ _ hx hrest => exact GStar.cons _ _ _ hx hrest

/-- **`[66] s-separate-in-line` IS `GStar SSWhite`**, one direction. -/
lemma separateInLine_of_whites {a b : SurfPos} (h : GStar SSWhite a b)
    (h0 : a = b → a.col = 0) : SSeparateInLine a b := by
  cases h with
  | nil _ => exact .startOfLine_of_col0 (h0 rfl)
  | cons _ s₂ _ hx hrest => exact .whites _ _ (GPlus.mk _ s₂ _ hx hrest)

/-- …and the other: the `startOfLine` arm is the empty run. -/
lemma whites_of_separateInLine {a b : SurfPos} (h : SSeparateInLine a b) :
    GStar SSWhite a b := by
  match h with
  | .whites _ _ hp => exact gstar_of_gplus hp
  | .startOfLine _ => exact .nil _

/-- A run of whites in front of an inline separation is one inline separation;
    the empty run adds nothing and asks for nothing. -/
lemma separateInLine_of_whites_trans {a b c : SurfPos} (h : GStar SSWhite a b)
    (h₂ : SSeparateInLine b c) : SSeparateInLine a c := by
  cases h with
  | nil _ => exact h₂
  | cons _ s₂ _ hx hrest =>
    exact .whites _ _ (GPlus.mk _ s₂ _ hx (gstar_append hrest (whites_of_separateInLine h₂)))

/-- **The concatenation lemma for `[66]`.**  Two inline separations end to end
    are one, which is what lets `[71]`'s indent and its optional tail be read
    as a single separation. -/
lemma separateInLine_trans {a b c : SurfPos}
    (h₁ : SSeparateInLine a b) (h₂ : SSeparateInLine b c) : SSeparateInLine a c :=
  separateInLine_of_whites_trans (whites_of_separateInLine h₁) h₂

/-- **`[63] s-indent(n)` is a run of whites** — the spaces it consumes are
    `[33] s-white`s, at every `n`. -/
lemma sIndent_whites {n : Nat} {a b : SurfPos} (h : SIndent n a b) :
    GStar SSWhite a b := by
  induction h with
  | zero s => exact .nil s
  | succ _ rest col _ _ ih =>
    exact GStar.cons ⟨' ' :: rest, col⟩ ⟨rest, col + 1⟩ _ (SSWhite.space rest col) ih

/-- **`[71] s-flow-line-prefix(n)` is an inline separation**, at every `n`.
    This is why the residue below comes from `[79]` alone. -/
lemma sFlowLinePrefix_separateInLine {n : Nat} {a b : SurfPos}
    (h : SFlowLinePrefix n a b) (h0 : a = b → a.col = 0) : SSeparateInLine a b := by
  match h with
  | .mk _ _ _ _ hind hopt =>
    match hopt with
    | .none _ => exact separateInLine_of_whites (sIndent_whites hind) h0
    | .some _ _ hsil => exact separateInLine_of_whites_trans (sIndent_whites hind) hsil

/-- **The end of the input is forward-closed.**  `atEnd` (`Surface.atEnd`, the
    predicate `s.chars = []`) propagates along every production, because every
    production consumes a prefix and a suffix of `[]` is `[]`. -/
lemma atEnd_of_suffix {a b : SurfPos} (hsuf : b.chars <:+ a.chars) (h : atEnd a) :
    atEnd b := by
  obtain ⟨pre, hpre⟩ := hsuf
  simp only [atEnd] at h ⊢
  rw [h] at hpre
  simpa using (List.append_eq_nil_iff.mp hpre).2

/-- Widening the residue on the right: both disjuncts survive. -/
lemma breakOrEnd_extend_right {a b c : SurfPos} (hbc : c.chars <:+ b.chars)
    (h : BreakBetween a b ∨ atEnd b) : BreakBetween a c ∨ atEnd c :=
  h.elim (fun hb => Or.inl (breakBetween_extend_right hbc hb))
    (fun he => Or.inr (atEnd_of_suffix hbc he))

/-- Widening it on the left: only the break half moves, `atEnd` is about the
    right endpoint alone. -/
lemma breakOrEnd_extend_left {a b c : SurfPos} (hab : b.chars <:+ a.chars)
    (h : BreakBetween b c ∨ atEnd c) : BreakBetween a c ∨ atEnd c :=
  h.elim (fun hb => Or.inl (breakBetween_extend_left hab hb)) Or.inr

/-- **`[77] b-comment` ends a comment in exactly two ways**, and both are
    residues: a break, or the end of the input. -/
lemma sbComment_breakOrEnd {a b : SurfPos} (h : SBComment a b) :
    BreakBetween a b ∨ atEnd b := by
  match h with
  | .break _ _ hb => exact Or.inl (breakBetween_of_break hb)
  | .eof _ => exact Or.inr rfl

/-- The shape `[76] s-b-comment` and `[78] l-comment` share, read for its
    residue rather than for its suffix (`comment_body_suffix` is the other
    reading of the same three components). -/
private lemma commentBody_breakOrEnd {s s₁ s₂ s' : SurfPos}
    (hsep : SSeparateInLine s s₁) (hopt : GOpt SCNbCommentText s₁ s₂)
    (hbc : SBComment s₂ s') : BreakBetween s s' ∨ atEnd s' :=
  breakOrEnd_extend_left
    ((gopt_suffix (fun _ _ => scNbCommentText_suffix) hopt).trans
      (sSeparateInLine_suffix hsep))
    (sbComment_breakOrEnd hbc)

/-- **`[76] s-b-comment` always leaves a residue** — it ends in `[77]` on both
    arms. -/
lemma ssbComment_breakOrEnd {a b : SurfPos} (h : SSBComment a b) :
    BreakBetween a b ∨ atEnd b := by
  match h with
  | .withSep _ _ _ _ hsep hopt hbc => exact commentBody_breakOrEnd hsep hopt hbc
  | .noSep _ _ hbc => exact sbComment_breakOrEnd hbc

/-- **`[78] l-comment` likewise.** -/
lemma slComment_breakOrEnd {a b : SurfPos} (h : SLComment a b) :
    BreakBetween a b ∨ atEnd b := by
  match h with
  | .mk _ _ _ _ hsep hopt hbc => exact commentBody_breakOrEnd hsep hopt hbc

/-- A run of `[78]`s is empty, or it leaves a residue.  The empty run is the
    one that keeps `[79]`'s `startOfLine` arm inline. -/
lemma gstarComment_breakOrEnd {a b : SurfPos} (h : GStar SLComment a b) :
    b = a ∨ (BreakBetween a b ∨ atEnd b) := by
  match h with
  | .nil _ => exact Or.inl rfl
  | .cons _ _ _ hx hrest =>
    exact Or.inr (breakOrEnd_extend_right
      (gstar_suffix (fun _ _ => slComment_suffix) hrest) (slComment_breakOrEnd hx))

/-- **`[79] s-l-comments` is zero-width, or it leaves a residue.**  Zero-width
    is `startOfLine` with no comments, so it sits at column 0; every other
    derivation reaches a `[77]`. -/
lemma sslComments_inline_or_breakOrEnd {a b : SurfPos} (h : SSLComments a b) :
    (b = a ∧ a.col = 0) ∨ (BreakBetween a b ∨ atEnd b) := by
  match h with
  | .withComment _ _ _ hsb hstar =>
    exact Or.inr (breakOrEnd_extend_right
      (gstar_suffix (fun _ _ => slComment_suffix) hstar) (ssbComment_breakOrEnd hsb))
  | .startOfLine _ _ hstar =>
    rcases gstarComment_breakOrEnd hstar with rfl | hout
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr hout

/-- **THE TRICHOTOMY.**  `[70] s-separate-lines(n)` is an inline separation,
    or its span carries a `[28] b-break`, or it ran the input out.  The first
    disjunct is what the key contexts have a production for; the other two are
    refuted by a consumer holding "this key crosses no line" and "a `:`
    follows", which is what `[193] c-s-implicit-json-key` supplies. -/
lemma separateLines_inline_or_breakOrEnd {n : Nat} {a b : SurfPos}
    (h : SSeparateLines n a b) :
    SSeparateInLine a b ∨ (BreakBetween a b ∨ atEnd b) := by
  match h with
  | .inline _ _ _ hsil => exact Or.inl hsil
  | .commented _ _ _ _ hcom hpre =>
    rcases sslComments_inline_or_breakOrEnd hcom with ⟨rfl, hcol⟩ | hout
    · exact Or.inl (sFlowLinePrefix_separateInLine hpre (fun _ => hcol))
    · exact Or.inr (breakOrEnd_extend_right (sFlowLinePrefix_suffix hpre) hout)

/-- **`[69] s-separate(n,c)` at the four non-key contexts**, which is the form
    the conversion consumes. -/
lemma separate_inline_or_breakOrEnd {n : Nat} {c : YamlContext} {a b : SurfPos}
    (hc : c = .blockOut ∨ c = .blockIn ∨ c = .flowOut ∨ c = .flowIn)
    (h : SSeparate n c a b) :
    SSeparateInLine a b ∨ (BreakBetween a b ∨ atEnd b) := by
  have h' : SSeparateLines n a b := by
    rcases hc with rfl | rfl | rfl | rfl <;> exact h
  exact separateLines_inline_or_breakOrEnd h'

end L4YAML.Proofs.SurfaceSpan

end Blanket
