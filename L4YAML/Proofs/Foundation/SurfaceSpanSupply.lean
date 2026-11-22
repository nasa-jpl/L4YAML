/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Surface.Surface
public import L4YAML.Proofs.Foundation.SurfaceSpan

@[expose] public section Blanket

/-!
# The rest of the span supply

`SurfaceSpan.lean` proves `b.chars <:+ a.chars` for sixty-nine of the
ninety-two productions a surface-grammar walk can cite.  This module carries
the remaining twenty-two.  The ninety-third — `[211] l-yaml-stream` — has no
such lemma because the statement is FALSE: `SLYamlStream.scannerDrop` relates
its two premises at unconnected positions, and the derivation refuting the
suffix law is in `Tests/Guards/Proofs/SuffixGapAudit.lean` (DOCS item 236).

## What decides which side a production falls on

A constructor carries the suffix law when its PREMISES connect the
conclusion's source to the conclusion's target — through a cited production,
or through characters the arm consumes literally.  One arm of the surface
grammar's one hundred and sixty-seven does not, and it is `scannerDrop`.  The
census is machine-checked in the audit file's §1.

## Seven of the twenty-two need nothing at all

`SBAsLineFeed`, `SBNonContent`, `SBlockLinePrefix`, `SCommentChar`, `SNsChar`,
`SNbChar` and `SENode` are `abbrev`s for `SBBreak`, `SIndent`, `GChar` at three
predicates, and `GEps`.  A walk cites the aliased production's own lemma at
each of them, unchanged, so they cost no statement — item 229's reading, whose
census reports five of them uncovered for exactly this reason.  A census that
tests a lemma's TYPE for the production's name cannot see through an alias,
which is why two instruments over the same grammar disagree by seven; the
audit file's §2 reports the split rather than closing it with restatements.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.SurfaceSpan

open L4YAML.Surface

/-! ## §1 The four remaining combinators

`GEps` and `GConsumeAll` carry the law outright.  `GAlt` and `GSeq3` are
parameterized, so they carry it exactly as `GSeq`, `GStar`, `GPlus` and `GOpt`
do — one hypothesis per parameter. -/

/-- **`GEps` consumes nothing**, so its target is its source. -/
lemma geps_suffix {a b : SurfPos} (h : GEps a b) : b.chars <:+ a.chars := by
  cases h; exact List.suffix_refl _

/-- **`GConsumeAll` consumes a prefix** — every character, in fact. -/
lemma gconsumeAll_suffix {a b : SurfPos} (h : GConsumeAll a b) :
    b.chars <:+ a.chars := by
  induction h with
  | nil col => exact List.suffix_refl _
  | cons c rest col s' _ ih => exact ih.trans (List.suffix_cons c rest)

/-- **`GAlt` consumes a prefix when both alternatives do.** -/
lemma galt_suffix {P Q : SurfPos → SurfPos → Prop} {a b : SurfPos}
    (hP : ∀ x y, P x y → y.chars <:+ x.chars)
    (hQ : ∀ x y, Q x y → y.chars <:+ x.chars) (h : GAlt P Q a b) :
    b.chars <:+ a.chars := by
  match h with
  | .left _ _ hp => exact hP _ _ hp
  | .right _ _ hq => exact hQ _ _ hq

/-- **`GSeq3` consumes a prefix when all three factors do.** -/
lemma gseq3_suffix {P Q R : SurfPos → SurfPos → Prop} {a b : SurfPos}
    (hP : ∀ x y, P x y → y.chars <:+ x.chars)
    (hQ : ∀ x y, Q x y → y.chars <:+ x.chars)
    (hR : ∀ x y, R x y → y.chars <:+ x.chars) (h : GSeq3 P Q R a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ hp hq hr =>
    exact ((hR _ _ hr).trans (hQ _ _ hq)).trans (hP _ _ hp)

/-! ## §2 Directives and folded scalar lines -/

/-- **`[82] l-directive` consumes a prefix.**  The `%` is consumed literally;
    the trailing body is a comment-character run and a `[79] s-l-comments`. -/
lemma slDirective_suffix {a b : SurfPos} (h : SLDirective a b) :
    b.chars <:+ a.chars := by
  match h with
  | .yaml rest _ _ _ _ _ _ _ hw hd1 hdot hd2 hc =>
    exact (((((sslComments_suffix hc).trans
      (gplus_suffix (fun _ _ => gchar_suffix) hd2)).trans
      (glit_suffix hdot)).trans
      (gplus_suffix (fun _ _ => gchar_suffix) hd1)).trans
      (gstar_suffix (fun _ _ => sswhite_suffix) hw)).trans
      ⟨['%', 'Y', 'A', 'M', 'L'], rfl⟩
  | .tag rest _ _ _ _ _ _ _ hw hh _ hw2 hp hc =>
    exact (((((sslComments_suffix hc).trans
      (gstar_suffix (fun _ _ => gchar_suffix) hp)).trans
      (gstar_suffix (fun _ _ => sswhite_suffix) hw2)).trans
      (gstar_suffix (fun _ _ => gchar_suffix) hh)).trans
      (gstar_suffix (fun _ _ => sswhite_suffix) hw)).trans
      ⟨['%', 'T', 'A', 'G'], rfl⟩
  | .reserved rest _ _ _ _ hg _ _ _ hsk hc =>
    exact (((sslComments_suffix hc).trans
      (gstar_suffix (fun _ _ => gchar_suffix) hsk)).trans
      (gstar_suffix (fun _ _ => gchar_suffix) hg)).trans
      (List.suffix_cons '%' rest)

/-- **`[175] s-nb-folded-text(n)` consumes a prefix.** -/
lemma ssNbFoldedText_suffix {n : Nat} {a b : SurfPos} (h : SSNbFoldedText n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ hi hp =>
    exact (gplus_suffix (fun _ _ => gchar_suffix) hp).trans (sIndent_suffix hi)

/-- **`[176] l-nb-folded-lines(n)` consumes a prefix.** -/
lemma slNbFoldedLines_suffix {n : Nat} {a b : SurfPos} (h : SLNbFoldedLines n a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ _ ht hg =>
    exact (gstar_suffix (fun _ _ hs =>
      gseq_suffix (fun _ _ => sbBreak_suffix) (fun _ _ => ssNbFoldedText_suffix) hs) hg).trans
      (ssNbFoldedText_suffix ht)

/-! ## §3 The document layer

`Surface/Node.lean` imports `Surface/Scalars.lean`, not `Surface/Document.lean`,
so `SurfaceSpan.lean`'s closure stops one layer below these eight.  Each of
the eight is a single lemma citing the layer beneath it. -/

/-- **`[203] c-directives-end` consumes `---`.** -/
lemma scDirectivesEnd_suffix {a b : SurfPos} (h : SCDirectivesEnd a b) :
    b.chars <:+ a.chars := by
  cases h with
  | mk _ => exact ⟨['-', '-', '-'], rfl⟩

/-- **`[204] c-document-end` consumes `...`.** -/
lemma scDocumentEnd_suffix {a b : SurfPos} (h : SCDocumentEnd a b) :
    b.chars <:+ a.chars := by
  cases h with
  | mk _ => exact ⟨['.', '.', '.'], rfl⟩

/-- **`[207] l-bare-document` consumes a prefix.** -/
lemma slBareDocument_suffix {a b : SurfPos} (h : SLBareDocument a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ hb => exact sBlockNode_suffix hb

/-- **`[208] l-explicit-document` consumes a prefix.** -/
lemma slExplicitDocument_suffix {a b : SurfPos} (h : SLExplicitDocument a b) :
    b.chars <:+ a.chars := by
  match h with
  | .withContent _ _ _ hd ha =>
    exact (galt_suffix (fun _ _ => slBareDocument_suffix)
      (fun _ _ => gseq_suffix (fun _ _ => geps_suffix)
        (fun _ _ => sslComments_suffix)) ha).trans (scDirectivesEnd_suffix hd)

/-- **`[209] l-directive-document` consumes a prefix.** -/
lemma slDirectiveDocument_suffix {a b : SurfPos} (h : SLDirectiveDocument a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ hp he =>
    exact (slExplicitDocument_suffix he).trans
      (gplus_suffix (fun _ _ => slDirective_suffix) hp)

/-- **`[210] l-any-document` consumes a prefix.** -/
lemma slAnyDocument_suffix {a b : SurfPos} (h : SLAnyDocument a b) :
    b.chars <:+ a.chars := by
  match h with
  | .directive _ _ hd => exact slDirectiveDocument_suffix hd
  | .explicit _ _ he => exact slExplicitDocument_suffix he
  | .bare _ _ hb => exact slBareDocument_suffix hb

/-- **`[202] l-document-prefix` consumes a prefix.**  The byte-order mark
    spends no column, and it does spend a character. -/
lemma slDocumentPrefix_suffix {a b : SurfPos} (h : SLDocumentPrefix a b) :
    b.chars <:+ a.chars := by
  match h with
  | .comments _ _ hg => exact gstar_suffix (fun _ _ => slComment_suffix) hg
  | .bom rest _ _ hg =>
    exact (gstar_suffix (fun _ _ => slComment_suffix) hg).trans (List.suffix_cons _ rest)

/-- **`[205] l-document-suffix` consumes a prefix.** -/
lemma slDocumentSuffix_suffix {a b : SurfPos} (h : SLDocumentSuffix a b) :
    b.chars <:+ a.chars := by
  match h with
  | .mk _ _ _ hd hc => exact (sslComments_suffix hc).trans (scDocumentEnd_suffix hd)

end L4YAML.Proofs.SurfaceSpan

end Blanket
