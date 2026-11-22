/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Surface.Node
public import L4YAML.Spec.CharPredicates

public meta import L4YAML.Spec.YamlSpec
@[expose] public section Blanket

/-!
# Document & Stream Surface Syntax — Chapter 9

Surface syntax predicates for YAML document boundaries, document markers,
and stream-level composition.

## Productions Covered

- **Document markers**: c-forbidden, c-directives-end,
  c-document-end
- **Document types**: l-bare-document, l-explicit-document,
  l-directive-document
- **Stream**: [206]-[211] l-any-document, l-yaml-stream
-/

set_option autoImplicit false

namespace L4YAML.Surface

open L4YAML (YamlContext)
open L4YAML.CharPredicates

/-! ## §1 Document Markers -/

/-- Helper: the characters after '---' or '...' must be whitespace,
    line break, or end of input. -/
def isMarkerFollower : List Char → Prop
  | [] => True
  | c :: _ => isWhiteSpaceProp c ∨ isLineBreakProp c

/-- [206] c-forbidden: document boundary markers at column 0.
    Matches '---' or '...' at column 0 followed by whitespace/break/eof. -/
@[yaml_spec "9.1.2" 206 "c-forbidden"]
inductive SCForbidden : SurfPos → Prop where
  | directivesEnd (rest : List Char)
      (hFollow : isMarkerFollower rest) :
      SCForbidden ⟨'-' :: '-' :: '-' :: rest, 0⟩
  | documentEnd (rest : List Char)
      (hFollow : isMarkerFollower rest) :
      SCForbidden ⟨'.' :: '.' :: '.' :: rest, 0⟩

/-- [203] c-directives-end: the '---' marker.
    Must be at column 0. Consumes 3 characters, advancing to column 3. -/
@[yaml_spec "9.1.2" 203 "c-directives-end"]
inductive SCDirectivesEnd : SurfPos → SurfPos → Prop where
  | mk (rest : List Char) :
      SCDirectivesEnd ⟨'-' :: '-' :: '-' :: rest, 0⟩ ⟨rest, 3⟩

/-- [204] c-document-end: the '...' marker.
    Must be at column 0. Consumes 3 characters, advancing to column 3. -/
@[yaml_spec "9.1.2" 204 "c-document-end"]
inductive SCDocumentEnd : SurfPos → SurfPos → Prop where
  | mk (rest : List Char) :
      SCDocumentEnd ⟨'.' :: '.' :: '.' :: rest, 0⟩ ⟨rest, 3⟩

/-! ## §2 Document Types -/

/-- [207] l-bare-document: document without explicit markers.
    Content is a block node at indent -1 (top level).
    We use indent = 0 since Nat can't represent -1; hence n_lean = n_spec + 1
    throughout (spec's -1 maps to our 0, spec's 0 maps to our 1, etc.).
    SBlockNode constructors use n directly (not n+1) to match this convention. -/
@[yaml_spec "9.1.3" 207 "l-bare-document"]
inductive SLBareDocument : SurfPos → SurfPos → Prop where
  | mk (s s' : SurfPos) :
      SBlockNode 0 .blockIn s s' →
      SLBareDocument s s'

/-- [208] l-explicit-document: '---' + content or empty.
    The content starts after the '---' marker. -/
@[yaml_spec "9.1.4" 208 "l-explicit-document"]
inductive SLExplicitDocument : SurfPos → SurfPos → Prop where
  | withContent (s s₁ s' : SurfPos) :
      SCDirectivesEnd s s₁ →
      GAlt SLBareDocument (GSeq SENode SSLComments) s₁ s' →
      SLExplicitDocument s s'

/-- [209] l-directive-document: directives + '---' + content.
    One or more directives followed by an explicit document. -/
@[yaml_spec "9.1.5" 209 "l-directive-document"]
inductive SLDirectiveDocument : SurfPos → SurfPos → Prop where
  | mk (s s₁ s' : SurfPos) :
      GPlus SLDirective s s₁ →
      SLExplicitDocument s₁ s' →
      SLDirectiveDocument s s'

/-- [210] l-any-document: any document form. -/
@[yaml_spec "9.2" 210 "l-any-document"]
inductive SLAnyDocument : SurfPos → SurfPos → Prop where
  | directive (s s' : SurfPos) :
      SLDirectiveDocument s s' → SLAnyDocument s s'
  | explicit (s s' : SurfPos) :
      SLExplicitDocument s s' → SLAnyDocument s s'
  | bare (s s' : SurfPos) :
      SLBareDocument s s' → SLAnyDocument s s'

/-! ## §3 Stream

The YAML stream is the top-level grammar production. It represents one
or more documents separated by document markers, with optional leading
and trailing comments/whitespace.

[211] l-yaml-stream ::=
  l-document-prefix* l-any-document?
  ( l-document-suffix+ l-document-prefix* l-any-document?
  | l-document-prefix* l-explicit-document? )* -/

/-- [202] l-document-prefix: optional BOM + l-comment*.
    Simplified: just comments (BOM is a single-character check).

    **The BOM spends no column** (§5.2, item 35).  `[3] c-byte-order-mark`
    is an encoding marker rather than content — in UTF-8 it "is not
    considered part of the content" — so the character after it opens the
    line at the SAME column the marker stood at, and `[63] s-indent(n)` on
    the first line is counted from there.  Carrying `col + 1` made the
    first line one deeper than every other: `﻿a: 1⏎b: 2` dedents below
    its own `[187] l+block-mapping`, and `﻿---` sits off column 0, where
    `[203] c-directives-end` cannot be read at all. -/
@[yaml_spec "9.1.1" 202 "l-document-prefix",
  yaml_spec "5.2" 3 "c-byte-order-mark"]
inductive SLDocumentPrefix : SurfPos → SurfPos → Prop where
  | comments (s s' : SurfPos) :
      GStar SLComment s s' → SLDocumentPrefix s s'
  | bom (rest : List Char) (col : Nat) (s' : SurfPos) :
      GStar SLComment ⟨rest, col⟩ s' →
      SLDocumentPrefix ⟨'\uFEFF' :: rest, col⟩ s'

/-- [205] l-document-suffix: '...' + s-l-comments. -/
@[yaml_spec "9.1.2" 205 "l-document-suffix"]
inductive SLDocumentSuffix : SurfPos → SurfPos → Prop where
  | mk (s s₁ s' : SurfPos) :
      SCDocumentEnd s s₁ → SSLComments s₁ s' →
      SLDocumentSuffix s s'

/-- [211] l-yaml-stream: the complete YAML stream.
    One or more documents with prefixes and suffixes.
    This is the top-level surface syntax production. -/
@[yaml_spec "9.2" 211 "l-yaml-stream"]
inductive SLYamlStream : SurfPos → SurfPos → Prop where
  /-- Single document (possibly bare, explicit, or directive). -/
  | single (s s₁ s₂ s' : SurfPos) :
      GStar SLDocumentPrefix s s₁ →
      GOpt SLAnyDocument s₁ s₂ →
      GStar SLDocumentSuffix s₂ s' →
      SLYamlStream s s'
  /-- Multiple documents: previous stream + suffix(es) + prefix(es) + next document. -/
  | suffixContinue (s s₁ s₂ s₃ s₄ s' : SurfPos) :
      SLYamlStream s s₁ →
      GPlus SLDocumentSuffix s₁ s₂ →
      GStar SLDocumentPrefix s₂ s₃ →
      GOpt SLAnyDocument s₃ s₄ →
      GStar SLDocumentSuffix s₄ s' →
      SLYamlStream s s'
  /-- Implicit continuation: previous stream + prefix(es) + any document.
      Matches spec [211] `l-document-prefix* l-any-document?` branch.
      This includes bare documents (no `---` marker). -/
  | implicitContinue (s s₁ s₂ s₃ s' : SurfPos) :
      SLYamlStream s s₁ →
      GStar SLDocumentPrefix s₁ s₂ →
      GOpt SLAnyDocument s₂ s₃ →
      GStar SLDocumentSuffix s₃ s' →
      SLYamlStream s s'
  /-- Scanner content absorption: previous stream + opaque scanned content
      + trailing SSLComments. When the scanner processes flow indicators
      (`[`, `{`, `]`, `}`, `,`) or block indicators (`-`, `?`, `:`) that
      don't correspond to a complete grammar production at closing time, the
      stream absorbs the gap. The SSLComments evidence anchors the endpoint.
      Grammar over-approximation — the gap s₁→s₂ is opaque.

      **The opacity costs the suffix law.** `s₁` and `s₂` are unrelated, so
      this arm concludes `SLYamlStream s s'` from evidence that never connects
      `s` to `s'`: `[211]` derives pairs whose target holds characters the
      source never had, and `s'.chars <:+ s.chars` is false at this production.
      `Tests/Guards/Proofs/ColumnWalkPrice.lean` §6 (DOCS item 235) carries the
      derivation and the refutation. Retiring this constructor is what row 12's
      β.5 names, and it is also what a span or column proof of the stream
      waits on.  It is the only thing such a proof waits on: this is the one
      arm of the surface grammar's one hundred and sixty-seven whose premises
      leave the conclusion's target unconnected to its source, and every other
      production carries its suffix lemma — `SurfaceSpanSupply.lean` and
      `Tests/Guards/Proofs/SuffixGapAudit.lean` (DOCS item 236).

      **What retiring it costs.**  Two proofs in the library build this arm —
      `dropClose` and `PendingNode.close_with_ssl`, both in
      `Proofs/Production/StreamAccum.lean` — and twenty-six run through it,
      ending at the two Group 7 capstones.  Nothing anywhere case-splits on
      `SLYamlStream`, so the deletion costs nothing on the side a removed
      constructor usually costs the most.  No statement in the library names
      the constructor, so the repair propagates only where a statement must
      change, and exactly two are candidates:
      `Tests/Guards/Proofs/DropDependents.lean` (DOCS item 238).

      **Both of those two are false without it, and nothing else is.**  Six of
      the twenty-six are refutable once the suffix law holds — `dropClose`,
      `PendingNode.close_with_ssl` and four guard exhibits written to witness
      the defect.  The other twenty conclude at a target the law cannot
      forbid: ten end at `chars = []`, where `[] <:+ anything`, and nine bind
      the target existentially, where the law is a constraint on the witness
      rather than a contradiction.  So β.5 restates two statements and reproves
      twenty-four, and Group 7's own statements are all in the first of those
      two classes and none of them is FALSE.  `dropClose` is false
      unconditionally; `close_with_ssl` is false in the environment that
      deletes this arm and keeps `PendingNode.pendingFlow`, the only park arm
      with the same gap — which is why row 12 names both halves of β.5 in one
      item.  `Tests/Guards/Proofs/DropFalsity.lean` (DOCS item 239).

      **How many statements change is a CHOICE, and the choice is between two
      threads.**  `close_with_ssl` can be repaired by a premise connecting the
      park's two positions, by that same connection as a FIELD on
      `PendingNode.pendingFlow`, or by retiring the park; the three flips
      break 5, 1 and 7 definitions and travel three different edges, so the
      counts are not a ratio.  Only the premise changes `close_with_ssl`'s own
      TYPE, and it changes nineteen statements above it — the whole reverse
      closure, out to both capstones and to `parse_strict`/`scan_strict` —
      because no statement on that closure holds a stream to the park's scan
      position and the park cannot supply one.  All nineteen are inside the
      twenty-six, so that repair moves items between restated and reproved
      without moving the total: `Tests/Guards/Proofs/RepairChoice.lean`
      (DOCS item 240).

      The FIELD repair changes no consumer of `close_with_ssl`, and that is
      the whole of what it saves.  It relocates the connection onto the park's
      PRODUCER, `block_dispatch_deferred`, which holds a `ScannerSurfCorr` at
      the scan position and cannot derive the connection from it — a
      correspondence is a statement about a POINT and the connection is a
      statement about a PATH, and the library derives one from the other at
      the stream's seed and nowhere else.  So the premise is threaded there
      too, and the producer's own reverse closure is eighteen declarations,
      ending at the same `parse_strict`, with SEVEN of them outside the
      twenty-six entirely.  The two closures share eleven and cover
      twenty-six between them:
      `Tests/Guards/Proofs/ProducerDerivation.lean` (DOCS item 241).

      **And the CONNECTED form of this arm is a THEOREM, so none of that
      price is the step's.**  `s₁` and `s₂` below are unrelated, which is
      what makes the arm hold of every string; identify them and
      `implicitContinue` derives it, through `SLDocumentPrefix.comments` and
      the fact that an `s-b-comment` is an `l-comment`.  Three lines, and the
      same three hold in the relation with this arm DELETED, which is the
      check that the derivation is not circular.  So the reproofs β.5 owes
      need no new grammar lemma: what the repairs above price is the
      CONNECTION, not the proof.  The derivation spends
      `SSeparateInLine.startOfLine`, which holds only at column 0, so the
      escape is available exactly where the comment sits at a line start:
      `Tests/Guards/Proofs/DispatchPrice.lean` (DOCS item 242).

      **The connected form closes none of the sites that spend this arm.**
      It is applied at eleven places in the tree, and at none of them are
      `s₁` and `s₂` the same expression, reducibly defeq, equated by a
      hypothesis in scope, or forced equal by a pair of correspondences.
      Five of the eleven hold a `ScannerSurfCorr` at `s₂` — every one at the
      state of the `PendingNode` being closed — and none holds one at `s₁`,
      because a park holding both has `s₁ = s₂` and therefore absorbed no
      characters.  So the gap admits exactly two closures, identifying the
      endpoints or deriving a path across them, and identification is the
      empty park.  The price is owed once per CALL, which is six, and not
      once per dependent: `Tests/Guards/Proofs/ParkGapCensus.lean`
      (DOCS item 243).

      **Each of those six calls is ONE scanner step wide, and the step is one
      character.**  The gap is fixed where the park is built, not where it is
      spent: `block_dispatch_deferred` binds `s₁` free under a stream and pins
      `s₂` with a correspondence.  Read at the producer's twelve application
      sites, six hold a grammar path from `s₁` up to a block-indicator
      dispatch's input and owe only that dispatch; one owes a preprocessing
      step beside it; the other five reach nothing.  The dispatch is exactly
      one `ScannerState.advance` — all three of `scanBlockEntry`, `scanKey` and
      `scanValue` emit, push at most one indent and advance once — so the
      production owed across it is a single `GLit` for `-`, `?` or `:`:
      `[184] c-l-block-seq-entry`, `[190] c-l-block-map-explicit-key` or
      `[6] c-mapping-value`.  **What the six owe is a literal, not an
      induction.**  What makes it unpaid is the other census:
      `scanNextToken_dispatchBlockIndicators` has ninety-seven holders and not
      one of them carries a production across it, where the content dispatch
      carries one and preprocessing six:
      `Tests/Guards/Proofs/ParkGapWidth.lean` (DOCS item 244).

      **And the literal has nowhere to land.**  The path from `s₁` up to the
      dispatch's input is ONE edge and it is whitespace — `GStar SSWhite` or
      `SIndent` — so the indicator the dispatch scans opens a construct rather
      than closing one.  Thirty of the library's two hundred and thirty-five
      production constructors end at a literal; twenty-three of the thirty end
      at one of the three block indicators; and every one of the twenty-three
      is a FLOW form — `MapFrame`, `SeqFrame`, `PendingFlowMapEntry`,
      `PendingFlowSeqEntry`, `SFlowMapEntry`, `SFlowSeqEntry`.  `-` ends no
      production anywhere.  The twenty-three that exist need a frame, and
      `block_dispatch_deferred` parks with `BlockStack.nil` beside a
      depth-zero `FlowStackB`, both of which force their two positions equal,
      so neither carrier it hands its consumer can hold a character.  Composed
      into the grammar's own entry constructor the literal is premise two of
      `SBlockSeqEntries.single`, whose conclusion ends where the ENTRY'S
      CONTENT ends: **what the six owe is a block node, not a character** —
      `Tests/Guards/Proofs/ParkGapProduction.lean` (DOCS item 245). -/
  | scannerDrop (s s₁ s₂ s' : SurfPos) :
      SLYamlStream s s₁ →
      SSLComments s₂ s' →
      SLYamlStream s s'

/-! ## Top-Level Predicate -/

/-- A string is a valid YAML stream according to the surface syntax grammar.

    This is the input-level specification: the string's characters conform
    to the YAML 1.2.2 productions [1]–[211], consuming the entire input.

    **`SLYamlStream.scannerDrop` makes this predicate hold of EVERY string.**
    That arm relates `s` to `s'` from premises that never connect them, so
    `SLYamlStream ⟨s.toList, 0⟩ ⟨[], 0⟩` is derivable for any `s` and the
    second conjunct is `rfl` — `inYamlLanguage_everything` in
    `Tests/Guards/Proofs/SuffixGapAudit.lean` §5 (DOCS item 236).  Every
    theorem concluding `InYamlLanguage` is therefore true for a reason that
    has nothing to do with its hypothesis, and stays that way until row 12's
    β.5 retires the constructor. -/
def InYamlLanguage (s : String) : Prop :=
  ∃ s' : SurfPos,
    SLYamlStream ⟨s.toList, 0⟩ s' ∧ s'.chars = []

/-- The indent consumed by the scanner corresponds to `SIndent n` in
    the surface syntax. This is the simplest coupling theorem and
    serves as a template for more complex ones. -/
lemma indent_coupling (n : Nat) (cs : List Char) (col : Nat) :
    cs.take n = List.replicate n ' ' →
    cs.length ≥ n →
    SIndent n ⟨cs, col⟩ ⟨cs.drop n, col + n⟩ := by
  induction n generalizing cs col with
  | zero => intros; exact SIndent.zero _
  | succ k ih =>
    intro hrep hlen
    match cs, hlen with
    | c :: rest, hlen =>
      simp [List.replicate_succ] at hrep
      obtain ⟨hc, hrest_rep⟩ := hrep
      subst hc
      have hlen' : rest.length ≥ k := by simp at hlen; omega
      have ih_result := ih rest (col + 1) hrest_rep hlen'
      have hcol : col + 1 + k = col + (k + 1) := by omega
      rw [hcol] at ih_result
      exact SIndent.succ k rest col _ ih_result

end L4YAML.Surface

end Blanket
