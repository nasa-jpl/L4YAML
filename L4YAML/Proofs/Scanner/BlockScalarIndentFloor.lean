/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Production.ScalarProduction

@[expose] public section Blanket

/-!
# The block scalar's detected content indent, kept (DOCS item 26)

`scanBlockScalar_prod` (`ScalarProduction`) reads a `|`/`>` header and its body
and concludes `SCLLiteral 0 ∨ SCLFolded 0`.  The `0` is not a fact about block
scalars: `[170] c-l+literal(n)` is `"|" c-b-block-header(m,t) l-literal-content(n+m,t)`
and the constructor binds `m` existentially, so the reading holds at every `n`
for which an `m` exists — that is, at every `n ≤` the indent the body was
actually collected at.  The scanner MEASURES that indent (`contentIndent`) and
the production lemma then throws it away by instantiating `n := 0`, which is
Reflection 651's shape: a constant in a conclusion is a quantity declined.

So the body's own floor is what has to survive.  `scanBlockScalarBody`
(`Scanner/Scalar.lean`) computes

    parentIndent     := s_orig.currentIndent
    minContentIndent := (max 0 (parentIndent + 1)).toNat
    contentIndent    := match explicitOffset with
                        | some m => (max 0 (parentIndent + m)).toNat   -- m ≥ 1
                        | none   => autoDetect … minContentIndent …

and both halves of `minContentIndent ≤ contentIndent` are already proven —
`parseBlockHeaderLoop_offset_preserves` (the digit `0` is refused, so `m ≥ 1`)
and `autoDetectBlockScalarIndent_ge_min` (the detector's answer is a `max` with
the floor).  This module composes them and hands the accumulator the reading at
every index the floor admits.

`scanBlockScalar_prod` itself is left alone: its `n = 0` conclusion is what the
column-0 arms consume, and keeping both is the same "narrower sibling, not a
generalisation" split item 23 made for the one-line content reading.

Kept out of `ScalarProduction` deliberately — a satellite module imported by
`StreamAccum` rebuilds only itself, whereas editing `ScalarProduction` rebuilds
`StructureProduction` and `NodeProduction` on the way.
-/

namespace L4YAML.Proofs.BlockScalarIndentFloor

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Grammar
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScannerCoupling
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.ScalarProduction
open L4YAML (ChompStyle)

/-! ## §1  The body's floor

`scanBlockScalarBody_literal_prod` / `_folded_prod` already name the exact
`contentIndent` term in both branches; the only difference between them is the
post-processing of the collected string, which touches neither position nor
correspondence.  So this is ONE lemma, parametric in `isLiteral`, with the floor
added to the existential. -/

/-- The indent `scanBlockScalarBody` collects at is at least the parent's own
    `minContentIndent` — `[170]`/`[174]`'s `n + m` with `m ≥ 1` read off the
    runtime.  The `explicitOffset` hypothesis is discharged at the call site by
    `parseBlockHeaderLoop_offset_preserves`. -/
lemma scanBlockScalarBody_contentIndent_floor
    (sc_orig sc_after_nl : ScannerState) (sp : SurfPos)
    (chomp : ChompStyle) (explicitOffset : Option Nat)
    (isLiteral : Bool) (startPos : YamlPos) {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc_after_nl sp)
    (hoff : ∀ d, explicitOffset = some d → d ≥ 1)
    (h_ie : sc_after_nl.inputEnd ≤ sc_orig.inputEnd)
    (hok : scanBlockScalarBody sc_orig sc_after_nl chomp explicitOffset isLiteral startPos
           = .ok s') :
    ∃ sp' contentIndent,
      (max 0 (sc_orig.currentIndent + 1)).toNat ≤ contentIndent ∧
      SLLiteralContent contentIndent sp sp' ∧ ScannerSurfCorr s' sp' ∧
      (∀ sp_mid : SurfPos, SSLComments sp' sp_mid →
        SLLiteralContent contentIndent sp sp_mid) := by
  unfold scanBlockScalarBody at hok
  dsimp only [] at hok
  cases hoff_eq : explicitOffset with
  | some d =>
    rw [hoff_eq] at hok
    have hd : d ≥ 1 := hoff d hoff_eq
    let contentIndent := (max 0 (sc_orig.currentIndent + (↑d : Int))).toNat
    let fuel := sc_orig.inputEnd - sc_after_nl.offset + 1
    obtain ⟨sp_loop, h_lit_content, hcorr_loop, h_absorb⟩ :=
      collectBlockScalarLoop_literal_prod sc_after_nl sp "" fuel contentIndent sc_orig.inputEnd hcorr
        (Nat.le_refl _) h_ie
    dsimp only [] at hok
    split at hok
    · cases hok
    rename_i h_gate
    have h := Except.ok.inj hok; subst h
    refine ⟨sp_loop, contentIndent, ?_, h_lit_content,
            ⟨hcorr_loop.chars_from, hcorr_loop.col_eq, hcorr_loop.end_eq,
             hcorr_loop.input_prefix, hcorr_loop.indent_cols_nonneg⟩,
            h_absorb.resolve_right (not_blockScalarTabStop_of_gate hcorr_loop h_gate)⟩
    show (max 0 (sc_orig.currentIndent + 1)).toNat
         ≤ (max 0 (sc_orig.currentIndent + (↑d : Int))).toNat
    omega
  | none =>
    rw [hoff_eq] at hok
    generalize h_auto : autoDetectBlockScalarIndent sc_after_nl
      (max 0 (sc_orig.currentIndent + 1)).toNat sc_orig.inputEnd = auto_res at hok
    obtain ⟨ci, err⟩ := auto_res
    simp only [] at h_auto hok
    cases h_err : err with
    | some e =>
      simp only [h_err] at hok
      cases hok
    | none =>
      simp only [h_err] at hok
      have h_ge : (max 0 (sc_orig.currentIndent + 1)).toNat ≤ ci := by
        have := autoDetectBlockScalarIndent_ge_min sc_after_nl
          (max 0 (sc_orig.currentIndent + 1)).toNat sc_orig.inputEnd
        rw [h_auto] at this
        exact this (by simp [h_err])
      let fuel := sc_orig.inputEnd - sc_after_nl.offset + 1
      obtain ⟨sp_loop, h_lit_content, hcorr_loop, h_absorb⟩ :=
        collectBlockScalarLoop_literal_prod sc_after_nl sp "" fuel ci sc_orig.inputEnd hcorr
          (Nat.le_refl _) h_ie
      split at hok
      · cases hok
      · rename_i h_gate
        have h := Except.ok.inj hok; subst h
        exact ⟨sp_loop, ci, h_ge, h_lit_content,
               ⟨hcorr_loop.chars_from, hcorr_loop.col_eq, hcorr_loop.end_eq,
                hcorr_loop.input_prefix, hcorr_loop.indent_cols_nonneg⟩,
               h_absorb.resolve_right (not_blockScalarTabStop_of_gate hcorr_loop h_gate)⟩

/-! ## §2  The reading at every index the floor admits

The header derivation is `scanBlockScalar_prod`'s verbatim — only the tail
differs, and it differs in the one way that matters: instead of instantiating
`SCLLiteral.mk`'s `m` at the measured `contentIndent` with `n := 0`, it keeps
`d := contentIndent` in the conclusion and lets the caller choose any `n ≤ d`,
paying `m := d - n`.  `[170]`'s only occurrence of `n` is the `n + m` handed to
`[173] l-literal-content`, so no lift of any sub-production is involved — this
is Reflection 649's best case, an index whose every occurrence is absorbed by a
sibling existential. -/

/-- `scanBlockScalar_prod` with the measured indent kept: the block scalar reads
    as `[170]`/`[174]` at EVERY index up to the body's collection indent `d`, and
    `d` is at least the parent's `minContentIndent`.  The `∨` sits outside the
    `∀` because the leading character decides literal-vs-folded once. -/
lemma scanBlockScalar_prod_at (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hchar : sc.peek? = some '|' ∨ sc.peek? = some '>')
    (hok : scanBlockScalar sc = .ok s') :
    ∃ sp' d,
      (max 0 (sc.currentIndent + 1)).toNat ≤ d ∧
      ((∀ n, n ≤ d → SCLLiteral n sp sp') ∨ (∀ n, n ≤ d → SCLFolded n sp sp')) ∧
      ScannerSurfCorr s' sp' ∧
      (∀ sp_mid : SurfPos, SSLComments sp' sp_mid →
        (∀ n, n ≤ d → SCLLiteral n sp sp_mid) ∨ (∀ n, n ≤ d → SCLFolded n sp sp_mid)) := by
  unfold scanBlockScalar at hok
  dsimp only [] at hok
  have hoff : ∀ d, (parseBlockHeaderLoop sc.advance .clip none 2).2.1 = some d → d ≥ 1 :=
    parseBlockHeaderLoop_offset_preserves sc.advance .clip none 2 (fun _ h => nomatch h)
  obtain ⟨sp_adv_gen, hcorr_adv⟩ := advance_corr sc sp hcorr
  obtain ⟨sp_hdr, h_hdr_chars, hcorr_hdr⟩ :=
    parseBlockHeaderLoop_prod sc.advance sp_adv_gen hcorr_adv 2
  obtain ⟨sp_ws, h_ws, hcorr_ws⟩ :=
    skipWhitespace_corr (parseBlockHeaderLoop sc.advance .clip none 2).2.2 sp_hdr hcorr_hdr
  obtain ⟨sp_cmt, h_cmt, hcorr_cmt⟩ :=
    scanBlockScalarSkipComment_prod _ sp_ws hcorr_ws
  split at hok
  · simp at hok
  · rename_i s_after_nl hcn
    have h_ie : s_after_nl.inputEnd ≤ sc.inputEnd :=
      scanBlockScalar_afterNewline_inputEnd hcn
    obtain ⟨sp_nl, h_brk, hcorr_nl⟩ :=
      scanBlockScalarConsumeNewline_prod _ sp_cmt hcorr_cmt hcn
    have h_ssbcomment : SSBComment sp_hdr sp_nl := by
      cases h_ws with
      | nil =>
        match h_cmt with
        | .none _ => exact SSBComment.noSep sp_hdr sp_nl h_brk
        | .some _ _ hcnt =>
          exfalso
          rcases hchar with hlit | hfold
          · obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hlit; subst hsp_eq
            exact scanBlockScalar_unreachable_comment_without_ws
              sc sp_adv_gen sp_hdr sp_cmt '|' rest
              hcorr (peek_some_has_more hlit) (by decide) (by decide)
              ⟨by native_decide, by native_decide, by native_decide⟩
              hcorr_adv hcorr_hdr hcorr_ws hcorr_cmt hcnt
          · obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hfold; subst hsp_eq
            exact scanBlockScalar_unreachable_comment_without_ws
              sc sp_adv_gen sp_hdr sp_cmt '>' rest
              hcorr (peek_some_has_more hfold) (by decide) (by decide)
              ⟨by native_decide, by native_decide, by native_decide⟩
              hcorr_adv hcorr_hdr hcorr_ws hcorr_cmt hcnt
      | cons _ sp_mid _ h_first h_rest =>
        exact whitespace_comment_break_to_SSBComment_withWS
          sp_hdr sp_mid sp_ws sp_cmt sp_nl h_first h_rest h_cmt h_brk
    rcases hchar with hlit | hfold
    · obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hlit
      subst hsp_eq
      have hmore := peek_some_has_more hlit
      have hcorr_adv' := advance_non_newline_corr sc '|' rest hcorr hmore (by decide) (by decide)
      have hsp_adv_eq : sp_adv_gen = ⟨rest, sc.col + 1⟩ :=
        ScannerSurfCorr_unique hcorr_adv hcorr_adv'
      rw [hsp_adv_eq] at h_hdr_chars
      have h_header : SCBBlockHeader ⟨rest, sc.col + 1⟩ sp_nl :=
        SCBBlockHeader.mk ⟨rest, sc.col + 1⟩ sp_hdr sp_nl h_hdr_chars h_ssbcomment
      obtain ⟨sp_body, contentIndent, h_floor, h_literal_content, hcorr_body, h_absorb⟩ :=
        scanBlockScalarBody_contentIndent_floor sc s_after_nl sp_nl _ _ _ _ hcorr_nl hoff h_ie hok
      refine ⟨sp_body, contentIndent, h_floor, Or.inl (fun n hn => ?_), hcorr_body,
              fun sp_mid W => Or.inl fun n hn => ?_⟩
      · have h_at : SLLiteralContent (n + (contentIndent - n)) sp_nl sp_body := by
          have h_split : n + (contentIndent - n) = contentIndent := by omega
          rw [h_split]; exact h_literal_content
        exact SCLLiteral.mk n (contentIndent - n) rest sc.col sp_nl sp_body h_header h_at
      · have h_at : SLLiteralContent (n + (contentIndent - n)) sp_nl sp_mid := by
          have h_split : n + (contentIndent - n) = contentIndent := by omega
          rw [h_split]; exact h_absorb sp_mid W
        exact SCLLiteral.mk n (contentIndent - n) rest sc.col sp_nl sp_mid h_header h_at
    · obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hfold
      subst hsp_eq
      have hmore := peek_some_has_more hfold
      have hcorr_adv' := advance_non_newline_corr sc '>' rest hcorr hmore (by decide) (by decide)
      have hsp_adv_eq : sp_adv_gen = ⟨rest, sc.col + 1⟩ :=
        ScannerSurfCorr_unique hcorr_adv hcorr_adv'
      rw [hsp_adv_eq] at h_hdr_chars
      have h_header : SCBBlockHeader ⟨rest, sc.col + 1⟩ sp_nl :=
        SCBBlockHeader.mk ⟨rest, sc.col + 1⟩ sp_hdr sp_nl h_hdr_chars h_ssbcomment
      obtain ⟨sp_body, contentIndent, h_floor, h_literal_content, hcorr_body, h_absorb⟩ :=
        scanBlockScalarBody_contentIndent_floor sc s_after_nl sp_nl _ _ _ _ hcorr_nl hoff h_ie hok
      refine ⟨sp_body, contentIndent, h_floor, Or.inr (fun n hn => ?_), hcorr_body,
              fun sp_mid W => Or.inr fun n hn => ?_⟩
      · have h_at : SLLiteralContent (n + (contentIndent - n)) sp_nl sp_body := by
          have h_split : n + (contentIndent - n) = contentIndent := by omega
          rw [h_split]; exact h_literal_content
        exact SCLFolded.mk n (contentIndent - n) rest sc.col sp_nl sp_body h_header h_at
      · have h_at : SLLiteralContent (n + (contentIndent - n)) sp_nl sp_mid := by
          have h_split : n + (contentIndent - n) = contentIndent := by omega
          rw [h_split]; exact h_absorb sp_mid W
        exact SCLFolded.mk n (contentIndent - n) rest sc.col sp_nl sp_mid h_header h_at

end L4YAML.Proofs.BlockScalarIndentFloor

end Blanket
