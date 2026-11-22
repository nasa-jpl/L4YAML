module

public import L4YAML.Proofs.Serialization.TraceOf.Node
public meta import L4YAML.Proofs.Serialization.TraceOf.Node

/-! # `tFlowNode_unique` on the event-annotated flow grammar (Rule 2)

Refutations (all three closed) of

    TFlowNode n c s s' ev₁ → TFlowNode n c s s' ev₂ → ev₁ = ev₂

each a pair of hand-built derivations of the same span with different traces.

1. `&xa` — CLOSED: `[101]`/`[104]` now demand the maximal anchor name
   (`GNot (GChar isNsAnchorChar)` after the run), so the reading "anchor `x`,
   empty `s-separate`, plain `a`" is no longer a derivation
   (`anchorX_not_property`); only `[defineAnchor "xa"]` remains.
2. `[a # b, &x⏎]` — plain-vs-comment, CLOSED: `#` after a space is a comment
   under `s-separate`.  `SNsPlainChar.hashAfterNs` (guard `col > 0`, not
   "preceded by ns-char") used to admit it inside the plain scalar too; now
   `[130]` has no `#` and `[132]`'s `hash` entry needs an empty `s-white*`,
   so ` #` is no entry (`hash_after_white_not_entry`) and only the comment
   reading `readComment` (trace `[]`) remains.
3. `[!t &x a]` — tag non-maximal, CLOSED: `!t` is a primary tag, or it was the
   non-specific tag `!` followed by an EMPTY `s-separate` and the plain scalar
   `t &x a` (traces `[useTag "!", defineAnchor "x"]` vs `[useTag "!"]`).  Every
   `[97]` arm now ends with `GNot (GChar isTagCharProp)`, so `[100]` cannot stop
   in front of `t` (`nonSpecific_not_before_t`); only the first reading remains.
4. `[!<a>]` — verbatim-vs-non-specific, CLOSED: the verbatim tag `!<a>` (trace
   `[]`, §6 Q4), or the non-specific tag `!` (`<` is no `[40] ns-tag-char`, so
   `[100]`'s lookahead holds), an EMPTY `s-separate` at col 2, and the plain
   scalar `<a>` (trace `[useTag "!"]`).  `[96]` is followed by a mandatory
   `s-separate`, which `[66]` now grants zero-width only at column 0
   (`no_empty_sep_v1`); only `readVerbatim` remains.

Refutations 1, 3 and 4 each record the surviving derivation plus the proof that
the other does not exist; 1 and 3 are refuted twice (maximal name/tag, and the
`[66]` narrowing). -/

namespace L4YAML.Tests.Guards.TraceOfFlowAmbiguity

open L4YAML L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf

private lemma sswhite_col (a b : SurfPos) (h : SSWhite a b) : b.col = a.col + 1 := by
  cases h <;> rfl

private lemma gstar_sswhite_col_le (a b : SurfPos) (h : GStar SSWhite a b) : a.col ≤ b.col := by
  induction h with
  | nil _ => exact Nat.le_refl _
  | cons _ _ _ hx _ ih => rw [sswhite_col _ _ hx] at ih; omega

/-- A zero-width `[66]` forces column 0: `whites` is nonempty and raises the
    column, `startOfLine` is the column-0 match. -/
private lemma sep_refl_col0_false {s : SurfPos} (hne : s.col ≠ 0) : ¬ SSeparateInLine s s := by
  intro h
  cases h
  · rename_i hp
    match hp with
    | .mk _ _ _ hw hrest =>
      have h1 := sswhite_col _ _ hw
      have h2 := gstar_sswhite_col_le _ _ hrest
      omega
  · exact hne rfl

private lemma ns_x : isNsAnchorChar 'x' := by unfold isNsAnchorChar isNsChar; decide
private lemma ns_a : isNsAnchorChar 'a' := by unfold isNsAnchorChar isNsChar; decide
private lemma safe_a : isNsPlainSafe .flowIn 'a' := by unfold isNsPlainSafe isNsChar; decide
private lemma safe_b : isNsPlainSafe .flowIn 'b' := by unfold isNsPlainSafe isNsChar; decide

/-! ## Refutation 1 (CLOSED by maximal anchor names): `[&xa]` -/
section AnchorSplit

abbrev s0 : SurfPos := ⟨['&', 'x', 'a', ']'], 1⟩
abbrev s1 : SurfPos := ⟨['a', ']'], 3⟩
abbrev s2 : SurfPos := ⟨[']'], 4⟩

/-- The `[101]`/`[104]` lookahead at a position whose head char is not an anchor char. -/
private lemma gnot_anchor_of_head {c : Char} {rest : List Char} {col : Nat}
    (h : ¬ isNsAnchorChar c) : GNot (GChar isNsAnchorChar) ⟨c :: rest, col⟩ :=
  fun _ hg => by cases hg with | mk _ _ _ hp => exact h hp

/-- `&xa` as one property, anchor `xa`; `]` is not an anchor char. -/
lemma readAnchorXA : TFlowNode 0 .flowIn s0 s2 [Event.defineAnchor "xa"] :=
  .propsEmpty 0 .flowIn s0 s2 _
    (TCNsProperties.anchorFirst s0 s2 s2 [Event.defineAnchor "xa"] []
      (And.intro
        (SCNsAnchorProperty.mk _ 1 s2
          (GPlus.mk _ _ _ (GChar.mk 'x' _ 2 ns_x)
            (GStar.cons _ _ _ (GChar.mk 'a' _ 3 ns_a) (GStar.nil _)))
          (gnot_anchor_of_head (by unfold isNsAnchorChar isNsChar; decide)))
        (by decide))
      (TOpt.none _))

/-- The former second reading — anchor `x` stopping in front of `a` — is no
longer a `[101]` derivation: the name must be maximal. -/
lemma anchorX_not_property : ¬ SCNsAnchorProperty s0 s1 :=
  fun h => by cases h with | mk _ _ _ _ hnot => exact hnot _ (GChar.mk 'a' _ 3 ns_a)

/-- A zero-width `[66]` exists only at column 0, so `&x` at column 1 cannot be
followed by an empty separation at `s1` (column 3): the split reading of `&xa`
has no derivation. -/
lemma no_empty_sep_s1 : ¬ SSeparateInLine s1 s1 := sep_refl_col0_false (by decide)

end AnchorSplit

/-! ## Refutation 2: `[a # b, &x⏎]` -/
section PlainComment

abbrev t0 : SurfPos := ⟨['[', 'a', ' ', '#', ' ', 'b', ',', ' ', '&', 'x', '\n', ']'], 0⟩
abbrev t1 : SurfPos := ⟨['a', ' ', '#', ' ', 'b', ',', ' ', '&', 'x', '\n', ']'], 1⟩
abbrev t2 : SurfPos := ⟨[' ', '#', ' ', 'b', ',', ' ', '&', 'x', '\n', ']'], 2⟩
abbrev t3 : SurfPos := ⟨['#', ' ', 'b', ',', ' ', '&', 'x', '\n', ']'], 3⟩
abbrev t4 : SurfPos := ⟨[' ', 'b', ',', ' ', '&', 'x', '\n', ']'], 4⟩
abbrev t5 : SurfPos := ⟨['b', ',', ' ', '&', 'x', '\n', ']'], 5⟩
abbrev t6 : SurfPos := ⟨[',', ' ', '&', 'x', '\n', ']'], 6⟩
abbrev t7 : SurfPos := ⟨[' ', '&', 'x', '\n', ']'], 7⟩
abbrev t8 : SurfPos := ⟨['&', 'x', '\n', ']'], 8⟩
abbrev t9 : SurfPos := ⟨['x', '\n', ']'], 9⟩
abbrev t10 : SurfPos := ⟨['\n', ']'], 10⟩
abbrev t11 : SurfPos := ⟨[']'], 0⟩
abbrev t12 : SurfPos := ⟨[], 1⟩

private lemma cc (ch : Char) (h : ¬isLineBreakProp ch) : isCommentTextChar ch := h

/-- Plain `a`, then `s-separate` = ` # b, &x⏎` as a comment, then `]`. -/
lemma readComment : TFlowSequence 0 .flowOut t0 t12 [] :=
  .nonempty 0 .flowOut t0 t1 t1 t11 t12 []
    (GLit.mk _ 0) (GOpt.none _)
    (.single 0 .flowIn t1 t2 t11 []
      (.node 0 .flowIn t1 t2 [] (.content 0 .flowIn t1 t2 [] (.plain 0 .flowIn t1 t2
        (SNsPlainMultiLine.mk 0 .flowIn t1 t2 t2
          (SNsPlainOneLine.mk .flowIn t1 t2 t2
            (SNsPlainFirst.nonIndicator .flowIn 'a' _ 1 safe_a (by decide)) (GStar.nil _))
          (GStar.nil _)))))
      (GOpt.some _ _ (SSeparateLines.commented 0 t2 t11 t11
        (SSLComments.withComment t2 t11 t11
          (SSBComment.withSep t2 t3 t10 t11
            (SSeparateInLine.whites t2 t3 (GPlus.mk _ _ _ (SSWhite.space _ 2) (GStar.nil _)))
            (GOpt.some _ _ (SCNbCommentText.mk _ 3 t10
              (GStar.cons _ _ _ (GChar.mk ' ' _ 4 (cc _ (by decide)))
              (GStar.cons _ _ _ (GChar.mk 'b' _ 5 (cc _ (by decide)))
              (GStar.cons _ _ _ (GChar.mk ',' _ 6 (cc _ (by decide)))
              (GStar.cons _ _ _ (GChar.mk ' ' _ 7 (cc _ (by decide)))
              (GStar.cons _ _ _ (GChar.mk '&' _ 8 (cc _ (by decide)))
              (GStar.cons _ _ _ (GChar.mk 'x' _ 9 (cc _ (by decide)))
              (GStar.nil _)))))))))
            (SBComment.break t10 t11 (SBBreak.lf _ 10)))
          (GStar.nil _))
        (SFlowLinePrefix.mk 0 t11 t11 t11 (SIndent.zero _) (GOpt.none _)))))
    (GLit.mk _ 0)

/-- The second derivation is gone: ` #` (white, then `#`) is NOT a `[132]` entry.  `mk`'s
    `ns-plain-char` has no `#`, and `hash` wants the `#` at the entry's own start — here
    the entry starts with a space.  `[a # b, &x⏎]` keeps only `readComment`. -/
lemma hash_after_white_not_entry : ¬ SNbNsPlainInLineEntry .flowIn t2 t4 := by
  intro h
  cases h
  · rename_i hws hch
    cases hws
    · cases hch
    · rename_i hw hws'
      cases hw
      cases hws'
      · cases hch
        rename_i hNotHash
        exact hNotHash rfl
      · rename_i hw' _
        cases hw'
  · rename_i hl
    cases hl

end PlainComment

/-! ## Refutation 3: `[!t &x a]` (a listed input) -/
section TagSplit

abbrev u0 : SurfPos := ⟨['!', 't', ' ', '&', 'x', ' ', 'a', ']'], 1⟩
abbrev u1 : SurfPos := ⟨['t', ' ', '&', 'x', ' ', 'a', ']'], 2⟩
abbrev u2 : SurfPos := ⟨[' ', '&', 'x', ' ', 'a', ']'], 3⟩
abbrev u3 : SurfPos := ⟨['&', 'x', ' ', 'a', ']'], 4⟩
abbrev u4 : SurfPos := ⟨['x', ' ', 'a', ']'], 5⟩
abbrev u5 : SurfPos := ⟨[' ', 'a', ']'], 6⟩
abbrev u6 : SurfPos := ⟨['a', ']'], 7⟩
abbrev u7 : SurfPos := ⟨[']'], 8⟩

private lemma gnot_tag_u2 : GNot (GChar isTagCharProp) u2 :=
  fun _ h => by cases h with | mk _ _ _ hp => exact absurd hp (by decide)

/-- Tag `!t`, anchor `&x`, plain `a`. -/
lemma readTagAnchor : TFlowNode 0 .flowIn u0 u7 [Event.useTag "!", Event.defineAnchor "x"] :=
  .propsContent 0 .flowIn u0 u5 u6 u7 [Event.useTag "!", Event.defineAnchor "x"] []
    (TCNsProperties.tagFirst u0 u2 u5 [Event.useTag "!"] [Event.defineAnchor "x"]
      (And.intro
        (SCNsTagProperty.primary _ 1 u2
          (GPlus.mk _ _ _ (GChar.mk 't' _ 2 (by decide)) (GStar.nil _))
          gnot_tag_u2)
        (by decide))
      (TOpt.some _ _ _ (TSeq.mk u2 u3 u5 [] [Event.defineAnchor "x"]
        (And.intro
          (SSeparateLines.inline 0 u2 u3
            (SSeparateInLine.whites u2 u3 (GPlus.mk _ _ _ (SSWhite.space _ 3) (GStar.nil _))))
          rfl)
        (And.intro
          (SCNsAnchorProperty.mk _ 4 u5
            (GPlus.mk _ _ _ (GChar.mk 'x' _ 5 ns_x) (GStar.nil _))
            (gnot_anchor_of_head (by unfold isNsAnchorChar isNsChar; decide)))
          (by decide)))))
    (SSeparateLines.inline 0 u5 u6
      (SSeparateInLine.whites u5 u6 (GPlus.mk _ _ _ (SSWhite.space _ 6) (GStar.nil _))))
    (.plain 0 .flowIn u6 u7
      (SNsPlainMultiLine.mk 0 .flowIn u6 u7 u7
        (SNsPlainOneLine.mk .flowIn u6 u7 u7
          (SNsPlainFirst.nonIndicator .flowIn 'a' _ 7 safe_a (by decide)) (GStar.nil _))
        (GStar.nil _)))

/-- The former second reading — `[100]` stopping in front of `t` — is no
longer a derivation: the tag must be maximal (`t` is a `[40] ns-tag-char`). -/
lemma nonSpecific_not_before_t : ¬ GNot (GChar isTagCharProp) u1 :=
  fun h => h _ (GChar.mk 't' _ 2 (by decide))

/-- Likewise `!` followed by an empty separation at `u1` (column 2) has no
derivation: the split reading of `!t` is gone. -/
lemma no_empty_sep_u1 : ¬ SSeparateInLine u1 u1 := sep_refl_col0_false (by decide)

end TagSplit

/-! ## Refutation 4 (CLOSED by `[66]` at col 0): `[!<a>]` -/
section VerbatimSplit

abbrev v0 : SurfPos := ⟨['!', '<', 'a', '>', ']'], 1⟩
abbrev v1 : SurfPos := ⟨['<', 'a', '>', ']'], 2⟩
abbrev v2 : SurfPos := ⟨['a', '>', ']'], 3⟩
abbrev v3 : SurfPos := ⟨['>', ']'], 4⟩
abbrev v4 : SurfPos := ⟨[']'], 5⟩

private lemma safe_lt : isNsPlainSafe .flowIn '<' := by unfold isNsPlainSafe isNsChar; decide
private lemma safe_gt : isNsPlainSafe .flowIn '>' := by unfold isNsPlainSafe isNsChar; decide

/-- `<` is not a `[40] ns-tag-char`, so `[100] c-non-specific-tag` may stop after `!`. -/
lemma gnot_tag_v1 : GNot (GChar isTagCharProp) v1 :=
  fun _ h => by cases h with | mk _ _ _ hp => exact absurd hp (by decide)

/-- Reading 1: the verbatim tag `!<a>`, which names no handle (trace `[]`). -/
lemma readVerbatim : TFlowNode 0 .flowIn v0 v4 [] :=
  .propsEmpty 0 .flowIn v0 v4 []
    (TCNsProperties.tagFirst v0 v4 v4 [] []
      (And.intro
        (SCNsTagProperty.verbatim _ 1 v2 v3 v4
          (GLit.mk _ 2)
          (GPlus.mk _ _ _ (GChar.mk 'a' _ 3 (by decide)) (GStar.nil _))
          (GLit.mk _ 4))
        (by decide))
      (TOpt.none _))

/-- The former reading 2 — `!`, then the plain scalar `<a>` with an EMPTY
`s-separate` at `v1` (column 2) — has no derivation: `[66]` is zero-width only at
column 0 (`gnot_tag_v1` shows `[100]` itself could stop there). -/
lemma no_empty_sep_v1 : ¬ SSeparateInLine v1 v1 := sep_refl_col0_false (by decide)

end VerbatimSplit

end L4YAML.Tests.Guards.TraceOfFlowAmbiguity
