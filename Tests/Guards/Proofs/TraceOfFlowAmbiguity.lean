module

public import L4YAML.Proofs.Serialization.TraceOf.Node
public meta import L4YAML.Proofs.Serialization.TraceOf.Node

/-! # `tFlowNode_unique` is FALSE on the event-annotated flow grammar (Rule 2)

Two refutations of

    TFlowNode n c s s' ev₁ → TFlowNode n c s s' ev₂ → ev₁ = ev₂

each a pair of hand-built derivations of the same span with different traces.

1. `&xa` — anchor name non-maximal: `propsEmpty` reads the whole span as the
   anchor `xa`; the split reading (anchor `x`, an EMPTY `s-separate`, plain
   `a`) needed `SSeparateInLine.startOfLine` off column 0, which `[66]` no
   longer grants; `no_empty_sep_s1` records that the separation is refuted.
2. `[a # b, &x⏎]` — plain-vs-comment: `#` after a space is a comment under
   `s-separate`, but `SNsPlainChar.hashAfterNs` (guard `col > 0`, not
   "preceded by ns-char") also admits it inside the plain scalar, so the
   same text is one entry `a` + comment, or two entries `a # b` and `&x`.
   Traces `[]` vs `[defineAnchor "x"]`.
3. `[!t &x a]` — tag non-maximal: `!t` is a primary tag; the split reading
   (non-specific tag `!`, an EMPTY `s-separate`, plain `t &x a`) needed the
   same off-column-0 `startOfLine`; `no_empty_sep_u1` records its refutation.

Refutations 1 and 3 were pairs of derivations; with `[66]` narrowed to the spec
they are one derivation each plus the proof that the other does not exist. -/

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

/-! ## Refutation 1: `[&xa]` -/
section AnchorSplit

abbrev s0 : SurfPos := ⟨['&', 'x', 'a', ']'], 1⟩
abbrev s1 : SurfPos := ⟨['a', ']'], 3⟩
abbrev s2 : SurfPos := ⟨[']'], 4⟩

/-- `&xa` as one property, anchor `xa`. -/
lemma readAnchorXA : TFlowNode 0 .flowIn s0 s2 [Event.defineAnchor "xa"] :=
  .propsEmpty 0 .flowIn s0 s2 _
    (TCNsProperties.anchorFirst s0 s2 s2 [Event.defineAnchor "xa"] []
      (And.intro
        (SCNsAnchorProperty.mk _ 1 s2
          (GPlus.mk _ _ _ (GChar.mk 'x' _ 2 ns_x)
            (GStar.cons _ _ _ (GChar.mk 'a' _ 3 ns_a) (GStar.nil _))))
        (by decide))
      (TOpt.none _))

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

/-- Plain `a # b` (via `hashAfterNs`), `,`, space, anchor `&x`, break, `]`. -/
lemma readTwoEntries : TFlowSequence 0 .flowOut t0 t12 [Event.defineAnchor "x"] :=
  .nonempty 0 .flowOut t0 t1 t1 t11 t12 ([] ++ [Event.defineAnchor "x"])
    (GLit.mk _ 0) (GOpt.none _)
    (.consMore 0 .flowIn t1 t6 t6 t7 t8 t11 [] [Event.defineAnchor "x"]
      (.node 0 .flowIn t1 t6 [] (.content 0 .flowIn t1 t6 [] (.plain 0 .flowIn t1 t6
        (SNsPlainMultiLine.mk 0 .flowIn t1 t6 t6
          (SNsPlainOneLine.mk .flowIn t1 t2 t6
            (SNsPlainFirst.nonIndicator .flowIn 'a' _ 1 safe_a (by decide))
            (GStar.cons t2 t4 t6
              (SNbNsPlainInLineEntry.mk .flowIn t2 t3 t4
                (GStar.cons _ _ _ (SSWhite.space _ 2) (GStar.nil _))
                (SNsPlainChar.hashAfterNs .flowIn _ 3 (by decide)))
              (GStar.cons t4 t6 t6
                (SNbNsPlainInLineEntry.mk .flowIn t4 t5 t6
                  (GStar.cons _ _ _ (SSWhite.space _ 4) (GStar.nil _))
                  (SNsPlainChar.safe .flowIn 'b' _ 5 safe_b (by decide) (by decide)))
                (GStar.nil _))))
          (GStar.nil _)))))
      (GOpt.none _)
      (GLit.mk _ 6)
      (GOpt.some _ _ (SSeparateLines.inline 0 t7 t8
        (SSeparateInLine.whites t7 t8 (GPlus.mk _ _ _ (SSWhite.space _ 7) (GStar.nil _)))))
      (.single 0 .flowIn t8 t10 t11 [Event.defineAnchor "x"]
        (.node 0 .flowIn t8 t10 _ (.propsEmpty 0 .flowIn t8 t10 _
          (TCNsProperties.anchorFirst t8 t10 t10 [Event.defineAnchor "x"] []
            (And.intro
              (SCNsAnchorProperty.mk _ 8 t10
                (GPlus.mk _ _ _ (GChar.mk 'x' _ 9 ns_x) (GStar.nil _)))
              (by decide))
            (TOpt.none _))))
        (GOpt.some _ _ (SSeparateLines.commented 0 t10 t11 t11
          (SSLComments.withComment t10 t11 t11
            (SSBComment.noSep t10 t11 (SBComment.break t10 t11 (SBBreak.lf _ 10)))
            (GStar.nil _))
          (SFlowLinePrefix.mk 0 t11 t11 t11 (SIndent.zero _) (GOpt.none _))))))
    (GLit.mk _ 0)

#guard (([] : List Event) == [Event.defineAnchor "x"]) = false

lemma tFlowSequence_unique_false :
    ¬ ∀ ev₁ ev₂, TFlowSequence 0 .flowOut t0 t12 ev₁ → TFlowSequence 0 .flowOut t0 t12 ev₂ →
      ev₁ = ev₂ :=
  fun h => absurd (h _ _ readComment readTwoEntries) (by decide)

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

private lemma safe_t : isNsPlainSafe .flowIn 't' := by unfold isNsPlainSafe isNsChar; decide
private lemma safe_amp : isNsPlainSafe .flowIn '&' := by unfold isNsPlainSafe isNsChar; decide
private lemma safe_x : isNsPlainSafe .flowIn 'x' := by unfold isNsPlainSafe isNsChar; decide

/-- Tag `!t`, anchor `&x`, plain `a`. -/
lemma readTagAnchor : TFlowNode 0 .flowIn u0 u7 [Event.useTag "!", Event.defineAnchor "x"] :=
  .propsContent 0 .flowIn u0 u5 u6 u7 [Event.useTag "!", Event.defineAnchor "x"] []
    (TCNsProperties.tagFirst u0 u2 u5 [Event.useTag "!"] [Event.defineAnchor "x"]
      (And.intro
        (SCNsTagProperty.primary _ 1 u2
          (GStar.cons _ _ _ (GChar.mk 't' _ 2 (by decide)) (GStar.nil _)))
        (by decide))
      (TOpt.some _ _ _ (TSeq.mk u2 u3 u5 [] [Event.defineAnchor "x"]
        (And.intro
          (SSeparateLines.inline 0 u2 u3
            (SSeparateInLine.whites u2 u3 (GPlus.mk _ _ _ (SSWhite.space _ 3) (GStar.nil _))))
          rfl)
        (And.intro
          (SCNsAnchorProperty.mk _ 4 u5
            (GPlus.mk _ _ _ (GChar.mk 'x' _ 5 ns_x) (GStar.nil _)))
          (by decide)))))
    (SSeparateLines.inline 0 u5 u6
      (SSeparateInLine.whites u5 u6 (GPlus.mk _ _ _ (SSWhite.space _ 6) (GStar.nil _))))
    (.plain 0 .flowIn u6 u7
      (SNsPlainMultiLine.mk 0 .flowIn u6 u7 u7
        (SNsPlainOneLine.mk .flowIn u6 u7 u7
          (SNsPlainFirst.nonIndicator .flowIn 'a' _ 7 safe_a (by decide)) (GStar.nil _))
        (GStar.nil _)))

/-- Likewise `!` followed by an empty separation at `u1` (column 2) has no
derivation: the split reading of `!t` is gone. -/
lemma no_empty_sep_u1 : ¬ SSeparateInLine u1 u1 := sep_refl_col0_false (by decide)

end TagSplit

end L4YAML.Tests.Guards.TraceOfFlowAmbiguity
