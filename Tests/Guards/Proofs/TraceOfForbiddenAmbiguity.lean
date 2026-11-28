module

public import L4YAML.Proofs.Serialization.TraceOf.Document
public meta import L4YAML.Proofs.Serialization.TraceOf.Document

/-! # `traceOf_unique` against `[206] c-forbidden` (Rule 2): refutations

`[207] l-bare-document` is `s-l+block-node(-1,BLOCK-IN)` *excluding `c-forbidden` content*;
`SLBareDocument` carries no such exclusion, so a column-0 `...` / `---` line is both a
continuation line of a plain scalar and a document marker.  Neither pair below needs a bare
document after a bare document: the first uses `TLYamlStream.single` alone, the second opens
an EXPLICIT document through `implicitContinue`, which `[211]` explicit-only keeps. -/

namespace L4YAML.Tests.Guards.TraceOfForbiddenAmbiguity

open L4YAML L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf

private lemma nsc_a : isNsChar 'a' := by unfold isNsChar; decide
private lemma nsc_dot : isNsChar '.' := by unfold isNsChar; decide
private lemma nsc_dash : isNsChar '-' := by unfold isNsChar; decide
private lemma notInd_a : ¬ isIndicatorProp 'a' := by unfold isIndicatorProp; decide

private lemma eofComments (col : Nat) : SSLComments ⟨[], col⟩ ⟨[], col⟩ :=
  .withComment _ _ _ (.noSep _ _ (.eof col)) (.nil _)

/-- The plain scalar `a m m m` folded over the break: `[69]` grants the continuation line
indent 0 at `n = 0`, and `m` is an `ns-plain-safe` character. -/
private lemma plainOverMarker (m : Char) (hns : isNsChar m) (hc : m ≠ ':') (hh : m ≠ '#') :
    TBlockNode 0 .blockIn ⟨['a', '\n', m, m, m], 0⟩ ⟨[], 3⟩ [] :=
  .flowInBlock 0 .blockIn _ _ ⟨[], 3⟩ _ []
    (.inline 0 _ _ (.startOfLine _))
    (.content 0 .flowOut _ _ [] (.plain 0 .flowOut _ _
      (SNsPlainMultiLine.mk 0 .flowOut _ ⟨['\n', m, m, m], 1⟩ _
        (SNsPlainOneLine.mk .flowOut _ _ _
          (SNsPlainFirst.nonIndicator .flowOut 'a' _ 0 nsc_a notInd_a) (.nil _))
        (.cons _ ⟨[], 3⟩ _
          (SSNsPlainNextLine.mk 0 .flowOut _ _ ⟨[m, m, m], 0⟩ ⟨[m, m, m], 0⟩ ⟨[m, m, m], 0⟩
            ⟨[m, m], 1⟩ _
            (.nil _) (SBBreak.lf _ 1) (.nil _)
            (SFlowLinePrefix.mk 0 _ _ _ (.zero _) (.none _))
            (SNsPlainChar.safe .flowOut m _ 0 hns hc hh)
            (.cons _ ⟨[m], 2⟩ _
              (SNbNsPlainInLineEntry.mk .flowOut _ _ _ (.nil _)
                (SNsPlainChar.safe .flowOut m _ 1 hns hc hh))
              (.cons _ ⟨[], 3⟩ _
                (SNbNsPlainInLineEntry.mk .flowOut _ _ _ (.nil _)
                  (SNsPlainChar.safe .flowOut m _ 2 hns hc hh))
                (.nil _))))
          (.nil _)))))
    (eofComments 3)

/-- The bare document `a⏎`, ending at the start of the marker line. -/
private lemma docA (rest : List Char) :
    TBlockNode 0 .blockIn ⟨'a' :: '\n' :: rest, 0⟩ ⟨rest, 0⟩ [] :=
  .flowInBlock 0 .blockIn _ _ ⟨'\n' :: rest, 1⟩ _ []
    (.inline 0 _ _ (.startOfLine _))
    (.content 0 .flowOut _ _ [] (.plain 0 .flowOut _ _
      (SNsPlainMultiLine.mk 0 .flowOut _ ⟨'\n' :: rest, 1⟩ _
        (SNsPlainOneLine.mk .flowOut _ _ _
          (SNsPlainFirst.nonIndicator .flowOut 'a' _ 0 nsc_a notInd_a) (.nil _))
        (.nil _))))
    (.withComment _ ⟨rest, 0⟩ _ (.noSep _ _ (.break _ _ (SBBreak.lf _ 1))) (.nil _))

private lemma streamOf {s s' : SurfPos} {ev : List Event} (h : TBlockNode 0 .blockIn s s' ev) :
    TLYamlStream s s' ev := by
  have := TLYamlStream.single s s s' s' ev [] (.nil _)
    (.some _ _ _ (.bare _ _ _ (.mk _ _ _ h))) (.nil _)
  simpa using this

/-! ## Refutation 3 (OPEN — `[206]` on `[207]`): `a⏎...`, `single` alone -/

lemma traceOf_dotsPlain : TraceOf "a\n..." [] :=
  ⟨3, streamOf (plainOverMarker '.' nsc_dot (by decide) (by decide))⟩

/-- `a⏎`, then the `[205] l-document-suffix` `...` — the scanner's reading. -/
lemma traceOf_dotsMarker : TraceOf "a\n..." [Event.endDocument] := by
  have := TLYamlStream.single ⟨['a', '\n', '.', '.', '.'], 0⟩ _ ⟨['.', '.', '.'], 0⟩ ⟨[], 3⟩
    [] [Event.endDocument] (.nil _)
    (.some _ _ _ (.bare _ _ _ (TLBareDocument.mk _ _ _ (docA _))))
    (.cons _ ⟨[], 3⟩ _ _ [] (TLDocumentSuffix.mk _ _ _ (SCDocumentEnd.mk []) (eofComments 3)) (.nil _))
  exact ⟨3, by simpa using this⟩

/-- Stream uniqueness is false with no `implicitContinue` in either derivation. -/
lemma traceOf_unique_refuted_forbidden :
    ¬ (∀ (input : String) (ev₁ ev₂ : List Event),
        TraceOf input ev₁ → TraceOf input ev₂ → ev₁ = ev₂) :=
  fun h => by cases h _ _ _ traceOf_dotsPlain traceOf_dotsMarker

/-! ## Refutation 4 (OPEN — `[206]` on `[207]`): `a⏎---`, an explicit second document -/

lemma traceOf_dashesPlain : TraceOf "a\n---" [] :=
  ⟨3, streamOf (plainOverMarker '-' nsc_dash (by decide) (by decide))⟩

/-- `a⏎`, then the explicit empty document `---` — the scanner's reading, and the
continuation `[211]` explicit-only keeps. -/
lemma traceOf_dashesMarker : TraceOf "a\n---" [Event.beginDocument] := by
  have := TLYamlStream.implicitContinue ⟨['a', '\n', '-', '-', '-'], 0⟩ ⟨['-', '-', '-'], 0⟩ _
    ⟨[], 3⟩ ⟨[], 3⟩ [] [Event.beginDocument] []
    (streamOf (docA _))
    (.nil _)
    (.some _ _ _ (.explicit _ _ _ (TLExplicitDocument.withContent _ ⟨[], 3⟩ _ []
      (SCDirectivesEnd.mk [])
      (TAlt.right _ _ _ (TSeq.mk _ ⟨[], 3⟩ _ [] [] ⟨GEps.mk _, rfl⟩ ⟨eofComments 3, rfl⟩)))))
    (.nil _)
  exact ⟨3, by simpa using this⟩

end L4YAML.Tests.Guards.TraceOfForbiddenAmbiguity
