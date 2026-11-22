module

public import L4YAML.Proofs.Serialization.TraceOf.Document
public meta import L4YAML.Proofs.Serialization.TraceOf.Document

/-! # `traceOf_unique` on the block/document fragment (Rule 2): refutations -/

namespace L4YAML.Tests.Guards.TraceOfBlockAmbiguity

open L4YAML L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf

private lemma ns_x : isNsAnchorChar 'x' := by unfold isNsAnchorChar isNsChar; decide
private lemma nsc_a : isNsChar 'a' := by unfold isNsChar; decide
private lemma nsc_amp : isNsChar '&' := by unfold isNsChar; decide
private lemma nsc_x : isNsChar 'x' := by unfold isNsChar; decide
private lemma notInd_a : ¬ isIndicatorProp 'a' := by unfold isIndicatorProp; decide

private lemma eofComments (col : Nat) : SSLComments ⟨[], col⟩ ⟨[], col⟩ :=
  .withComment _ _ _ (.noSep _ _ (.eof col)) (.nil _)

/-! ## Refutation 1 (OPEN — row 19 `implicitContinue`): `a⏎&x` -/
section ImplicitContinue

abbrev u0 : SurfPos := ⟨['a', '\n', '&', 'x'], 0⟩
abbrev u1 : SurfPos := ⟨['\n', '&', 'x'], 1⟩
abbrev u2 : SurfPos := ⟨['&', 'x'], 0⟩
abbrev u3 : SurfPos := ⟨['x'], 1⟩
abbrev u4 : SurfPos := ⟨[], 2⟩

/-- Reading A (the parser's): one bare document, plain scalar `a &x` folded over the break. -/
lemma readPlain : TLYamlStream u0 u4 [] :=
  .single u0 u0 u4 u4 [] [] (.nil _)
    (.some _ _ _ (.bare _ _ _ (.mk _ _ _
      (.flowInBlock 0 .blockIn u0 u0 u4 u4 []
        (.inline 0 _ _ (.startOfLine _))
        (.content 0 .flowOut u0 u4 [] (.plain 0 .flowOut u0 u4
          (SNsPlainMultiLine.mk 0 .flowOut u0 u1 u4
            (SNsPlainOneLine.mk .flowOut u0 u1 u1
              (SNsPlainFirst.nonIndicator .flowOut 'a' _ 0 nsc_a notInd_a) (.nil _))
            (.cons u1 u4 u4
              (SSNsPlainNextLine.mk 0 .flowOut u1 u1 u2 u2 u2 u3 u4
                (.nil _) (SBBreak.lf _ 1) (.nil _)
                (SFlowLinePrefix.mk 0 u2 u2 u2 (.zero _) (.none _))
                (SNsPlainChar.safe .flowOut '&' _ 0 nsc_amp (by decide) (by decide))
                (.cons u3 u4 u4
                  (SNbNsPlainInLineEntry.mk .flowOut u3 u3 u4 (.nil _)
                    (SNsPlainChar.safe .flowOut 'x' _ 1 nsc_x (by decide) (by decide)))
                  (.nil _)))
              (.nil _)))))
        (eofComments 2)))))
    (.nil _)

/-- Reading B: bare document `a`, then `implicitContinue` with a second BARE document `&x`. -/
lemma readAnchor : TLYamlStream u0 u4 [Event.defineAnchor "x"] :=
  .implicitContinue u0 u2 u2 u4 u4 [] [Event.defineAnchor "x"] []
    (.single u0 u0 u2 u2 [] [] (.nil _)
      (.some _ _ _ (.bare _ _ _ (.mk _ _ _
        (.flowInBlock 0 .blockIn u0 u0 u1 u2 []
          (.inline 0 _ _ (.startOfLine _))
          (.content 0 .flowOut u0 u1 [] (.plain 0 .flowOut u0 u1
            (SNsPlainMultiLine.mk 0 .flowOut u0 u1 u1
              (SNsPlainOneLine.mk .flowOut u0 u1 u1
                (SNsPlainFirst.nonIndicator .flowOut 'a' _ 0 nsc_a notInd_a) (.nil _))
              (.nil _))))
          (.withComment u1 u2 u2 (.noSep _ _ (.break _ _ (SBBreak.lf _ 1))) (.nil _))))))
      (.nil _))
    (.nil _)
    (.some _ _ _ (.bare _ _ _ (.mk _ _ _
      (.flowInBlock 0 .blockIn u2 u2 u4 u4 [Event.defineAnchor "x"]
        (.inline 0 _ _ (.startOfLine _))
        (.propsEmpty 0 .flowOut u2 u4 _
          (TCNsProperties.anchorFirst u2 u4 u4 [Event.defineAnchor "x"] []
            (And.intro
              (SCNsAnchorProperty.mk _ 0 u4
                (GPlus.mk _ _ _ (GChar.mk 'x' _ 1 ns_x) (.nil _))
                (fun _ hg => by cases hg))
              (by decide))
            (.none _)))
        (eofComments 2)))))
    (.nil _)

lemma traceOf_plain : TraceOf "a\n&x" [] := ⟨2, readPlain⟩
lemma traceOf_anchor : TraceOf "a\n&x" [Event.defineAnchor "x"] := ⟨2, readAnchor⟩

/-- `traceOf_unique` is FALSE as stated while `implicitContinue` admits a bare document. -/
lemma traceOf_unique_refuted :
    ¬ (∀ (input : String) (ev₁ ev₂ : List Event),
        TraceOf input ev₁ → TraceOf input ev₂ → ev₁ = ev₂) :=
  fun h => by cases h _ _ _ traceOf_plain traceOf_anchor

end ImplicitContinue

/-! ## Refutation 2 (OPEN at the stream layer — row 19 `implicitContinue` + autodetected `m`;
    the `[173]` tail half is CLOSED, see `literalB`): `a: |⏎   x⏎  &x b: *x` -/
section LiteralTail

private instance : DecidablePred isNbChar := fun c => by unfold isNbChar; infer_instance

private lemma nbRun (cs rest : List Char) (col : Nat) (h : ∀ c ∈ cs, isNbChar c) :
    GStar SNbChar ⟨cs ++ rest, col⟩ ⟨rest, col + cs.length⟩ := by
  induction cs generalizing col with
  | nil => exact GStar.nil _
  | cons c cs ih =>
    refine GStar.cons _ ⟨cs ++ rest, col + 1⟩ _ (GChar.mk c _ col (h c (by simp))) ?_
    have := ih (col + 1) (fun d hd => h d (List.mem_cons_of_mem _ hd))
    have e : col + 1 + cs.length = col + (c :: cs).length := by simp; omega
    rw [e] at this
    exact this

private lemma nbPlus (c : Char) (cs rest : List Char) (col : Nat) (hc : isNbChar c)
    (h : ∀ d ∈ cs, isNbChar d) :
    GPlus SNbChar ⟨c :: cs ++ rest, col⟩ ⟨rest, col + 1 + cs.length⟩ :=
  GPlus.mk _ _ _ (GChar.mk c _ col hc) (nbRun cs rest (col + 1) h)

private lemma gnot_anchor_of_head {c : Char} {rest : List Char} {col : Nat}
    (h : ¬ isNsAnchorChar c) : GNot (GChar isNsAnchorChar) ⟨c :: rest, col⟩ :=
  fun _ hg => by cases hg with | mk _ _ _ hp => exact h hp

private lemma nsc_b : isNsChar 'b' := by unfold isNsChar; decide
private lemma notInd_b : ¬ isIndicatorProp 'b' := by unfold isIndicatorProp; decide
private lemma notAnchor_space : ¬ isNsAnchorChar ' ' := by unfold isNsAnchorChar isNsChar; decide

abbrev tail3 : List Char := ['\n', ' ', ' ', '&', 'x', ' ', 'b', ':', ' ', '*', 'x']
abbrev v0 : SurfPos := ⟨'a' :: ':' :: ' ' :: '|' :: '\n' :: ' ' :: ' ' :: ' ' :: 'x' :: tail3, 0⟩
abbrev v1 : SurfPos := ⟨':' :: ' ' :: '|' :: '\n' :: ' ' :: ' ' :: ' ' :: 'x' :: tail3, 1⟩
abbrev v2 : SurfPos := ⟨' ' :: '|' :: '\n' :: ' ' :: ' ' :: ' ' :: 'x' :: tail3, 2⟩
abbrev v3 : SurfPos := ⟨'|' :: '\n' :: ' ' :: ' ' :: ' ' :: 'x' :: tail3, 3⟩
abbrev v4 : SurfPos := ⟨'\n' :: ' ' :: ' ' :: ' ' :: 'x' :: tail3, 4⟩
abbrev v5 : SurfPos := ⟨' ' :: ' ' :: ' ' :: 'x' :: tail3, 0⟩
abbrev v6 : SurfPos := ⟨' ' :: ' ' :: 'x' :: tail3, 1⟩
abbrev v8 : SurfPos := ⟨'x' :: tail3, 3⟩
abbrev v9 : SurfPos := ⟨tail3, 4⟩
abbrev v10 : SurfPos := ⟨[' ', ' ', '&', 'x', ' ', 'b', ':', ' ', '*', 'x'], 0⟩
abbrev v11 : SurfPos := ⟨[' ', '&', 'x', ' ', 'b', ':', ' ', '*', 'x'], 1⟩
abbrev v12 : SurfPos := ⟨['&', 'x', ' ', 'b', ':', ' ', '*', 'x'], 2⟩
abbrev v14 : SurfPos := ⟨[' ', 'b', ':', ' ', '*', 'x'], 4⟩
abbrev v15 : SurfPos := ⟨['b', ':', ' ', '*', 'x'], 5⟩
abbrev v16 : SurfPos := ⟨[':', ' ', '*', 'x'], 6⟩
abbrev v17 : SurfPos := ⟨[' ', '*', 'x'], 7⟩
abbrev v18 : SurfPos := ⟨['*', 'x'], 8⟩
abbrev vEnd : SurfPos := ⟨[], 10⟩

/-- The shared prefix `a: ` of both readings: key `a`, then `:`. -/
private lemma keyA : TImplicitKey v0 v1 [] :=
  .yamlKey v0 v1 v1
    (SNsPlainOneLine.mk .blockKey v0 v1 v1
      (SNsPlainFirst.nonIndicator .blockKey 'a' _ 0 nsc_a notInd_a) (.nil _))
    (.none _)

/-- `|` + empty header + the comment-less line end; the body starts at `v5`. -/
private lemma header : SCBBlockHeader v4 v5 :=
  .mk v4 v4 v5
    (.left _ _ (.mk _ _ _ (.empty _) (.empty _)))
    (.noSep _ _ (.break _ _ (SBBreak.lf _ 4)))

/-- Reading A: autodetected indent `m = 0`, content indent 1 — BOTH following lines are
literal text (the extra spaces are `nb-char`s).  One entry, trace `[]`. -/
lemma literalA : SCLLiteral 1 v3 vEnd :=
  .mk 1 0 _ 3 v5 vEnd header
    (SLLiteralContent.mk 1 v5 vEnd vEnd vEnd vEnd vEnd
      (.some _ _ (.mk v5 v9 vEnd
        (SLNbLiteralText.mk 1 v5 v5 v9 (.nil _)
          (.mk v5 v6 v9 (.succ 0 _ 0 v6 (.zero _))
            (nbPlus ' ' [' ', 'x'] tail3 1 (by decide) (by decide))))
        (.cons v9 vEnd vEnd
          (SBNbLiteralNext.mk 1 v9 v10 vEnd (SBBreak.lf _ 4)
            (SLNbLiteralText.mk 1 v10 v10 vEnd (.nil _)
              (.mk v10 v11 vEnd (.succ 0 _ 0 v11 (.zero _))
                (nbPlus ' ' ['&', 'x', ' ', 'b', ':', ' ', '*', 'x'] [] 1 (by decide) (by decide)))))
          (.nil _))))
      (.none _) (.nil _) (.none _) (.none _))

lemma readOneEntry : TBlockNode 0 .blockIn v0 vEnd [] :=
  .blockMap 0 .blockIn 0 v0 v0 v0 vEnd [] [] (.none _) (.startOfLine _ _ (.nil _))
    (.single 0 v0 v0 vEnd [] (.zero _)
      (.implicitKeyNode 0 v0 v1 v2 vEnd [] [] keyA (GLit.mk _ 1)
        (.blockLiteral 1 .blockOut v2 v3 v3 vEnd []
          (.inline 1 _ _ (.whites _ _ (.mk _ _ _ (.space _ 2) (.nil _))))
          (.none _) literalA)))

/-- Reading B: autodetected indent `m = 2`, content indent 3 — the second line is text, the
third is not indented enough, so the content ENDS after the break (at `v10`).

`[173]`'s partial-indent tail is now confined to end of input, so the two spaces of line 3
are NOT the scalar's: the enclosing mapping at indent 0 cannot resume at indent 2 either, and
the `TBlockNode`-level half of this refutation (two entries in ONE mapping, formerly its own
refutation lemma) is CLOSED.  What survives is the stream layer: `TLYamlStream.implicitContinue`
(row 19, `[211]`) admits `  &x b: *x` as a second BARE document — a block mapping at indent 2
— without a `...` suffix.  The traces still differ, so `traceOf_unique` stays refuted. -/
lemma literalB : SCLLiteral 1 v3 v10 :=
  .mk 1 2 _ 3 v5 v10 header
    (SLLiteralContent.mk 3 v5 v9 v10 v10 v10 v10
      (.some _ _ (.mk v5 v9 v9
        (SLNbLiteralText.mk 3 v5 v5 v9 (.nil _)
          (.mk v5 v8 v9 (.succ 2 _ 0 v8 (.succ 1 _ 1 v8 (.succ 0 _ 2 v8 (.zero _))))
            (nbPlus 'x' [] tail3 3 (by decide) (by decide))))
        (.nil _)))
      (.some _ _ (SBBreak.lf _ 4)) (.nil _) (.none _) (.none _))

/-- First document of reading B: the single entry `a: |⏎   x⏎` with the `m = 2` literal. -/
lemma readOneEntryB : TBlockNode 0 .blockIn v0 v10 [] :=
  .blockMap 0 .blockIn 0 v0 v0 v0 v10 [] [] (.none _) (.startOfLine _ _ (.nil _))
    (.single 0 v0 v0 v10 [] (.zero _)
      (.implicitKeyNode 0 v0 v1 v2 v10 [] [] keyA (GLit.mk _ 1)
        (.blockLiteral 1 .blockOut v2 v3 v3 v10 []
          (.inline 1 _ _ (.whites _ _ (.mk _ _ _ (.space _ 2) (.nil _))))
          (.none _) literalB)))

private lemma keyAnchoredB : TImplicitKey v12 v16 [Event.defineAnchor "x"] :=
  .jsonKey v12 v16 v16 _
    (.propsContent 0 .blockKey v12 v14 v15 v16 [Event.defineAnchor "x"] []
      (TCNsProperties.anchorFirst v12 v14 v14 [Event.defineAnchor "x"] []
        (And.intro
          (SCNsAnchorProperty.mk _ 2 v14
            (GPlus.mk _ _ _ (GChar.mk 'x' _ 3 ns_x) (.nil _))
            (gnot_anchor_of_head notAnchor_space))
          (by decide))
        (.none _))
      (.whites _ _ (.mk _ _ _ (.space _ 4) (.nil _)))
      (.plain 0 .blockKey v15 v16
        (SNsPlainOneLine.mk .blockKey v15 v16 v16
          (SNsPlainFirst.nonIndicator .blockKey 'b' _ 5 nsc_b notInd_b) (.nil _))))
    (.none _)

private lemma aliasValue (n : Nat) : TBlockNode n .blockOut v17 vEnd [Event.useAlias "x"] :=
  .flowInBlock n .blockOut v17 v18 vEnd vEnd _
    (.inline n _ _ (.whites _ _ (.mk _ _ _ (.space _ 7) (.nil _))))
    (.alias n .flowOut v18 vEnd _
      (And.intro
        (SCNsAliasNode.mk _ 8 vEnd
          (GPlus.mk _ _ _ (GChar.mk 'x' _ 9 ns_x) (.nil _))
          (fun _ hg => by cases hg))
        (by decide)))
    (eofComments 10)

/-- Second document of reading B: the bare document `  &x b: *x`, a block mapping at indent 2. -/
lemma secondDoc : TBlockNode 0 .blockIn v10 vEnd [Event.defineAnchor "x", Event.useAlias "x"] :=
  .blockMap 0 .blockIn 2 v10 v10 v10 vEnd [] _ (.none _) (.startOfLine _ _ (.nil _))
    (.single 2 v10 v12 vEnd _ (.succ 1 _ 0 v12 (.succ 0 _ 1 v12 (.zero _)))
      (.implicitKeyNode 2 v12 v16 v17 vEnd [Event.defineAnchor "x"] [Event.useAlias "x"]
        keyAnchoredB (GLit.mk _ 6) (aliasValue 3)))

/-- Reading B at the stream layer: two bare documents joined by `implicitContinue`. -/
lemma readTwoDocs : TLYamlStream v0 vEnd [Event.defineAnchor "x", Event.useAlias "x"] := by
  have := TLYamlStream.implicitContinue v0 v10 v10 vEnd vEnd
    [] [Event.defineAnchor "x", Event.useAlias "x"] []
    (.single v0 v0 v10 v10 [] [] (.nil _)
      (.some _ _ _ (.bare _ _ _ (.mk _ _ _ readOneEntryB))) (.nil _))
    (.nil _)
    (.some _ _ _ (.bare _ _ _ (.mk _ _ _ secondDoc)))
    (.nil _)
  simpa using this

private lemma streamOf {s' : SurfPos} {ev : List Event} (h : TBlockNode 0 .blockIn v0 s' ev) :
    TLYamlStream v0 s' ev := by
  have := TLYamlStream.single v0 v0 s' s' ev [] (.nil _)
    (.some _ _ _ (.bare _ _ _ (.mk _ _ _ h))) (.nil _)
  simpa using this

lemma traceOf_literalA : TraceOf "a: |\n   x\n  &x b: *x" [] := ⟨10, streamOf readOneEntry⟩
lemma traceOf_literalB :
    TraceOf "a: |\n   x\n  &x b: *x" [Event.defineAnchor "x", Event.useAlias "x"] :=
  ⟨10, readTwoDocs⟩

end LiteralTail

end L4YAML.Tests.Guards.TraceOfBlockAmbiguity
