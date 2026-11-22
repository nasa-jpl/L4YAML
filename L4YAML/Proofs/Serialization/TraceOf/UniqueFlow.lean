/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import L4YAML.Surface.Document
public import L4YAML.Proofs.Serialization.TraceOf.Node
public import L4YAML.Proofs.Foundation.SurfaceSpan

/-!
# Trace uniqueness over the FLOW fragment (EVENTSOF-CONCEPT §10, slice 2)

Capstone chain: Blueprint 7.7 `parse_iff_grammar` ← `TraceWellFormed` has one trace per
input ← `traceOf_unique` ← this flow fragment.

Two derivations of one span may use different constructors with the same trace
(`["a": b]` is `pairValue` or `pairJsonAdjacentValue`) and may split the span at
different intermediate positions, so the induction carries *span determinism under
the flow follow-set*: for each member `T` of the flow fragment,
`T n c s m₁ ev₁ → T n c s m₂ ev₂ → follow m₁ → follow m₂ → m₁ = m₂ ∧ ev₁ = ev₂`
(`NodeDet`, `ContentDet`, `JsonDet`, `CrossDet`, `SeqDet`, `MapDet`, `SeqEntriesDet`,
`MapEntriesDet`), proved together by strong induction on the length of the remaining
input (`allDet`).  The same-end lemmas `tFlowNode_unique`, `tFlowContent_unique`,
`tCFlowJsonNode_unique`, `tCFlowJsonContent_unique`, `tFlowSequence_unique`,
`tFlowMapping_unique`, `tCNsProperties_unique`, `tCNsTagProperty_unique`,
`tCNsAnchorProperty_unique`, `tCNsAliasNode_unique` are the corollaries with the trivial
follow.  Entries and entry lists are not prefix-free (inside `[a:b]` the span `a:` is the
plain node `a:` or the key `a` with an empty value), so `tFlowSeqEntry_unique`,
`tFlowMapEntry_unique`, `tFlowSeqEntries_unique`, `tFlowMapEntries_unique` carry the
follow (`EFollow`, resp. `CloseStop`) that the enclosing collection always provides.

The leaf span-determinism lemmas are where the proof lives: separators (`sep_det`),
anchors/aliases/tags (`anchor_det`, `alias_det`, `tag_det`), quoted scalars (`dq_det`,
`sq_det`), plain scalars including multi-line flow continuation (`plain_det`, under
`FStop`), properties (`props_det`, under `PStop`).
-/

namespace L4YAML.Proofs.Serialization.TraceOf

@[expose] public section

open L4YAML L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.SurfaceSpan

/-! ## Separator skipping -/

/-- Greedy skip over whitespace, line breaks and `#` comments. Mode `true` is
"inside a comment". Not a grammar: a superset every separator step preserves. -/
def skip : Bool → List Char → Nat → SurfPos
  | _, [], col => ⟨[], col⟩
  | false, c :: cs, col =>
      if c = ' ' ∨ c = '\t' then skip false cs (col + 1)
      else if c = '\n' ∨ c = '\r' then skip false cs 0
      else if c = '#' then skip true cs (col + 1)
      else ⟨c :: cs, col⟩
  | true, c :: cs, col =>
      if c = '\n' ∨ c = '\r' then skip false cs 0 else skip true cs (col + 1)

def skipSep (s : SurfPos) : SurfPos := skip false s.chars s.col

/-- A position no separator step can continue from (also the end of input). -/
def SepStop (s : SurfPos) : Prop :=
  match s.chars with
  | [] => True
  | c :: _ => ¬(c = ' ' ∨ c = '\t') ∧ ¬(c = '\n' ∨ c = '\r') ∧ c ≠ '#'

lemma skipSep_stop {s : SurfPos} (h : SepStop s) : skipSep s = s := by
  obtain ⟨chars, col⟩ := s
  cases chars with
  | nil => rfl
  | cons c cs =>
    obtain ⟨h1, h2, h3⟩ := h
    simp [skipSep, skip, h1, h2, h3]

lemma sswhite_skip {a m : SurfPos} (h : SSWhite a m) : skipSep a = skipSep m := by
  cases h <;> simp [skipSep, skip]

lemma gstar_sswhite_skip {a m : SurfPos} (h : GStar SSWhite a m) : skipSep a = skipSep m := by
  induction h with
  | nil => rfl
  | cons =>
    rename_i h₁ _ ih
    exact (sswhite_skip h₁).trans ih

lemma gplus_sswhite_skip {a m : SurfPos} (h : GPlus SSWhite a m) : skipSep a = skipSep m := by
  cases h with
  | mk =>
    rename_i h₁ h₂
    exact (sswhite_skip h₁).trans (gstar_sswhite_skip h₂)

lemma sbbreak_skip {a m : SurfPos} (h : SBBreak a m) : skipSep a = skipSep m := by
  cases h <;> simp [skipSep, skip]

lemma sbcomment_skip {a m : SurfPos} (h : SBComment a m) : skipSep a = skipSep m := by
  cases h with
  | «break» =>
    rename_i h
    exact sbbreak_skip h
  | eof => rfl

lemma commentChars_skip {a m : SurfPos} (h : GStar SCommentChar a m) :
    skip true a.chars a.col = skip true m.chars m.col := by
  induction h with
  | nil => rfl
  | cons =>
    rename_i h₁ _ ih
    obtain ⟨c, rest, col, hc⟩ := h₁
    have hnb : ¬(c = '\n' ∨ c = '\r') := by
      intro hc'
      apply hc
      rcases hc' with h | h <;> simp [h, isLineBreakProp, isLineFeedProp, isCarriageReturnProp]
    simp only [skip, hnb, ite_false]
    exact ih

lemma optText_comment_skip {a m m' : SurfPos} (h : GOpt SCNbCommentText a m)
    (h' : SBComment m m') : skipSep a = skipSep m' := by
  cases h with
  | none => exact sbcomment_skip h'
  | some =>
    rename_i h
    cases h with
    | mk =>
      rename_i hstar
      rename_i rest col
      have h1 := commentChars_skip hstar
      have h2 : skipSep ⟨'#' :: rest, col⟩ = skip true rest (col + 1) := by
        simp [skipSep, skip]
      rw [h2, h1]
      cases h' with
      | «break» =>
        rename_i hb
        cases hb <;> simp [skipSep, skip]
      | eof => rfl

lemma sepInLine_skip {a m : SurfPos} (h : SSeparateInLine a m) : skipSep a = skipSep m := by
  cases h with
  | whites =>
    rename_i h
    exact gplus_sswhite_skip h
  | startOfLine => rfl

lemma ssbComment_skip {a m : SurfPos} (h : SSBComment a m) : skipSep a = skipSep m := by
  cases h with
  | withSep =>
    rename_i h₁ h₂ h₃
    exact (sepInLine_skip h₁).trans (optText_comment_skip h₂ h₃)
  | noSep =>
    rename_i h
    exact sbcomment_skip h

lemma slComment_skip {a m : SurfPos} (h : SLComment a m) : skipSep a = skipSep m := by
  cases h with
  | mk =>
    rename_i h₁ h₂ h₃
    exact (sepInLine_skip h₁).trans (optText_comment_skip h₂ h₃)

lemma gstar_slComment_skip {a m : SurfPos} (h : GStar SLComment a m) : skipSep a = skipSep m := by
  induction h with
  | nil => rfl
  | cons =>
    rename_i h₁ _ ih
    exact (slComment_skip h₁).trans ih

lemma sslComments_skip {a m : SurfPos} (h : SSLComments a m) : skipSep a = skipSep m := by
  cases h with
  | withComment =>
    rename_i h₁ h₂
    exact (ssbComment_skip h₁).trans (gstar_slComment_skip h₂)
  | startOfLine =>
    rename_i h
    exact gstar_slComment_skip h

lemma sindent_skip {n : Nat} {a m : SurfPos} (h : SIndent n a m) : skipSep a = skipSep m := by
  induction h with
  | zero => rfl
  | succ =>
    rename_i ih
    exact (by simp [skipSep, skip] : skipSep _ = skipSep _).trans ih

lemma sflowLinePrefix_skip {n : Nat} {a m : SurfPos} (h : SFlowLinePrefix n a m) :
    skipSep a = skipSep m := by
  cases h with
  | mk =>
    rename_i h₁ h₂
    refine (sindent_skip h₁).trans ?_
    cases h₂ with
    | none => rfl
    | some =>
      rename_i h
      exact sepInLine_skip h

lemma slEmpty_skip {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SLEmpty n c a m) :
    skipSep a = skipSep m := by
  cases h with
  | block =>
    rename_i h₁ h₂
    refine Eq.trans ?_ (sbbreak_skip h₂)
    cases h₁ with
    | none => rfl
    | some =>
      rename_i h
      obtain ⟨_, _, h⟩ := h; exact sindent_skip h
  | flow =>
    rename_i h₁ h₂
    refine Eq.trans ?_ (sbbreak_skip h₂)
    cases h₁ with
    | none => rfl
    | some =>
      rename_i h
      exact sflowLinePrefix_skip h
  | flowLt =>
    rename_i h₁ h₂
    obtain ⟨_, _, h₁⟩ := h₁
    exact (sindent_skip h₁).trans (sbbreak_skip h₂)

lemma gstar_slEmpty_skip {n : Nat} {c : YamlContext} {a m : SurfPos}
    (h : GStar (SLEmpty n c) a m) : skipSep a = skipSep m := by
  induction h with
  | nil => rfl
  | cons =>
    rename_i h₁ _ ih
    exact (slEmpty_skip h₁).trans ih

lemma sepLines_skip {n : Nat} {a m : SurfPos} (h : SSeparateLines n a m) :
    skipSep a = skipSep m := by
  cases h with
  | commented =>
    rename_i h₁ h₂
    exact (sslComments_skip h₁).trans (sflowLinePrefix_skip h₂)
  | inline =>
    rename_i h
    exact sepInLine_skip h

lemma sep_skip {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SSeparate n c a m) :
    skipSep a = skipSep m := by
  cases c <;> simp only [SSeparate] at h
  all_goals first | exact sepLines_skip h | exact sepInLine_skip h

/-- Span determinism of a separator: its end under a `SepStop` is `skipSep`. -/
lemma sep_det {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SSeparate n c a m)
    (hs : SepStop m) : m = skipSep a := by
  rw [sep_skip h, skipSep_stop hs]

lemma gopt_sep_det {n : Nat} {c : YamlContext} {a m : SurfPos} (h : GOpt (SSeparate n c) a m)
    (hs : SepStop m) : m = skipSep a := by
  cases h with
  | none => exact (skipSep_stop hs).symm
  | some =>
    rename_i h
    exact sep_det h hs

/-! ## Maximal runs, tags, anchors, aliases -/

lemma gchar_det {p : Char → Prop} {a m₁ m₂ : SurfPos} (h₁ : GChar p a m₁) (h₂ : GChar p a m₂) :
    m₁ = m₂ := by
  cases h₁; cases h₂; rfl

lemma glit_det {ch : Char} {a m₁ m₂ : SurfPos} (h₁ : GLit ch a m₁) (h₂ : GLit ch a m₂) :
    m₁ = m₂ := by
  cases h₁; cases h₂; rfl

lemma gchar_mono {p q : Char → Prop} (hpq : ∀ c, p c → q c) {a b : SurfPos} (h : GChar p a b) :
    GChar q a b := by
  cases h with
  | mk c rest col hc => exact GChar.mk c rest col (hpq c hc)

/-- Two maximal runs from one position end together; the first may use a
narrower class (`p ⊆ q`) as long as it stops at a non-`q` character. -/
lemma run_det {p q : Char → Prop} (hpq : ∀ c, p c → q c) {a m₁ m₂ : SurfPos}
    (h₁ : GStar (GChar p) a m₁) (hn₁ : GNot (GChar q) m₁)
    (h₂ : GStar (GChar q) a m₂) (hn₂ : GNot (GChar q) m₂) : m₁ = m₂ := by
  induction h₁ generalizing m₂ with
  | nil =>
    cases h₂ with
    | nil => rfl
    | cons =>
      rename_i hc _
      exact absurd hc (hn₁ _)
  | cons =>
    rename_i hc _ ih
    have hcq := gchar_mono hpq hc
    cases h₂ with
    | nil => exact absurd hcq (hn₂ _)
    | cons =>
      rename_i hc' hrest'
      cases gchar_det hcq hc'
      exact ih hn₁ hrest' hn₂

lemma gnot_of_head {p : Char → Prop} {m : SurfPos}
    (h : ∀ c rest col, m = ⟨c :: rest, col⟩ → ¬ p c) : GNot (GChar p) m := by
  intro m' hm
  cases hm with
  | mk c rest col hc => exact h c rest col rfl hc

lemma gplus_run_det {p q : Char → Prop} (hpq : ∀ c, p c → q c) {a m₁ m₂ : SurfPos}
    (h₁ : GPlus (GChar p) a m₁) (hn₁ : GNot (GChar q) m₁)
    (h₂ : GPlus (GChar q) a m₂) (hn₂ : GNot (GChar q) m₂) : m₁ = m₂ := by
  cases h₁ with
  | mk =>
    rename_i hc hs
    cases h₂ with
    | mk =>
      rename_i hc' hs'
      have hcq := gchar_mono hpq hc
      cases gchar_det hcq hc'
      exact run_det hpq hs hn₁ hs' hn₂

lemma anchor_det {a m₁ m₂ : SurfPos} (h₁ : SCNsAnchorProperty a m₁)
    (h₂ : SCNsAnchorProperty a m₂) : m₁ = m₂ := by
  cases h₁ with
  | mk =>
    rename_i hp hn
    cases h₂ with
    | mk =>
      exact gplus_run_det (fun _ h => h) hp hn (by assumption) (by assumption)

lemma alias_det {a m₁ m₂ : SurfPos} (h₁ : SCNsAliasNode a m₁) (h₂ : SCNsAliasNode a m₂) :
    m₁ = m₂ := by
  cases h₁ with
  | mk =>
    rename_i hp hn
    cases h₂ with
    | mk =>
      exact gplus_run_det (fun _ h => h) hp hn (by assumption) (by assumption)

/-- What may follow a tag property in this fragment: anything but a character
that could continue a longer tag (`!` for `named`/`secondary`, `<` for `verbatim`). -/
def TagStop (s : SurfPos) : Prop :=
  match s.chars with
  | [] => True
  | c :: _ => c ≠ '!' ∧ c ≠ '<'

lemma word_tag {c : Char} (h : isWordCharProp c) : isTagCharProp c := by
  refine ⟨Or.inl h, ?_, ?_⟩
  · rintro rfl
    simp [isWordCharProp, isAsciiLetterProp] at h
  · intro hf
    simp [isFlowIndicatorProp] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;> simp [isWordCharProp, isAsciiLetterProp] at h

lemma not_word_lt : ¬ isWordCharProp '<' := by simp [isWordCharProp, isAsciiLetterProp]
lemma not_word_bang : ¬ isWordCharProp '!' := by simp [isWordCharProp, isAsciiLetterProp]
lemma not_tag_lt : ¬ isTagCharProp '<' := by
  simp [isTagCharProp, isUriCharProp, isWordCharProp, isAsciiLetterProp]
lemma not_tag_bang : ¬ isTagCharProp '!' := by simp [isTagCharProp]
lemma not_uri_gt : ¬ isUriCharProp '>' := by
  simp [isUriCharProp, isWordCharProp, isAsciiLetterProp]

lemma gplus_head {p : Char → Prop} {c : Char} {rest : List Char} {col : Nat} {m : SurfPos}
    (h : GPlus (GChar p) ⟨c :: rest, col⟩ m) : p c := by
  cases h with
  | mk =>
    rename_i hc _
    cases hc with
    | mk _ _ _ hpc => exact hpc

lemma gnot_head {p : Char → Prop} {c : Char} {rest : List Char} {col : Nat}
    (h : GNot (GChar p) ⟨c :: rest, col⟩) : ¬ p c :=
  fun hp => h _ (GChar.mk c rest col hp)

lemma gplus_nil {p : Char → Prop} {col : Nat} {m : SurfPos}
    (h : GPlus (GChar p) ⟨[], col⟩ m) : False := by
  cases h with
  | mk => cases ‹GChar p _ _›

lemma tag_inv_nil {col : Nat} {m : SurfPos} (h : SCNsTagProperty ⟨['!'], col⟩ m) :
    m = ⟨[], col + 1⟩ := by
  cases h with
  | verbatim => cases ‹GLit '<' _ _›
  | named => exact (gplus_nil ‹GPlus (GChar isWordCharProp) _ _›).elim
  | nonSpecific => rfl
  | primary => exact (gplus_nil ‹GPlus (GChar isTagCharProp) _ _›).elim

lemma tag_inv_lt {rest : List Char} {col : Nat} {m : SurfPos}
    (h : SCNsTagProperty ⟨'!' :: '<' :: rest, col⟩ m) (t : TagStop m) :
    ∃ s₂, GPlus (GChar isUriCharProp) ⟨rest, col + 1 + 1⟩ s₂ ∧ GLit '>' s₂ m := by
  cases h with
  | verbatim =>
    cases ‹GLit '<' _ _›
    exact ⟨_, ‹GPlus (GChar isUriCharProp) _ _›, ‹GLit '>' _ _›⟩
  | named => exact absurd (gplus_head ‹GPlus (GChar isWordCharProp) _ _›) not_word_lt
  | nonSpecific => simp [TagStop] at t
  | primary => exact absurd (gplus_head ‹GPlus (GChar isTagCharProp) _ _›) not_tag_lt

lemma tag_inv_bang {srest : List Char} {col : Nat} {m : SurfPos}
    (h : SCNsTagProperty ⟨'!' :: '!' :: srest, col⟩ m) (t : TagStop m) :
    GStar (GChar isTagCharProp) ⟨srest, col + 2⟩ m ∧ GNot (GChar isTagCharProp) m := by
  cases h with
  | verbatim => cases ‹GLit '<' _ _›
  | secondary => exact ⟨‹GStar (GChar isTagCharProp) _ _›, ‹GNot (GChar isTagCharProp) _›⟩
  | named => exact absurd (gplus_head ‹GPlus (GChar isWordCharProp) _ _›) not_word_bang
  | nonSpecific => simp [TagStop] at t
  | primary => exact absurd (gplus_head ‹GPlus (GChar isTagCharProp) _ _›) not_tag_bang

lemma tag_inv_word {c : Char} {rest : List Char} {col : Nat} {m : SurfPos}
    (hw : isWordCharProp c) (h : SCNsTagProperty ⟨'!' :: c :: rest, col⟩ m) :
    (∃ s₁ s₂, GPlus (GChar isWordCharProp) ⟨c :: rest, col + 1⟩ s₁ ∧ GLit '!' s₁ s₂ ∧
        GStar (GChar isTagCharProp) s₂ m ∧ GNot (GChar isTagCharProp) m) ∨
    (GPlus (GChar isTagCharProp) ⟨c :: rest, col + 1⟩ m ∧ GNot (GChar isTagCharProp) m) := by
  cases h with
  | verbatim => cases ‹GLit '<' _ _›; exact absurd hw not_word_lt
  | secondary => exact absurd hw not_word_bang
  | named =>
    exact Or.inl ⟨_, _, ‹GPlus (GChar isWordCharProp) _ _›, ‹GLit '!' _ _›,
      ‹GStar (GChar isTagCharProp) _ _›, ‹GNot (GChar isTagCharProp) _›⟩
  | nonSpecific => exact absurd (word_tag hw) (gnot_head ‹GNot (GChar isTagCharProp) _›)
  | primary =>
    exact Or.inr ⟨‹GPlus (GChar isTagCharProp) _ _›, ‹GNot (GChar isTagCharProp) _›⟩

lemma tag_inv_other {c : Char} {rest : List Char} {col : Nat} {m : SurfPos}
    (hw : ¬ isWordCharProp c) (hlt : c ≠ '<') (hb : c ≠ '!')
    (h : SCNsTagProperty ⟨'!' :: c :: rest, col⟩ m) :
    (isTagCharProp c ∧ GPlus (GChar isTagCharProp) ⟨c :: rest, col + 1⟩ m ∧
        GNot (GChar isTagCharProp) m) ∨
    (¬ isTagCharProp c ∧ m = ⟨c :: rest, col + 1⟩) := by
  cases h with
  | verbatim => cases ‹GLit '<' _ _›; exact absurd rfl hlt
  | secondary => exact absurd rfl hb
  | named => exact absurd (gplus_head ‹GPlus (GChar isWordCharProp) _ _›) hw
  | nonSpecific => exact Or.inr ⟨gnot_head ‹GNot (GChar isTagCharProp) _›, rfl⟩
  | primary =>
    have hp := ‹GPlus (GChar isTagCharProp) _ _›
    exact Or.inl ⟨gplus_head hp, hp, ‹GNot (GChar isTagCharProp) _›⟩

lemma tag_head {a m : SurfPos} (h : SCNsTagProperty a m) :
    ∃ rest col, a = ⟨'!' :: rest, col⟩ := by
  cases h <;> exact ⟨_, _, rfl⟩

/-- Span determinism of a tag property under `TagStop` at both ends. -/
lemma tag_det {a m₁ m₂ : SurfPos} (h₁ : SCNsTagProperty a m₁) (h₂ : SCNsTagProperty a m₂)
    (t₁ : TagStop m₁) (t₂ : TagStop m₂) : m₁ = m₂ := by
  obtain ⟨rest, col, rfl⟩ := tag_head h₁
  cases rest with
  | nil => rw [tag_inv_nil h₁, tag_inv_nil h₂]
  | cons c rest =>
    by_cases hlt : c = '<'
    · subst hlt
      obtain ⟨s₂, hp, hgt⟩ := tag_inv_lt h₁ t₁
      obtain ⟨s₂', hp', hgt'⟩ := tag_inv_lt h₂ t₂
      have hn : GNot (GChar isUriCharProp) s₂ :=
        gnot_of_head (fun _ _ _ heq => by cases hgt; cases heq; exact not_uri_gt)
      have hn' : GNot (GChar isUriCharProp) s₂' :=
        gnot_of_head (fun _ _ _ heq => by cases hgt'; cases heq; exact not_uri_gt)
      cases gplus_run_det (fun _ h => h) hp hn hp' hn'
      exact glit_det hgt hgt'
    by_cases hb : c = '!'
    · subst hb
      obtain ⟨hs, hn⟩ := tag_inv_bang h₁ t₁
      obtain ⟨hs', hn'⟩ := tag_inv_bang h₂ t₂
      exact run_det (fun _ h => h) hs hn hs' hn'
    by_cases hw : isWordCharProp c
    · have bangNot : ∀ {s₁ s₂ : SurfPos}, GLit '!' s₁ s₂ → GNot (GChar isTagCharProp) s₁ :=
        fun hb' => gnot_of_head (fun _ _ _ heq => by cases hb'; cases heq; exact not_tag_bang)
      have bangNotW : ∀ {s₁ s₂ : SurfPos}, GLit '!' s₁ s₂ → GNot (GChar isWordCharProp) s₁ :=
        fun hb' => gnot_of_head (fun _ _ _ heq => by cases hb'; cases heq; exact not_word_bang)
      have bangStop : ∀ {s₁ s₂ : SurfPos}, GLit '!' s₁ s₂ → ¬ TagStop s₁ :=
        fun hb' t => by cases hb'; simp [TagStop] at t
      rcases tag_inv_word hw h₁ with ⟨s₁, s₂, hp, hb₁, hs, hn⟩ | ⟨hp, hn⟩ <;>
      rcases tag_inv_word hw h₂ with ⟨s₁', s₂', hp', hb₁', hs', hn'⟩ | ⟨hp', hn'⟩
      · cases gplus_run_det (fun _ h => h) hp (bangNotW hb₁) hp' (bangNotW hb₁')
        cases glit_det hb₁ hb₁'
        exact run_det (fun _ h => h) hs hn hs' hn'
      · cases gplus_run_det (fun _ h => word_tag h) hp (bangNot hb₁) hp' hn'
        exact absurd t₂ (bangStop hb₁)
      · cases gplus_run_det (fun _ h => word_tag h) hp' (bangNot hb₁') hp hn
        exact absurd t₁ (bangStop hb₁')
      · exact gplus_run_det (fun _ h => h) hp hn hp' hn'
    · rcases tag_inv_other hw hlt hb h₁ with ⟨ht, hp, hn⟩ | ⟨ht, rfl⟩ <;>
      rcases tag_inv_other hw hlt hb h₂ with ⟨ht', hp', hn'⟩ | ⟨ht', rfl⟩
      · exact gplus_run_det (fun _ h => h) hp hn hp' hn'
      · exact absurd ht ht'
      · exact absurd ht' ht
      · rfl

/-! ## Whitespace-invariant scans -/

/-- A scan function that steps over white space and line breaks the way the
grammar does (`col + 1` per white, `0` after a break). -/
structure WsInv (f : SurfPos → SurfPos) : Prop where
  space : ∀ cs col, f ⟨' ' :: cs, col⟩ = f ⟨cs, col + 1⟩
  tab : ∀ cs col, f ⟨'\t' :: cs, col⟩ = f ⟨cs, col + 1⟩
  lf : ∀ cs col, f ⟨'\n' :: cs, col⟩ = f ⟨cs, 0⟩
  cr : ∀ cs col, f ⟨'\r' :: cs, col⟩ = f ⟨cs, 0⟩

namespace WsInv

variable {f : SurfPos → SurfPos} (hf : WsInv f)
include hf

lemma sswhite {a m : SurfPos} (h : SSWhite a m) : f a = f m := by
  cases h
  · exact hf.space _ _
  · exact hf.tab _ _

lemma gstar_sswhite {a m : SurfPos} (h : GStar SSWhite a m) : f a = f m := by
  induction h with
  | nil => rfl
  | cons => rename_i h₁ _ ih; exact (hf.sswhite h₁).trans ih

lemma sbbreak {a m : SurfPos} (h : SBBreak a m) : f a = f m := by
  cases h
  · exact (hf.cr _ _).trans (hf.lf _ _)
  · exact hf.cr _ _
  · exact hf.lf _ _

lemma sindent {n : Nat} {a m : SurfPos} (h : SIndent n a m) : f a = f m := by
  induction h with
  | zero => rfl
  | succ => rename_i ih; exact (hf.space _ _).trans ih

lemma sepInLine {a m : SurfPos} (h : SSeparateInLine a m) : f a = f m := by
  cases h with
  | whites => cases ‹GPlus SSWhite _ _› with
    | mk => exact (hf.sswhite ‹SSWhite _ _›).trans (hf.gstar_sswhite ‹GStar SSWhite _ _›)
  | startOfLine => rfl

lemma flowLinePrefix {n : Nat} {a m : SurfPos} (h : SFlowLinePrefix n a m) : f a = f m := by
  cases h with
  | mk =>
    refine (hf.sindent ‹SIndent n _ _›).trans ?_
    cases ‹GOpt SSeparateInLine _ _› with
    | none => rfl
    | some => exact hf.sepInLine ‹SSeparateInLine _ _›

lemma slEmpty {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SLEmpty n c a m) : f a = f m := by
  cases h with
  | block =>
    refine Eq.trans ?_ (hf.sbbreak ‹SBBreak _ _›)
    cases ‹GOpt (SIndentLe n) _ _› with
    | none => rfl
    | some => obtain ⟨_, _, h⟩ := ‹SIndentLe n _ _›; exact hf.sindent h
  | flow =>
    refine Eq.trans ?_ (hf.sbbreak ‹SBBreak _ _›)
    cases ‹GOpt (SFlowLinePrefix n) _ _› with
    | none => rfl
    | some => exact hf.flowLinePrefix ‹SFlowLinePrefix n _ _›
  | flowLt =>
    obtain ⟨_, _, h⟩ := ‹SIndentLt n _ _›
    exact (hf.sindent h).trans (hf.sbbreak ‹SBBreak _ _›)

lemma gstar_slEmpty {n : Nat} {c : YamlContext} {a m : SurfPos} (h : GStar (SLEmpty n c) a m) :
    f a = f m := by
  induction h with
  | nil => rfl
  | cons => rename_i h₁ _ ih; exact (hf.slEmpty h₁).trans ih

end WsInv

/-! ## Quoted scalars -/

def dqScan : List Char → Nat → SurfPos
  | [], col => ⟨[], col⟩
  | '"' :: cs, col => ⟨cs, col + 1⟩
  | '\\' :: [], col => ⟨[], col + 1⟩
  | '\\' :: c :: cs, col => dqScan cs (if c = '\n' ∨ c = '\r' then 0 else col + 2)
  | c :: cs, col => dqScan cs (if c = '\n' ∨ c = '\r' then 0 else col + 1)

def dqScanP (s : SurfPos) : SurfPos := dqScan s.chars s.col

lemma dqScanP_ws : WsInv dqScanP := by
  constructor <;> intro cs col <;> simp [dqScanP, dqScan]

lemma not_break_iff {c : Char} : ¬ isLineBreakProp c ↔ ¬ (c = '\n' ∨ c = '\r') := by
  simp [isLineBreakProp, isLineFeedProp, isCarriageReturnProp]

lemma namedEscape_not_break {ec : Char} (h : L4YAML.Grammar.isNamedEscapeChar ec) :
    ¬ (ec = '\n' ∨ ec = '\r') := by
  rintro (rfl | rfl) <;> revert h <;> decide

lemma hex_facts {c : Char} (h : isNsHexDigit c) :
    c ≠ '"' ∧ c ≠ '\\' ∧ c ≠ '\'' ∧ ¬ (c = '\n' ∨ c = '\r') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl; simp [isNsHexDigit] at h
  · rintro rfl; simp [isNsHexDigit] at h
  · rintro rfl; simp [isNsHexDigit] at h
  · rintro (rfl | rfl) <;> simp [isNsHexDigit] at h

set_option linter.unusedSimpArgs false in
lemma dqScan_hex {c : Char} (h : isNsHexDigit c) (cs : List Char) (col : Nat) :
    dqScan (c :: cs) col = dqScan cs (col + 1) := by
  obtain ⟨h1, h2, -, h4⟩ := hex_facts h
  simp [dqScan, h1, h2, h4]

lemma dqChar_scan {a m : SurfPos} (h : SNbDoubleChar a m) : dqScanP a = dqScanP m := by
  cases h with
  | plain c rest col hb hbs hdq =>
    have hb' := not_break_iff.mp hb
    simp [dqScanP, dqScan, hbs, hb']
  | escape ec rest col hv =>
    have := namedEscape_not_break hv
    simp [dqScanP, dqScan, this]
  | hexEscape2 rest col h1 h2 hh1 hh2 =>
    simp only [dqScanP, dqScan, dqScan_hex hh1, dqScan_hex hh2]
    simp
  | hexEscape4 rest col h1 h2 h3 h4 hh1 hh2 hh3 hh4 =>
    simp only [dqScanP, dqScan, dqScan_hex hh1, dqScan_hex hh2, dqScan_hex hh3, dqScan_hex hh4]
    simp
  | hexEscape8 rest col h1 h2 h3 h4 h5 h6 h7 h8 hh1 hh2 hh3 hh4 hh5 hh6 hh7 hh8 =>
    simp only [dqScanP, dqScan, dqScan_hex hh1, dqScan_hex hh2, dqScan_hex hh3, dqScan_hex hh4,
      dqScan_hex hh5, dqScan_hex hh6, dqScan_hex hh7, dqScan_hex hh8]
    simp

lemma dqOneLine_scan {a m : SurfPos} (h : SNbDoubleOneLine a m) : dqScanP a = dqScanP m := by
  induction h with
  | nil => rfl
  | cons => rename_i h₁ _ ih; exact (dqChar_scan h₁).trans ih

lemma dqEscaped_scan {n : Nat} {a m : SurfPos} (h : SSDoubleEscaped n a m) :
    dqScanP a = dqScanP m := by
  cases h with
  | mk =>
    refine (dqScanP_ws.gstar_sswhite ‹GStar SSWhite _ _›).trans ?_
    refine Eq.trans ?_ ((dqScanP_ws.gstar_slEmpty ‹GStar (SLEmpty n .flowIn) _ _›).trans
      (dqScanP_ws.flowLinePrefix ‹SFlowLinePrefix n _ _›))
    cases ‹GLit '\\' _ _›
    cases ‹SBNonContent _ _› <;> simp [dqScanP, dqScan]

lemma dqBreak_scan {n : Nat} {a m : SurfPos} (h : SSDoubleBreak n a m) : dqScanP a = dqScanP m := by
  cases h with
  | escaped => exact dqEscaped_scan ‹SSDoubleEscaped n _ _›
  | flowFold =>
    exact (dqScanP_ws.sbbreak ‹SBBreak _ _›).trans
      ((dqScanP_ws.gstar_slEmpty ‹GStar (SLEmpty n .flowIn) _ _›).trans
        (dqScanP_ws.flowLinePrefix ‹SFlowLinePrefix n _ _›))

lemma dqMulti_scan {n : Nat} {a m : SurfPos} (h : SNbDoubleMultiLine n a m) :
    dqScanP a = dqScanP m := by
  induction h with
  | single => exact dqOneLine_scan ‹SNbDoubleOneLine _ _›
  | multi =>
    rename_i ih
    have e1 := dqOneLine_scan ‹SNbDoubleOneLine _ _›
    have e2 := dqBreak_scan ‹SSDoubleBreak n _ _›
    exact e1.trans (e2.trans ih)

lemma dqText_scan {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SNbDoubleText n c a m) :
    dqScanP a = dqScanP m := by
  cases c <;> simp only [SNbDoubleText] at h
  all_goals first | exact dqMulti_scan h | exact dqOneLine_scan h

lemma dq_end {n : Nat} {c : YamlContext} {rest : List Char} {col : Nat} {m : SurfPos}
    (h : SCDoubleQuoted n c ⟨'"' :: rest, col⟩ m) : m = dqScan rest (col + 1) := by
  cases h with
  | mk =>
    cases ‹GLit '"' ⟨'"' :: rest, col⟩ _›
    have h1 := dqText_scan ‹SNbDoubleText n c _ _›
    cases ‹GLit '"' _ m›
    simp [dqScanP, dqScan] at h1
    exact h1.symm

/-- Span determinism of a double-quoted scalar: no follow-set needed. -/
lemma dq_det {n : Nat} {c : YamlContext} {a m₁ m₂ : SurfPos} (h₁ : SCDoubleQuoted n c a m₁)
    (h₂ : SCDoubleQuoted n c a m₂) : m₁ = m₂ := by
  obtain ⟨rest, col, rfl⟩ : ∃ rest col, a = ⟨'"' :: rest, col⟩ := by
    cases h₁ with
    | mk => cases ‹GLit '"' a _›; exact ⟨_, _, rfl⟩
  rw [dq_end h₁, dq_end h₂]

/-! ## Where a separator can start, and the flow follow-set -/

/-- Heads a (non-empty) separator may begin with: white, break, or `#` at column 0. -/
def SepHead (s : SurfPos) : Prop :=
  match s.chars with
  | [] => True
  | d :: _ => d = ' ' ∨ d = '\t' ∨ d = '\n' ∨ d = '\r' ∨ (d = '#' ∧ s.col = 0)

lemma sswhite_head {a m : SurfPos} (h : SSWhite a m) : SepHead a := by
  cases h <;> simp [SepHead]

lemma sbbreak_head {a m : SurfPos} (h : SBBreak a m) : SepHead a := by
  cases h <;> simp [SepHead]

lemma sbcomment_head {a m : SurfPos} (h : SBComment a m) : SepHead a := by
  cases h with
  | «break» => exact sbbreak_head ‹SBBreak _ _›
  | eof => simp [SepHead]

lemma sepInLine_shape {a m : SurfPos} (h : SSeparateInLine a m) : a = m ∨ SepHead a := by
  cases h with
  | whites =>
    cases ‹GPlus SSWhite _ _› with
    | mk => exact Or.inr (sswhite_head ‹SSWhite _ _›)
  | startOfLine => exact Or.inl rfl

lemma optText_comment_head {a w x : SurfPos} (h : GOpt SCNbCommentText a w) (h' : SBComment w x)
    (hcol : a.col = 0) : SepHead a := by
  cases h with
  | none => exact sbcomment_head h'
  | some =>
    cases ‹SCNbCommentText a _› with
    | mk => simp [SepHead] at hcol ⊢; exact hcol

lemma ssbComment_head {a m : SurfPos} (h : SSBComment a m) : SepHead a := by
  cases h with
  | withSep =>
    cases ‹SSeparateInLine a _› with
    | whites =>
      cases ‹GPlus SSWhite _ _› with
      | mk => exact sswhite_head ‹SSWhite _ _›
    | startOfLine => exact optText_comment_head ‹GOpt SCNbCommentText _ _› ‹SBComment _ _› rfl
  | noSep => exact sbcomment_head ‹SBComment _ _›

lemma slComment_head {a m : SurfPos} (h : SLComment a m) : SepHead a := by
  cases h with
  | mk =>
    cases ‹SSeparateInLine a _› with
    | whites =>
      cases ‹GPlus SSWhite _ _› with
      | mk => exact sswhite_head ‹SSWhite _ _›
    | startOfLine => exact optText_comment_head ‹GOpt SCNbCommentText _ _› ‹SBComment _ _› rfl

lemma sslComments_shape {a m : SurfPos} (h : SSLComments a m) : a = m ∨ SepHead a := by
  cases h with
  | withComment => exact Or.inr (ssbComment_head ‹SSBComment _ _›)
  | startOfLine =>
    cases ‹GStar SLComment _ _› with
    | nil => exact Or.inl rfl
    | cons => exact Or.inr (slComment_head ‹SLComment _ _›)

lemma flowLinePrefix_shape {n : Nat} {a m : SurfPos} (h : SFlowLinePrefix n a m) :
    a = m ∨ SepHead a := by
  cases h with
  | mk =>
    cases ‹SIndent n a _› with
    | succ => simp [SepHead]
    | zero =>
      cases ‹GOpt SSeparateInLine _ _› with
      | none => exact Or.inl rfl
      | some => exact sepInLine_shape ‹SSeparateInLine _ _›

lemma sepLines_shape {n : Nat} {a m : SurfPos} (h : SSeparateLines n a m) :
    a = m ∨ SepHead a := by
  cases h with
  | inline => exact sepInLine_shape ‹SSeparateInLine _ _›
  | commented =>
    rcases sslComments_shape ‹SSLComments a _› with rfl | hh
    · exact flowLinePrefix_shape ‹SFlowLinePrefix n _ _›
    · exact Or.inr hh

/-- A separator is empty or begins with a `SepHead`. -/
lemma sep_shape {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SSeparate n c a m) :
    a = m ∨ SepHead a := by
  cases c <;> simp only [SSeparate] at h
  all_goals first | exact sepLines_shape h | exact sepInLine_shape h

/-- After `:` in this fragment: white, break, flow indicator, or end of input. -/
def ColonFollow : List Char → Prop
  | [] => True
  | d :: _ => d = ' ' ∨ d = '\t' ∨ d = '\n' ∨ d = '\r' ∨ isFlowIndicatorProp d

/-- The literal that closes a node or entry in the flow fragment. -/
def LitStop (t : SurfPos) : Prop :=
  match t.chars with
  | [] => False
  | l :: rest => l = ',' ∨ l = ']' ∨ l = '}' ∨ (l = ':' ∧ ColonFollow rest)

/-- What may follow a node or entry: an optional separator, then a `LitStop`. -/
def FStop (n : Nat) (c : YamlContext) (s : SurfPos) : Prop :=
  ∃ t, GOpt (SSeparate n c) s t ∧ LitStop t

lemma litStop_sepStop {t : SurfPos} (h : LitStop t) : SepStop t := by
  obtain ⟨chars, col⟩ := t
  cases chars with
  | nil => simp [LitStop] at h
  | cons l rest =>
    simp only [LitStop] at h
    rcases h with rfl | rfl | rfl | ⟨rfl, -⟩ <;> simp [SepStop]

lemma litStop_tagStop {t : SurfPos} (h : LitStop t) : TagStop t := by
  obtain ⟨chars, col⟩ := t
  cases chars with
  | nil => simp [LitStop] at h
  | cons l rest =>
    simp only [LitStop] at h
    rcases h with rfl | rfl | rfl | ⟨rfl, -⟩ <;> simp [TagStop]

lemma sepHead_tagStop {t : SurfPos} (h : SepHead t) : TagStop t := by
  obtain ⟨chars, col⟩ := t
  cases chars with
  | nil => simp [TagStop]
  | cons l rest =>
    simp only [SepHead] at h
    rcases h with rfl | rfl | rfl | rfl | ⟨rfl, -⟩ <;> simp [TagStop]

lemma fstop_tagStop {n : Nat} {c : YamlContext} {m : SurfPos} (h : FStop n c m) : TagStop m := by
  obtain ⟨t, hopt, hl⟩ := h
  cases hopt with
  | none => exact litStop_tagStop hl
  | some =>
    rcases sep_shape ‹SSeparate n c m _› with rfl | hh
    · exact litStop_tagStop hl
    · exact sepHead_tagStop hh

/-- `'` cannot be the next character. -/
def NotQuote (m : SurfPos) : Prop := ∀ rest col, m ≠ ⟨'\'' :: rest, col⟩

lemma fstop_notQuote {n : Nat} {c : YamlContext} {m : SurfPos} (h : FStop n c m) : NotQuote m := by
  intro rest col heq
  subst heq
  obtain ⟨t, hopt, hl⟩ := h
  cases hopt with
  | none => simp [LitStop] at hl
  | some =>
    rcases sep_shape ‹SSeparate n c _ _› with heq | hh
    · subst heq; simp [LitStop] at hl
    · simp [SepHead] at hh

/-! ## Single-quoted scalars -/

def sqScan : List Char → Nat → SurfPos
  | [], col => ⟨[], col⟩
  | '\'' :: '\'' :: cs, col => sqScan cs (col + 2)
  | '\'' :: cs, col => ⟨cs, col + 1⟩
  | c :: cs, col => sqScan cs (if c = '\n' ∨ c = '\r' then 0 else col + 1)

def sqScanP (s : SurfPos) : SurfPos := sqScan s.chars s.col

lemma sqScanP_ws : WsInv sqScanP := by
  constructor <;> intro cs col <;> simp [sqScanP, sqScan]

lemma sqChar_scan {a m : SurfPos} (h : SNbSingleChar a m) : sqScanP a = sqScanP m := by
  cases h with
  | plain c rest col hb hsq =>
    have hb' := not_break_iff.mp hb
    simp [sqScanP, sqScan, hsq, hb']
  | escapedQuote rest col => simp [sqScanP, sqScan]

lemma sqOneLine_scan {a m : SurfPos} (h : SNbSingleOneLine a m) : sqScanP a = sqScanP m := by
  induction h with
  | nil => rfl
  | cons => rename_i h₁ _ ih; exact (sqChar_scan h₁).trans ih

lemma sqMulti_scan {n : Nat} {a m : SurfPos} (h : SNbSingleMultiLine n a m) :
    sqScanP a = sqScanP m := by
  induction h with
  | single => exact sqOneLine_scan ‹SNbSingleOneLine _ _›
  | multi =>
    rename_i ih
    have e1 := sqOneLine_scan ‹SNbSingleOneLine _ _›
    have e2 := sqScanP_ws.sbbreak ‹SBBreak _ _›
    have e3 := sqScanP_ws.gstar_slEmpty ‹GStar (SLEmpty n .flowIn) _ _›
    have e4 := sqScanP_ws.flowLinePrefix ‹SFlowLinePrefix n _ _›
    exact e1.trans (e2.trans (e3.trans (e4.trans ih)))

lemma sqText_scan {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SNbSingleText n c a m) :
    sqScanP a = sqScanP m := by
  cases c <;> simp only [SNbSingleText] at h
  all_goals first | exact sqMulti_scan h | exact sqOneLine_scan h

lemma sqScan_close {rest : List Char} {col : Nat} (hm : NotQuote ⟨rest, col + 1⟩) :
    sqScan ('\'' :: rest) col = ⟨rest, col + 1⟩ := by
  cases rest with
  | nil => simp [sqScan]
  | cons d ds =>
    have hd : d ≠ '\'' := fun hd => hm ds (col + 1) (by subst hd; rfl)
    simp [sqScan, hd]

lemma sq_end {n : Nat} {c : YamlContext} {rest : List Char} {col : Nat} {m : SurfPos}
    (h : SCSingleQuoted n c ⟨'\'' :: rest, col⟩ m) (hm : NotQuote m) :
    m = sqScan rest (col + 1) := by
  cases h with
  | mk =>
    cases ‹GLit '\'' ⟨'\'' :: rest, col⟩ _›
    have h1 := sqText_scan ‹SNbSingleText n c _ _›
    cases ‹GLit '\'' _ m›
    simp only [sqScanP] at h1
    rw [sqScan_close hm] at h1
    exact h1.symm

/-- Span determinism of a single-quoted scalar under the follow-set (`''` would
otherwise let a derivation stop one quote early). -/
lemma sq_det {n : Nat} {c : YamlContext} {a m₁ m₂ : SurfPos} (h₁ : SCSingleQuoted n c a m₁)
    (h₂ : SCSingleQuoted n c a m₂) (q₁ : NotQuote m₁) (q₂ : NotQuote m₂) : m₁ = m₂ := by
  obtain ⟨rest, col, rfl⟩ : ∃ rest col, a = ⟨'\'' :: rest, col⟩ := by
    cases h₁ with
    | mk => cases ‹GLit '\'' a _›; exact ⟨_, _, rfl⟩
  rw [sq_end h₁ q₁, sq_end h₂ q₂]

/-! ## Plain scalars -/

/-- Skip white space and line breaks only (no comments). -/
def skipWS : List Char → Nat → SurfPos
  | [], col => ⟨[], col⟩
  | c :: cs, col =>
      if c = ' ' ∨ c = '\t' then skipWS cs (col + 1)
      else if c = '\n' ∨ c = '\r' then skipWS cs 0
      else ⟨c :: cs, col⟩

def skipWSP (s : SurfPos) : SurfPos := skipWS s.chars s.col

lemma skipWSP_ws : WsInv skipWSP := by
  constructor <;> intro cs col <;> simp [skipWSP, skipWS]

lemma skipSep_ws : WsInv skipSep := by
  constructor <;> intro cs col <;> simp [skipSep, skip]

/-- Where one plain-scalar step from `x` must end: skip white/breaks, consume one char. -/
def stepEnd (x : SurfPos) : SurfPos :=
  ⟨(skipWSP x).chars.tail, (skipWSP x).col + 1⟩

/-- One step of a plain scalar after its first character: an in-line entry, or a
line continuation up to and including its first plain character. -/
inductive PStep (n : Nat) (c : YamlContext) : SurfPos → SurfPos → Prop where
  | entry {x z : SurfPos} : SNbNsPlainInLineEntry c x z → PStep n c x z
  | line {x a b d e z : SurfPos} :
      GStar SSWhite x a → SBBreak a b → GStar (SLEmpty n .flowIn) b d →
      SFlowLinePrefix n d e → SNsPlainChar c e z → PStep n c x z

def FlowCtx (c : YamlContext) : Prop := c = .flowIn ∨ c = .flowKey

lemma plainSafe_nsChar {c : YamlContext} {p : Char} (h : isNsPlainSafe c p) : isNsChar p := by
  cases c <;> simp only [isNsPlainSafe] at h
  all_goals first | exact h | exact h.1

lemma plainSafe_flow {c : YamlContext} (hc : FlowCtx c) {p : Char} (h : isNsPlainSafe c p) :
    ¬ isFlowIndicatorProp p := by
  rcases hc with rfl | rfl <;> exact h.2

lemma nsChar_facts {p : Char} (h : isNsChar p) :
    ¬ (p = ' ' ∨ p = '\t') ∧ ¬ (p = '\n' ∨ p = '\r') := by
  obtain ⟨hb, hw, -, -⟩ := h
  refine ⟨?_, not_break_iff.mp hb⟩
  rintro (rfl | rfl) <;> simp [isWhiteSpaceProp, isSpaceProp, isTabProp] at hw

lemma plainChar_pos {c : YamlContext} {u z : SurfPos} (h : SNsPlainChar c u z) :
    ∃ p rest col, u = ⟨p :: rest, col⟩ ∧ z = ⟨rest, col + 1⟩ ∧
      ¬ (p = ' ' ∨ p = '\t') ∧ ¬ (p = '\n' ∨ p = '\r') ∧ p ≠ '#' := by
  cases h with
  | safe ch rest col hs _ hh =>
    obtain ⟨h1, h2⟩ := nsChar_facts (plainSafe_nsChar hs)
    exact ⟨ch, rest, col, rfl, rfl, h1, h2, hh⟩
  | colonSafe _ next rest col _ => exact ⟨':', next :: rest, col, rfl, rfl, by simp, by simp, by simp⟩

lemma skipWS_stop {p : Char} {rest : List Char} {col : Nat} (h1 : ¬ (p = ' ' ∨ p = '\t'))
    (h2 : ¬ (p = '\n' ∨ p = '\r')) : skipWSP ⟨p :: rest, col⟩ = ⟨p :: rest, col⟩ := by
  simp [skipWSP, skipWS, h1, h2]

lemma pstep_end {n : Nat} {c : YamlContext} {x z : SurfPos} (h : PStep n c x z) : z = stepEnd x := by
  cases h with
  | entry he =>
    cases he with
    | mk =>
      obtain ⟨p, rest, col, rfl, rfl, h1, h2, -⟩ := plainChar_pos ‹SNsPlainChar c _ _›
      have e := skipWSP_ws.gstar_sswhite ‹GStar SSWhite x _›
      simp only [stepEnd, e, skipWS_stop h1 h2, List.tail_cons]
    | hash =>
      cases ‹GLit '#' x z›
      simp [stepEnd, skipWSP, skipWS]
  | line hw hb hl hp hch =>
    obtain ⟨p, rest, col, rfl, rfl, h1, h2, -⟩ := plainChar_pos hch
    have e := (skipWSP_ws.gstar_sswhite hw).trans ((skipWSP_ws.sbbreak hb).trans
      ((skipWSP_ws.gstar_slEmpty hl).trans (skipWSP_ws.flowLinePrefix hp)))
    simp only [stepEnd, e, skipWS_stop h1 h2, List.tail_cons]

lemma pstep_det {n : Nat} {c : YamlContext} {x z₁ z₂ : SurfPos} (h₁ : PStep n c x z₁)
    (h₂ : PStep n c x z₂) : z₁ = z₂ := by
  rw [pstep_end h₁, pstep_end h₂]

lemma pstep_col {n : Nat} {c : YamlContext} {x z : SurfPos} (h : PStep n c x z) : 1 ≤ z.col := by
  rw [pstep_end h]; simp [stepEnd]

/-- Two runs of a deterministic step relation that both stop end together. -/
lemma star_det {S : SurfPos → SurfPos → Prop} (hdet : ∀ x z₁ z₂, S x z₁ → S x z₂ → z₁ = z₂)
    {a m₁ m₂ : SurfPos} (h₁ : GStar S a m₁) (hn₁ : ∀ z, ¬ S m₁ z) (h₂ : GStar S a m₂)
    (hn₂ : ∀ z, ¬ S m₂ z) : m₁ = m₂ := by
  induction h₁ generalizing m₂ with
  | nil =>
    cases h₂ with
    | nil => rfl
    | cons => rename_i hc _; exact absurd hc (hn₁ _)
  | cons =>
    rename_i hc _ ih
    cases h₂ with
    | nil => exact absurd hc (hn₂ _)
    | cons =>
      rename_i hc' hrest'
      cases hdet _ _ _ hc hc'
      exact ih hn₁ hrest' hn₂

lemma gstar_append {P : SurfPos → SurfPos → Prop} {a b d : SurfPos} (h₁ : GStar P a b)
    (h₂ : GStar P b d) : GStar P a d := by
  induction h₁ with
  | nil => exact h₂
  | cons => rename_i hc _ ih; exact GStar.cons _ _ _ hc (ih h₂)

lemma gstar_mono {P Q : SurfPos → SurfPos → Prop} (hpq : ∀ x y, P x y → Q x y) {a b : SurfPos}
    (h : GStar P a b) : GStar Q a b := by
  induction h with
  | nil => exact GStar.nil _
  | cons => rename_i hc _ ih; exact GStar.cons _ _ _ (hpq _ _ hc) ih

lemma nextLine_steps {n : Nat} {c : YamlContext} {x z : SurfPos} (h : SSNsPlainNextLine n c x z) :
    GStar (PStep n c) x z := by
  cases h with
  | mk =>
    refine GStar.cons _ _ _ (PStep.line ‹GStar SSWhite x _› ‹SBBreak _ _›
      ‹GStar (SLEmpty n .flowIn) _ _› ‹SFlowLinePrefix n _ _› ‹SNsPlainChar c _ _›) ?_
    exact gstar_mono (fun _ _ he => PStep.entry he) ‹GStar (SNbNsPlainInLineEntry c) _ z›

lemma nextLines_steps {n : Nat} {c : YamlContext} {a m : SurfPos}
    (h : GStar (SSNsPlainNextLine n c) a m) : GStar (PStep n c) a m := by
  induction h with
  | nil => exact GStar.nil _
  | cons => rename_i h₁ _ ih; exact gstar_append (nextLine_steps h₁) ih

lemma oneLine_steps {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SNsPlainOneLine c a m) :
    ∃ a₁, SNsPlainFirst c a a₁ ∧ GStar (PStep n c) a₁ m := by
  cases h with
  | mk =>
    exact ⟨_, ‹SNsPlainFirst c a _›,
      gstar_mono (fun _ _ he => PStep.entry he) ‹GStar (SNbNsPlainInLineEntry c) _ m›⟩

lemma plain_steps {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SNsPlain n c a m) :
    ∃ a₁, SNsPlainFirst c a a₁ ∧ GStar (PStep n c) a₁ m := by
  have multi : ∀ {m}, SNsPlainMultiLine n c a m → ∃ a₁, SNsPlainFirst c a a₁ ∧ GStar (PStep n c) a₁ m := by
    intro m h
    cases h with
    | mk =>
      obtain ⟨a₁, hf, hs⟩ := oneLine_steps (n := n) ‹SNsPlainOneLine c a _›
      exact ⟨a₁, hf, gstar_append hs (nextLines_steps ‹GStar (SSNsPlainNextLine n c) _ m›)⟩
  cases c <;> simp only [SNsPlain] at h
  all_goals first | exact multi h | exact oneLine_steps h

lemma first_det {c : YamlContext} {a a₁ a₂ : SurfPos} (h₁ : SNsPlainFirst c a a₁)
    (h₂ : SNsPlainFirst c a a₂) : a₁ = a₂ := by
  cases h₁ <;> cases h₂ <;> rfl

lemma first_col {c : YamlContext} {a a₁ : SurfPos} (h : SNsPlainFirst c a a₁) : 1 ≤ a₁.col := by
  cases h <;> simp

lemma steps_col {n : Nat} {c : YamlContext} {a m : SurfPos} (h : GStar (PStep n c) a m)
    (ha : 1 ≤ a.col) : 1 ≤ m.col := by
  induction h with
  | nil => exact ha
  | cons => rename_i hc _ ih; exact ih (pstep_col hc)

lemma plain_col {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SNsPlain n c a m) : 1 ≤ m.col := by
  obtain ⟨a₁, hf, hs⟩ := plain_steps h
  exact steps_col hs (first_col hf)

/-- No plain-scalar step is possible at a position with a legal flow follow. -/
lemma pstep_fstop {n : Nat} {c : YamlContext} (hc : FlowCtx c) {m z : SurfPos}
    (hcol : 1 ≤ m.col) (hs : PStep n c m z) (hf : FStop n c m) : False := by
  obtain ⟨t, hopt, hl⟩ := hf
  have ht : t = skipSep m := gopt_sep_det hopt (litStop_sepStop hl)
  -- the step's plain character sits exactly where the separator stops
  have key : ∀ {e z}, skipSep m = skipSep e → SNsPlainChar c e z → False := by
    intro e z he hch
    obtain ⟨p, rest, col, rfl, -, h1, h2, h3⟩ := plainChar_pos hch
    have hstop : SepStop ⟨p :: rest, col⟩ := ⟨h1, h2, h3⟩
    rw [he, skipSep_stop hstop] at ht
    subst ht
    cases hch with
    | safe _ _ _ hsafe hnc _ =>
      have hfi := plainSafe_flow hc hsafe
      simp only [LitStop] at hl
      rcases hl with rfl | rfl | rfl | ⟨rfl, -⟩
      · exact hfi (by simp [isFlowIndicatorProp])
      · exact hfi (by simp [isFlowIndicatorProp])
      · exact hfi (by simp [isFlowIndicatorProp])
      · exact hnc rfl
    | colonSafe _ next _ _ hsafe =>
      simp only [LitStop] at hl
      rcases hl with h | h | h | ⟨-, hcf⟩
      · simp at h
      · simp at h
      · simp at h
      · obtain ⟨hw, hb⟩ := nsChar_facts (plainSafe_nsChar hsafe)
        have hfi := plainSafe_flow hc hsafe
        simp only [ColonFollow] at hcf
        rcases hcf with h | h | h | h | h
        · exact hw (Or.inl h)
        · exact hw (Or.inr h)
        · exact hb (Or.inl h)
        · exact hb (Or.inr h)
        · exact hfi h
  cases hs with
  | entry he =>
    cases he with
    | mk => exact key (skipSep_ws.gstar_sswhite ‹GStar SSWhite m _›) ‹SNsPlainChar c _ _›
    | hash =>
      cases ‹GLit '#' m z›
      cases hopt with
      | none => simp [LitStop] at hl
      | some =>
        rcases sep_shape ‹SSeparate n c _ _› with heq | hh
        · subst heq; simp [LitStop] at hl
        · simp [SepHead] at hh; simp at hcol; omega
  | line hw hb hl' hp hch =>
    exact key ((skipSep_ws.gstar_sswhite hw).trans ((skipSep_ws.sbbreak hb).trans
      ((skipSep_ws.gstar_slEmpty hl').trans (skipSep_ws.flowLinePrefix hp)))) hch

/-- Span determinism of a plain scalar under the flow follow-set. -/
lemma plain_det {n : Nat} {c : YamlContext} (hc : FlowCtx c) {a m₁ m₂ : SurfPos}
    (h₁ : SNsPlain n c a m₁) (h₂ : SNsPlain n c a m₂) (f₁ : FStop n c m₁) (f₂ : FStop n c m₂) :
    m₁ = m₂ := by
  have c₁ := plain_col h₁
  have c₂ := plain_col h₂
  obtain ⟨a₁, hf₁, hs₁⟩ := plain_steps h₁
  obtain ⟨a₂, hf₂, hs₂⟩ := plain_steps h₂
  cases first_det hf₁ hf₂
  exact star_det (S := PStep n c) (fun _ _ _ h h' => pstep_det h h') hs₁ (fun _ hs => pstep_fstop hc c₁ hs f₁) hs₂
    (fun _ hs => pstep_fstop hc c₂ hs f₂)

/-! ## Follow-sets for entries and nodes -/

lemma sepInLine_shape' {a m : SurfPos} (h : SSeparateInLine a m) :
    (a = m ∧ a.col = 0) ∨ SepHead a := by
  cases h with
  | whites =>
    cases ‹GPlus SSWhite _ _› with
    | mk => exact Or.inr (sswhite_head ‹SSWhite _ _›)
  | startOfLine => exact Or.inl ⟨rfl, rfl⟩

lemma sslComments_shape' {a m : SurfPos} (h : SSLComments a m) :
    (a = m ∧ a.col = 0) ∨ SepHead a := by
  cases h with
  | withComment => exact Or.inr (ssbComment_head ‹SSBComment _ _›)
  | startOfLine =>
    cases ‹GStar SLComment _ _› with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons => exact Or.inr (slComment_head ‹SLComment _ _›)

lemma sepLines_shape' {n : Nat} {a m : SurfPos} (h : SSeparateLines n a m) :
    (a = m ∧ a.col = 0) ∨ SepHead a := by
  cases h with
  | inline => exact sepInLine_shape' ‹SSeparateInLine _ _›
  | commented =>
    rcases sslComments_shape' ‹SSLComments a _› with ⟨rfl, hcol⟩ | hh
    · rcases flowLinePrefix_shape ‹SFlowLinePrefix n _ _› with rfl | hh
      · exact Or.inl ⟨rfl, hcol⟩
      · exact Or.inr hh
    · exact Or.inr hh

/-- A separator is zero-width only at column 0; otherwise it begins with a `SepHead`. -/
lemma sep_shape' {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SSeparate n c a m) :
    (a = m ∧ a.col = 0) ∨ SepHead a := by
  cases c <;> simp only [SSeparate] at h
  all_goals first | exact sepLines_shape' h | exact sepInLine_shape' h

/-- What follows an entry (after an optional separator): `,` `]` `}`. -/
def EStop (t : SurfPos) : Prop :=
  match t.chars with
  | [] => False
  | l :: _ => l = ',' ∨ l = ']' ∨ l = '}'

def EFollow (n : Nat) (c : YamlContext) (m : SurfPos) : Prop :=
  ∃ t, GOpt (SSeparate n c) m t ∧ EStop t

lemma estop_litStop {t : SurfPos} (h : EStop t) : LitStop t := by
  obtain ⟨chars, col⟩ := t
  cases chars with
  | nil => simp [EStop] at h
  | cons l rest =>
    simp only [EStop] at h
    simp only [LitStop]
    rcases h with rfl | rfl | rfl <;> simp

lemma efollow_fstop {n : Nat} {c : YamlContext} {m : SurfPos} (h : EFollow n c m) : FStop n c m := by
  obtain ⟨t, ho, hl⟩ := h
  exact ⟨t, ho, estop_litStop hl⟩

lemma estop_sepStop {t : SurfPos} (h : EStop t) : SepStop t := litStop_sepStop (estop_litStop h)

lemma litStop_of_lit {ch : Char} {t u : SurfPos} (h : GLit ch t u)
    (hch : ch = ',' ∨ ch = ']' ∨ ch = '}') : EStop t := by
  cases h; simpa [EStop] using hch

lemma sepHead_colonFollow {rest : List Char} {col : Nat} (h : SepHead ⟨rest, col + 1⟩) :
    ColonFollow rest := by
  cases rest with
  | nil => trivial
  | cons d ds =>
    simp only [SepHead] at h
    simp only [ColonFollow]
    rcases h with rfl | rfl | rfl | rfl | ⟨-, h⟩
    all_goals first | (simp at h) | simp

/-- A mandatory separator right after `:` validates the colon. -/
lemma colonFollow_of_sep {n : Nat} {c : YamlContext} {rest : List Char} {col : Nat} {t : SurfPos}
    (h : SSeparate n c ⟨rest, col + 1⟩ t) : ColonFollow rest := by
  rcases sep_shape' h with ⟨-, hc⟩ | hh
  · simp at hc
  · exact sepHead_colonFollow hh

/-- An optional separator then `,` `]` `}` right after `:` validates the colon. -/
lemma colonFollow_of_estop {n : Nat} {c : YamlContext} {rest : List Char} {col : Nat} {t : SurfPos}
    (ho : GOpt (SSeparate n c) ⟨rest, col + 1⟩ t) (he : EStop t) : ColonFollow rest := by
  cases ho with
  | none =>
    cases rest with
    | nil => simp [EStop] at he
    | cons d ds =>
      simp only [EStop] at he
      simp only [ColonFollow]
      rcases he with rfl | rfl | rfl <;> simp [isFlowIndicatorProp]
  | some => exact colonFollow_of_sep ‹SSeparate n c _ _›

/-- The follow-set hypothesis for nodes: equal ends, or both ends legally followed. -/
def Follow (n : Nat) (c : YamlContext) (m₁ m₂ : SurfPos) : Prop :=
  m₁ = m₂ ∨ (FlowCtx c ∧ FStop n c m₁ ∧ FStop n c m₂)

lemma follow_of_efollow {n : Nat} {c : YamlContext} (hc : FlowCtx c) {m₁ m₂ : SurfPos}
    (h₁ : EFollow n c m₁) (h₂ : EFollow n c m₂) : Follow n c m₁ m₂ :=
  Or.inr ⟨hc, efollow_fstop h₁, efollow_fstop h₂⟩

/-- A key followed by an optional separator and a validated `:` has a legal follow. -/
lemma fstop_of_colon {n : Nat} {c : YamlContext} {m t : SurfPos} {rest : List Char} {col : Nat}
    (ho : GOpt (SSeparate n c) m t) (hl : GLit ':' t ⟨rest, col + 1⟩) (hcf : ColonFollow rest) :
    FStop n c m := by
  cases hl
  exact ⟨_, ho, Or.inr (Or.inr (Or.inr ⟨rfl, hcf⟩))⟩

/-! ## Properties: runs of non-blank characters and the two determinism forms -/

/-- Characters that are neither white space nor a line break. -/
def TChar (c : Char) : Prop := ¬ (c = ' ' ∨ c = '\t') ∧ ¬ (c = '\n' ∨ c = '\r')

instance (c : Char) : Decidable (TChar c) := by unfold TChar; infer_instance

lemma uri_tchar {c : Char} (h : isUriCharProp c) : TChar c := by
  refine ⟨?_, ?_⟩ <;> rintro (rfl | rfl) <;> revert h <;> decide

lemma tag_tchar {c : Char} (h : isTagCharProp c) : TChar c := uri_tchar h.1

lemma word_tchar {c : Char} (h : isWordCharProp c) : TChar c := tag_tchar (word_tag h)

lemma gplus_star {P : SurfPos → SurfPos → Prop} {a b : SurfPos} (h : GPlus P a b) : GStar P a b := by
  cases h with
  | mk => exact GStar.cons _ _ _ ‹P a _› ‹GStar P _ b›

lemma glit_run {ch : Char} {a b : SurfPos} (h : GLit ch a b) (ht : TChar ch) :
    GStar (GChar TChar) a b := by
  cases h; exact GStar.cons _ _ _ (GChar.mk _ _ _ ht) (GStar.nil _)

lemma run_tchar {p : Char → Prop} (hp : ∀ c, p c → TChar c) {a b : SurfPos}
    (h : GStar (GChar p) a b) : GStar (GChar TChar) a b :=
  gstar_mono (fun _ _ hc => by cases hc; exact GChar.mk _ _ _ (hp _ ‹p _›)) h

/-- Everything after the leading `!` of a tag is a run of non-blank characters. -/
lemma tag_run_tail {rest : List Char} {col : Nat} {m : SurfPos}
    (h : SCNsTagProperty ⟨'!' :: rest, col⟩ m) : GStar (GChar TChar) ⟨rest, col + 1⟩ m := by
  cases h with
  | verbatim =>
    exact gstar_append (glit_run ‹GLit '<' _ _› (by decide))
      (gstar_append (run_tchar (fun _ => uri_tchar) (gplus_star ‹GPlus (GChar isUriCharProp) _ _›))
        (glit_run ‹GLit '>' _ _› (by decide)))
  | secondary =>
    exact GStar.cons _ _ _ (GChar.mk '!' _ _ (by decide))
      (run_tchar (fun _ => tag_tchar) ‹GStar (GChar isTagCharProp) _ _›)
  | named =>
    exact gstar_append (run_tchar (fun _ => word_tchar) (gplus_star ‹GPlus (GChar isWordCharProp) _ _›))
      (gstar_append (glit_run ‹GLit '!' _ _› (by decide))
        (run_tchar (fun _ => tag_tchar) ‹GStar (GChar isTagCharProp) _ _›))
  | nonSpecific => exact GStar.nil _
  | primary => exact run_tchar (fun _ => tag_tchar) (gplus_star ‹GPlus (GChar isTagCharProp) _ _›)

lemma gchar_run_col {p : Char → Prop} {a b : SurfPos} (h : GStar (GChar p) a b) : a.col ≤ b.col := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons => rename_i hc _ ih; cases hc; simp at ih ⊢; omega

lemma gchar_run_len {p : Char → Prop} {a b : SurfPos} (h : GStar (GChar p) a b) :
    b.chars.length ≤ a.chars.length := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons => rename_i hc _ ih; cases hc; simp at ih ⊢; omega

lemma gchar_run_eq {p : Char → Prop} {a b : SurfPos} (h : GStar (GChar p) a b)
    (hl : a.chars.length ≤ b.chars.length) : a = b := by
  cases h with
  | nil => rfl
  | cons =>
    rename_i hc hr
    have := gchar_run_len hr
    cases hc; simp at this hl; omega

/-- Two character runs from one start: one of them extends the other. -/
lemma runs_prefix {p : Char → Prop} {a b₁ b₂ : SurfPos} (h₁ : GStar (GChar p) a b₁)
    (h₂ : GStar (GChar p) a b₂) : GStar (GChar p) b₁ b₂ ∨ GStar (GChar p) b₂ b₁ := by
  induction h₁ generalizing b₂ with
  | nil => exact Or.inl h₂
  | cons =>
    rename_i hc hr ih
    cases h₂ with
    | nil => exact Or.inr (GStar.cons _ _ _ hc hr)
    | cons =>
      rename_i hc' hr'
      cases gchar_det hc hc'
      exact ih hr'

lemma tag_col {a m : SurfPos} (h : SCNsTagProperty a m) : a.col + 1 ≤ m.col := by
  obtain ⟨rest, col, rfl⟩ := tag_head h
  exact gchar_run_col (tag_run_tail h)

lemma tag_len {a m : SurfPos} (h : SCNsTagProperty a m) : m.chars.length < a.chars.length := by
  obtain ⟨rest, col, rfl⟩ := tag_head h
  have := gchar_run_len (tag_run_tail h)
  simp at this ⊢; omega

lemma anchor_head {a m : SurfPos} (h : SCNsAnchorProperty a m) : ∃ rest col, a = ⟨'&' :: rest, col⟩ := by
  cases h; exact ⟨_, _, rfl⟩

lemma alias_head {a m : SurfPos} (h : SCNsAliasNode a m) : ∃ rest col, a = ⟨'*' :: rest, col⟩ := by
  cases h; exact ⟨_, _, rfl⟩

lemma anchor_len {a m : SurfPos} (h : SCNsAnchorProperty a m) : m.chars.length < a.chars.length := by
  cases h with
  | mk =>
    have := gchar_run_len (gplus_star ‹GPlus (GChar isNsAnchorChar) _ _›)
    simp at this ⊢; omega

/-- A tag cannot run past a position where a separator starts. -/
lemma tag_extend {a s₁ m : SurfPos} (h₁ : SCNsTagProperty a s₁) (hs : SepHead s₁)
    (h₂ : SCNsTagProperty a m) (hl : m.chars.length ≤ s₁.chars.length) : m = s₁ := by
  obtain ⟨rest, col, rfl⟩ := tag_head h₁
  have r₁ := tag_run_tail h₁
  have r₂ := tag_run_tail h₂
  have hcol := gchar_run_col r₁
  rcases runs_prefix r₁ r₂ with h | h
  · cases h with
    | nil => rfl
    | cons =>
      rename_i hc _
      cases hc with
      | mk d ds col' hd =>
        simp only [SepHead] at hs
        simp at hcol
        rcases hs with h | h | h | h | ⟨-, h⟩
        · exact absurd (Or.inl h) hd.1
        · exact absurd (Or.inr h) hd.1
        · exact absurd (Or.inl h) hd.2
        · exact absurd (Or.inr h) hd.2
        · omega
  · exact gchar_run_eq h hl


/-! ## Spans of the flow fragment are suffixes -/

lemma tprops_suffix {n : Nat} {c : YamlContext} {a b : SurfPos} {ev : List Event}
    (h : TCNsProperties n c a b ev) : b.chars <:+ a.chars := by
  cases h with
  | tagFirst _ _ _ _ _ ht ho =>
    cases ho with
    | none => exact scNsTagProperty_suffix ht.1
    | some =>
      cases ‹TSeq (Lift (SSeparate n c)) TCNsAnchorProperty _ _ _› with
      | mk _ _ _ _ _ hs ha =>
        exact (scNsAnchorProperty_suffix ha.1).trans ((sSeparate_suffix hs.1).trans
          (scNsTagProperty_suffix ht.1))
  | anchorFirst _ _ _ _ _ ha ho =>
    cases ho with
    | none => exact scNsAnchorProperty_suffix ha.1
    | some =>
      cases ‹TSeq (Lift (SSeparate n c)) TCNsTagProperty _ _ _› with
      | mk _ _ _ _ _ hs ht =>
        exact (scNsTagProperty_suffix ht.1).trans ((sSeparate_suffix hs.1).trans
          (scNsAnchorProperty_suffix ha.1))

mutual

lemma tFlowNode_suffix {n : Nat} {c : YamlContext} {a b : SurfPos} {ev : List Event}
    (h : TFlowNode n c a b ev) : b.chars <:+ a.chars := by
  match h with
  | .alias _ _ _ _ _ h0 =>
    exact (scNsAliasNode_suffix h0.1)
  | .content _ _ _ _ _ h0 =>
    exact (tFlowContent_suffix h0)
  | .propsContent _ _ _ _ _ _ _ _ h0 h1 h2 =>
    exact (((tFlowContent_suffix h2).trans (sSeparate_suffix h1)).trans (tprops_suffix h0))
  | .propsEmpty _ _ _ _ _ h0 =>
    exact (tprops_suffix h0)

lemma tFlowContent_suffix {n : Nat} {c : YamlContext} {a b : SurfPos} {ev : List Event}
    (h : TFlowContent n c a b ev) : b.chars <:+ a.chars := by
  match h with
  | .plain _ _ _ _ h0 =>
    exact (snsPlain_suffix h0)
  | .flowSeq _ _ _ _ _ h0 =>
    exact (tFlowSequence_suffix h0)
  | .flowMap _ _ _ _ _ h0 =>
    exact (tFlowMapping_suffix h0)
  | .singleQ _ _ _ _ h0 =>
    exact (scSingleQuoted_suffix h0)
  | .doubleQ _ _ _ _ h0 =>
    exact (scDoubleQuoted_suffix h0)

lemma tCFlowJsonContent_suffix {n : Nat} {c : YamlContext} {a b : SurfPos} {ev : List Event}
    (h : TCFlowJsonContent n c a b ev) : b.chars <:+ a.chars := by
  match h with
  | .flowSeq _ _ _ _ _ h0 =>
    exact (tFlowSequence_suffix h0)
  | .flowMap _ _ _ _ _ h0 =>
    exact (tFlowMapping_suffix h0)
  | .singleQ _ _ _ _ h0 =>
    exact (scSingleQuoted_suffix h0)
  | .doubleQ _ _ _ _ h0 =>
    exact (scDoubleQuoted_suffix h0)

lemma tCFlowJsonNode_suffix {n : Nat} {c : YamlContext} {a b : SurfPos} {ev : List Event}
    (h : TCFlowJsonNode n c a b ev) : b.chars <:+ a.chars := by
  match h with
  | .content _ _ _ _ _ h0 =>
    exact (tCFlowJsonContent_suffix h0)
  | .propsContent _ _ _ _ _ _ _ _ h0 h1 h2 =>
    exact (((tCFlowJsonContent_suffix h2).trans (sSeparate_suffix h1)).trans (tprops_suffix h0))

lemma tFlowSequence_suffix {n : Nat} {c : YamlContext} {a b : SurfPos} {ev : List Event}
    (h : TFlowSequence n c a b ev) : b.chars <:+ a.chars := by
  match h with
  | .empty _ _ _ _ _ _ h0 h1 h2 =>
    exact (((glit_suffix h2).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h1)).trans (glit_suffix h0))
  | .nonempty _ _ _ _ _ _ _ _ h0 h1 h2 h3 =>
    exact ((((glit_suffix h3).trans (tFlowSeqEntries_suffix h2)).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h1)).trans (glit_suffix h0))

lemma tFlowSeqEntries_suffix {n : Nat} {c : YamlContext} {a b : SurfPos} {ev : List Event}
    (h : TFlowSeqEntries n c a b ev) : b.chars <:+ a.chars := by
  match h with
  | .single _ _ _ _ _ _ h0 h1 =>
    exact ((gopt_suffix (fun _ _ => sSeparate_suffix) h1).trans (tFlowSeqEntry_suffix h0))
  | .consMore _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 =>
    exact (((((tFlowSeqEntries_suffix h4).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h3)).trans (glit_suffix h2)).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h1)).trans (tFlowSeqEntry_suffix h0))
  | .consEnd _ _ _ _ _ _ _ _ h0 h1 h2 h3 =>
    exact ((((gopt_suffix (fun _ _ => sSeparate_suffix) h3).trans (glit_suffix h2)).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h1)).trans (tFlowSeqEntry_suffix h0))

lemma tFlowSeqEntry_suffix {n : Nat} {c : YamlContext} {a b : SurfPos} {ev : List Event}
    (h : TFlowSeqEntry n c a b ev) : b.chars <:+ a.chars := by
  match h with
  | .node _ _ _ _ _ h0 =>
    exact (tFlowNode_suffix h0)
  | .pairValue _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 =>
    exact (((((tFlowNode_suffix h4).trans (sSeparate_suffix h3)).trans (glit_suffix h2)).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h1)).trans (tFlowNode_suffix h0))
  | .pairEmpty _ _ _ _ _ _ _ h0 h1 h2 =>
    exact (((glit_suffix h2).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h1)).trans (tFlowNode_suffix h0))
  | .pairJsonAdjacentValue _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 =>
    exact (((((tFlowNode_suffix h4).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h3)).trans (glit_suffix h2)).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h1)).trans (tCFlowJsonNode_suffix h0))
  | .explicitPairJsonAdjacentValue _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 =>
    exact (((((((tFlowNode_suffix h6).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h5)).trans (glit_suffix h4)).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h3)).trans (tCFlowJsonNode_suffix h2)).trans (sSeparate_suffix h1)).trans (glit_suffix h0))
  | .explicitPairValue _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 =>
    exact (((((((tFlowNode_suffix h6).trans (sSeparate_suffix h5)).trans (glit_suffix h4)).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h3)).trans (tFlowNode_suffix h2)).trans (sSeparate_suffix h1)).trans (glit_suffix h0))
  | .explicitPairEmpty _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 =>
    exact (((((glit_suffix h4).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h3)).trans (tFlowNode_suffix h2)).trans (sSeparate_suffix h1)).trans (glit_suffix h0))
  | .explicitPairKeyOnly _ _ _ _ _ _ _ h0 h1 h2 =>
    exact (((tFlowNode_suffix h2).trans (sSeparate_suffix h1)).trans (glit_suffix h0))
  | .explicitPairEmptyNodes _ _ _ _ _ h0 h1 =>
    exact ((sSeparate_suffix h1).trans (glit_suffix h0))
  | .emptyKeyValue _ _ _ _ _ _ _ h0 h1 h2 =>
    exact (((tFlowNode_suffix h2).trans (sSeparate_suffix h1)).trans (glit_suffix h0))
  | .emptyKeyEmpty _ _ _ _ h0 =>
    exact (glit_suffix h0)
  | .explicitEmptyKeyValue _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 =>
    exact (((((tFlowNode_suffix h4).trans (sSeparate_suffix h3)).trans (glit_suffix h2)).trans (sSeparate_suffix h1)).trans (glit_suffix h0))
  | .explicitEmptyKeyEmpty _ _ _ _ _ _ h0 h1 h2 =>
    exact (((glit_suffix h2).trans (sSeparate_suffix h1)).trans (glit_suffix h0))

lemma tFlowMapping_suffix {n : Nat} {c : YamlContext} {a b : SurfPos} {ev : List Event}
    (h : TFlowMapping n c a b ev) : b.chars <:+ a.chars := by
  match h with
  | .empty _ _ _ _ _ _ h0 h1 h2 =>
    exact (((glit_suffix h2).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h1)).trans (glit_suffix h0))
  | .nonempty _ _ _ _ _ _ _ _ h0 h1 h2 h3 =>
    exact ((((glit_suffix h3).trans (tFlowMapEntries_suffix h2)).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h1)).trans (glit_suffix h0))

lemma tFlowMapEntries_suffix {n : Nat} {c : YamlContext} {a b : SurfPos} {ev : List Event}
    (h : TFlowMapEntries n c a b ev) : b.chars <:+ a.chars := by
  match h with
  | .single _ _ _ _ _ _ h0 h1 =>
    exact ((gopt_suffix (fun _ _ => sSeparate_suffix) h1).trans (tFlowMapEntry_suffix h0))
  | .consMore _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 =>
    exact (((((tFlowMapEntries_suffix h4).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h3)).trans (glit_suffix h2)).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h1)).trans (tFlowMapEntry_suffix h0))
  | .consEnd _ _ _ _ _ _ _ _ h0 h1 h2 h3 =>
    exact ((((gopt_suffix (fun _ _ => sSeparate_suffix) h3).trans (glit_suffix h2)).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h1)).trans (tFlowMapEntry_suffix h0))

lemma tFlowMapEntry_suffix {n : Nat} {c : YamlContext} {a b : SurfPos} {ev : List Event}
    (h : TFlowMapEntry n c a b ev) : b.chars <:+ a.chars := by
  match h with
  | .explicitValue _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 =>
    exact (((((((tFlowNode_suffix h6).trans (sSeparate_suffix h5)).trans (glit_suffix h4)).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h3)).trans (tFlowNode_suffix h2)).trans (sSeparate_suffix h1)).trans (glit_suffix h0))
  | .explicitEmpty _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 =>
    exact (((((glit_suffix h4).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h3)).trans (tFlowNode_suffix h2)).trans (sSeparate_suffix h1)).trans (glit_suffix h0))
  | .explicitKeyOnly _ _ _ _ _ _ _ h0 h1 h2 =>
    exact (((tFlowNode_suffix h2).trans (sSeparate_suffix h1)).trans (glit_suffix h0))
  | .implicitValue _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 =>
    exact (((((tFlowNode_suffix h4).trans (sSeparate_suffix h3)).trans (glit_suffix h2)).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h1)).trans (tFlowNode_suffix h0))
  | .implicitEmpty _ _ _ _ _ _ _ h0 h1 h2 =>
    exact (((glit_suffix h2).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h1)).trans (tFlowNode_suffix h0))
  | .jsonKeyAdjacentValue _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 =>
    exact (((((tFlowNode_suffix h4).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h3)).trans (glit_suffix h2)).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h1)).trans (tCFlowJsonNode_suffix h0))
  | .explicitJsonKeyAdjacentValue _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 =>
    exact (((((((tFlowNode_suffix h6).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h5)).trans (glit_suffix h4)).trans (gopt_suffix (fun _ _ => sSeparate_suffix) h3)).trans (tCFlowJsonNode_suffix h2)).trans (sSeparate_suffix h1)).trans (glit_suffix h0))
  | .bareKey _ _ _ _ _ h0 =>
    exact (tFlowNode_suffix h0)
  | .emptyKeyValue _ _ _ _ _ _ _ h0 h1 h2 =>
    exact (((tFlowNode_suffix h2).trans (sSeparate_suffix h1)).trans (glit_suffix h0))
  | .emptyKeyEmpty _ _ _ _ h0 =>
    exact (glit_suffix h0)
  | .explicitEmptyNodes _ _ _ _ _ h0 h1 =>
    exact ((sSeparate_suffix h1).trans (glit_suffix h0))
  | .explicitEmptyKeyValue _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 =>
    exact (((((tFlowNode_suffix h4).trans (sSeparate_suffix h3)).trans (glit_suffix h2)).trans (sSeparate_suffix h1)).trans (glit_suffix h0))
  | .explicitEmptyKeyEmpty _ _ _ _ _ _ h0 h1 h2 =>
    exact (((glit_suffix h2).trans (sSeparate_suffix h1)).trans (glit_suffix h0))
end


/-! ## Properties: determinism under a property-free follow -/

/-- The next character does not start another property. -/
def NotProp (t : SurfPos) : Prop :=
  match t.chars with
  | [] => True
  | d :: _ => d ≠ '&' ∧ d ≠ '!'

/-- What must hold after a `c-ns-properties` for its span to be pinned. -/
def PStop (n : Nat) (c : YamlContext) (m : SurfPos) : Prop :=
  TagStop m ∧ ∃ t, GOpt (SSeparate n c) m t ∧ SepStop t ∧ NotProp t

lemma litStop_notProp {t : SurfPos} (h : LitStop t) : NotProp t := by
  obtain ⟨chars, col⟩ := t
  cases chars with
  | nil => trivial
  | cons l rest =>
    simp only [LitStop] at h
    rcases h with rfl | rfl | rfl | ⟨rfl, -⟩ <;> simp [NotProp]

lemma pstop_of_fstop {n : Nat} {c : YamlContext} {m : SurfPos} (h : FStop n c m) : PStop n c m := by
  obtain ⟨t, ho, hl⟩ := h
  exact ⟨fstop_tagStop ⟨t, ho, hl⟩, t, ho, litStop_sepStop hl, litStop_notProp hl⟩

lemma sep_sepHead {n : Nat} {c : YamlContext} {m t : SurfPos} (hs : SSeparate n c m t)
    (hcol : 1 ≤ m.col) : SepHead m := by
  rcases sep_shape' hs with ⟨-, h0⟩ | hh
  · omega
  · exact hh

lemma pstop_of_sep {n : Nat} {c : YamlContext} {m t : SurfPos} (hs : SSeparate n c m t)
    (hcol : 1 ≤ m.col) (hst : SepStop t) (hnp : NotProp t) : PStop n c m :=
  ⟨sepHead_tagStop (sep_sepHead hs hcol), t, GOpt.some _ _ hs, hst, hnp⟩

lemma anchor_col {a m : SurfPos} (h : SCNsAnchorProperty a m) : a.col + 1 ≤ m.col := by
  cases h with
  | mk => exact gchar_run_col (gplus_star ‹GPlus (GChar isNsAnchorChar) _ _›)

lemma anchor_sepStop {a m : SurfPos} (h : SCNsAnchorProperty a m) : SepStop a := by
  obtain ⟨rest, col, rfl⟩ := anchor_head h; simp [SepStop]

lemma tag_sepStop {a m : SurfPos} (h : SCNsTagProperty a m) : SepStop a := by
  obtain ⟨rest, col, rfl⟩ := tag_head h; simp [SepStop]

lemma anchor_notProp {a m : SurfPos} (h : SCNsAnchorProperty a m) (hn : NotProp a) : False := by
  obtain ⟨rest, col, rfl⟩ := anchor_head h; simp [NotProp] at hn

lemma tag_notProp {a m : SurfPos} (h : SCNsTagProperty a m) (hn : NotProp a) : False := by
  obtain ⟨rest, col, rfl⟩ := tag_head h; simp [NotProp] at hn

/-- The optional `s-separate c-ns-anchor-property` tail after a tag. -/
lemma tagOpt_end {n : Nat} {c : YamlContext} {s u m : SurfPos} {e : List Event}
    (ht : SCNsTagProperty s u) (ho : TOpt (TSeq (Lift (SSeparate n c)) TCNsAnchorProperty) u m e)
    (pm : PStop n c m) :
    TagStop u ∧ ((u = m ∧ e = []) ∨
      ∃ v, SSeparate n c u v ∧ SCNsAnchorProperty v m ∧ e = anchorEvents (span v m) ∧
        v = skipSep u ∧ SepHead u) := by
  cases ho with
  | none => exact ⟨pm.1, Or.inl ⟨rfl, rfl⟩⟩
  | some =>
    cases ‹TSeq (Lift (SSeparate n c)) TCNsAnchorProperty u m e› with
    | mk _ v _ _ _ hs ha =>
      have hh := sep_sepHead hs.1 (by have := tag_col ht; omega)
      refine ⟨sepHead_tagStop hh, Or.inr ⟨v, hs.1, ha.1, ?_, sep_det hs.1 (anchor_sepStop ha.1), hh⟩⟩
      rw [ha.2, hs.2]; rfl

/-- The optional `s-separate c-ns-tag-property` tail after an anchor. -/
lemma anchorOpt_end {n : Nat} {c : YamlContext} {s u m : SurfPos} {e : List Event}
    (ha : SCNsAnchorProperty s u) (ho : TOpt (TSeq (Lift (SSeparate n c)) TCNsTagProperty) u m e) :
    (u = m ∧ e = []) ∨
      ∃ v, SSeparate n c u v ∧ SCNsTagProperty v m ∧ e = tagEvents (span v m) ∧
        v = skipSep u ∧ SepHead u := by
  cases ho with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some =>
    cases ‹TSeq (Lift (SSeparate n c)) TCNsTagProperty u m e› with
    | mk _ v _ _ _ hs ht =>
      have hh := sep_sepHead hs.1 (by have := anchor_col ha; omega)
      refine Or.inr ⟨v, hs.1, ht.1, ?_, sep_det hs.1 (tag_sepStop ht.1), hh⟩
      rw [ht.2, hs.2]; rfl

lemma props_col {n : Nat} {c : YamlContext} {s m : SurfPos} {ev : List Event}
    (h : TCNsProperties n c s m ev) : 1 ≤ m.col := by
  cases h with
  | tagFirst _ _ _ _ _ ht ho =>
    cases ho with
    | none => have := tag_col ht.1; omega
    | some =>
      cases ‹TSeq (Lift (SSeparate n c)) TCNsAnchorProperty _ _ _› with
      | mk _ _ _ _ _ _ ha => have := anchor_col ha.1; omega
  | anchorFirst _ _ _ _ _ ha ho =>
    cases ho with
    | none => have := anchor_col ha.1; omega
    | some =>
      cases ‹TSeq (Lift (SSeparate n c)) TCNsTagProperty _ _ _› with
      | mk _ _ _ _ _ _ ht => have := tag_col ht.1; omega

/-- Span and trace determinism of `c-ns-properties` under a property-free follow. -/
lemma props_det {n : Nat} {c : YamlContext} {s m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}
    (h₁ : TCNsProperties n c s m₁ ev₁) (h₂ : TCNsProperties n c s m₂ ev₂)
    (p₁ : PStop n c m₁) (p₂ : PStop n c m₂) : m₁ = m₂ ∧ ev₁ = ev₂ := by
  cases h₁ with
  | tagFirst _ u₁ _ _ e₁ ht₁ ho₁ =>
    cases h₂ with
    | tagFirst _ u₂ _ _ e₂ ht₂ ho₂ =>
      obtain ⟨ts₁, r₁⟩ := tagOpt_end ht₁.1 ho₁ p₁
      obtain ⟨ts₂, r₂⟩ := tagOpt_end ht₂.1 ho₂ p₂
      cases tag_det ht₁.1 ht₂.1 ts₁ ts₂
      rcases r₁ with ⟨rfl, rfl⟩ | ⟨v₁, hs₁, ha₁, rfl, rfl, -⟩
      · rcases r₂ with ⟨rfl, rfl⟩ | ⟨v₂, hs₂, ha₂, rfl, rfl, -⟩
        · exact ⟨rfl, by rw [ht₁.2, ht₂.2]⟩
        · exfalso
          obtain ⟨-, t, ho, hst, hnp⟩ := p₁
          rw [gopt_sep_det ho hst] at hnp
          exact anchor_notProp ha₂ hnp
      · rcases r₂ with ⟨rfl, rfl⟩ | ⟨v₂, hs₂, ha₂, rfl, rfl, -⟩
        · exfalso
          obtain ⟨-, t, ho, hst, hnp⟩ := p₂
          rw [gopt_sep_det ho hst] at hnp
          exact anchor_notProp ha₁ hnp
        · cases anchor_det ha₁ ha₂
          exact ⟨rfl, by rw [ht₁.2, ht₂.2]⟩
    | anchorFirst _ _ _ _ _ ha₂ _ =>
      exfalso
      obtain ⟨r₁, c₁, e₁⟩ := tag_head ht₁.1
      obtain ⟨r₂, c₂, e₂⟩ := anchor_head ha₂.1
      rw [e₁] at e₂; cases e₂
  | anchorFirst _ u₁ _ _ e₁ ha₁ ho₁ =>
    cases h₂ with
    | tagFirst _ _ _ _ _ ht₂ _ =>
      exfalso
      obtain ⟨r₁, c₁, e₁⟩ := anchor_head ha₁.1
      obtain ⟨r₂, c₂, e₂⟩ := tag_head ht₂.1
      rw [e₁] at e₂; cases e₂
    | anchorFirst _ u₂ _ _ e₂ ha₂ ho₂ =>
      cases anchor_det ha₁.1 ha₂.1
      rcases anchorOpt_end ha₁.1 ho₁ with ⟨rfl, rfl⟩ | ⟨v₁, hs₁, ht₁, rfl, rfl, -⟩
      · rcases anchorOpt_end ha₂.1 ho₂ with ⟨rfl, rfl⟩ | ⟨v₂, hs₂, ht₂, rfl, rfl, -⟩
        · exact ⟨rfl, by rw [ha₁.2, ha₂.2]⟩
        · exfalso
          obtain ⟨-, t, ho, hst, hnp⟩ := p₁
          rw [gopt_sep_det ho hst] at hnp
          exact tag_notProp ht₂ hnp
      · rcases anchorOpt_end ha₂.1 ho₂ with ⟨rfl, rfl⟩ | ⟨v₂, hs₂, ht₂, rfl, rfl, -⟩
        · exfalso
          obtain ⟨-, t, ho, hst, hnp⟩ := p₂
          rw [gopt_sep_det ho hst] at hnp
          exact tag_notProp ht₁ hnp
        · cases tag_det ht₁ ht₂ p₁.1 p₂.1
          exact ⟨rfl, by rw [ha₁.2, ha₂.2]⟩

/-- A property run cannot be followed by a separator and a non-property while another
property run from the same start reaches strictly past that non-property. -/
lemma props_ext {n : Nat} {c : YamlContext} {s s₁ s₂ M : SurfPos} {ev₁ ev₂ : List Event}
    (h₁ : TCNsProperties n c s s₁ ev₁) (hs : SSeparate n c s₁ s₂) (hst : SepStop s₂)
    (hnp : NotProp s₂) (h₂ : TCNsProperties n c s M ev₂) (hl : M.chars.length < s₂.chars.length) :
    False := by
  have p₁ : PStop n c s₁ := pstop_of_sep hs (props_col h₁) hst hnp
  have l₁ : s₂.chars.length ≤ s₁.chars.length := (sSeparate_suffix hs).length_le
  have hs₂ : s₂ = skipSep s₁ := sep_det hs hst
  cases h₁ with
  | tagFirst _ u₁ _ _ e₁ ht₁ ho₁ =>
    obtain ⟨ts₁, r₁⟩ := tagOpt_end ht₁.1 ho₁ p₁
    have hu₁ : SepHead u₁ ∧ s₁.chars.length ≤ u₁.chars.length := by
      rcases r₁ with ⟨rfl, -⟩ | ⟨v₁, hs₁, ha₁, -, -, hh⟩
      · exact ⟨sep_sepHead hs (props_col (TCNsProperties.tagFirst _ _ _ _ _ ht₁ ho₁)), Nat.le_refl _⟩
      · exact ⟨hh, Nat.le_trans (scNsAnchorProperty_suffix ha₁).length_le (sSeparate_suffix hs₁).length_le⟩
    cases h₂ with
    | tagFirst _ u₂ _ _ e₂ ht₂ ho₂ =>
      cases ho₂ with
      | none =>
        have := tag_extend ht₁.1 hu₁.1 ht₂.1 (by omega)
        subst this; omega
      | some =>
        cases ‹TSeq (Lift (SSeparate n c)) TCNsAnchorProperty u₂ M _› with
        | mk _ v₂ _ _ _ hs₂' ha₂ =>
          have hh₂ := sep_sepHead hs₂'.1 (by have := tag_col ht₂.1; omega)
          cases tag_det ht₁.1 ht₂.1 ts₁ (sepHead_tagStop hh₂)
          have hv₂ := sep_det hs₂'.1 (anchor_sepStop ha₂.1)
          rcases r₁ with ⟨rfl, -⟩ | ⟨v₁, hs₁, ha₁, -, hv₁, -⟩
          · rw [← hs₂] at hv₂; subst hv₂; exact anchor_notProp ha₂.1 hnp
          · rw [← hv₁] at hv₂; subst hv₂
            cases anchor_det ha₁ ha₂.1
            omega
    | anchorFirst _ _ _ _ _ ha₂ _ =>
      obtain ⟨r₁, c₁, e₁⟩ := tag_head ht₁.1
      obtain ⟨r₂, c₂, e₂⟩ := anchor_head ha₂.1
      rw [e₁] at e₂; cases e₂
  | anchorFirst _ u₁ _ _ e₁ ha₁ ho₁ =>
    cases h₂ with
    | tagFirst _ _ _ _ _ ht₂ _ =>
      obtain ⟨r₁, c₁, e₁⟩ := anchor_head ha₁.1
      obtain ⟨r₂, c₂, e₂⟩ := tag_head ht₂.1
      rw [e₁] at e₂; cases e₂
    | anchorFirst _ u₂ _ _ e₂ ha₂ ho₂ =>
      cases anchor_det ha₁.1 ha₂.1
      rcases anchorOpt_end ha₁.1 ho₁ with ⟨rfl, -⟩ | ⟨v₁, hs₁, ht₁, -, hv₁, -⟩
      · rcases anchorOpt_end ha₂.1 ho₂ with ⟨rfl, -⟩ | ⟨v₂, hs₂', ht₂, -, hv₂, -⟩
        · omega
        · rw [← hs₂] at hv₂; subst hv₂; exact tag_notProp ht₂ hnp
      · rcases anchorOpt_end ha₂.1 ho₂ with ⟨rfl, -⟩ | ⟨v₂, hs₂', ht₂, -, hv₂, -⟩
        · have := Nat.le_trans (scNsTagProperty_suffix ht₁).length_le (sSeparate_suffix hs₁).length_le
          omega
        · rw [← hv₁] at hv₂; subst hv₂
          have hh := sep_sepHead hs (props_col (TCNsProperties.anchorFirst _ _ _ _ _ ha₁ ho₁))
          have := tag_extend ht₁ hh ht₂ (by omega)
          subst this; omega

/-! ## Heads: what a node or content may begin with -/

/-- The first characters of a `ns-flow-content` (plain, flow collection, or quoted). -/
def ContentHead (c : YamlContext) (s : SurfPos) : Prop :=
  match s.chars with
  | [] => False
  | ch :: rest =>
      (isNsPlainSafe c ch ∧ ¬ isIndicatorProp ch) ∨
      ((ch = '-' ∨ ch = ':' ∨ ch = '?') ∧ ∃ nx r, rest = nx :: r ∧ isNsPlainSafe c nx) ∨
      ch = '[' ∨ ch = '{' ∨ ch = '"' ∨ ch = '\''

lemma plain_contentHead {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SNsPlain n c a m) :
    ContentHead c a := by
  obtain ⟨a₁, hf, -⟩ := plain_steps h
  cases hf with
  | nonIndicator ch rest col hs hi => exact Or.inl ⟨hs, hi⟩
  | dashSafe nx rest col hs => exact Or.inr (Or.inl ⟨by simp, nx, rest, rfl, hs⟩)
  | colonSafe nx rest col hs => exact Or.inr (Or.inl ⟨by simp, nx, rest, rfl, hs⟩)
  | questionSafe nx rest col hs => exact Or.inr (Or.inl ⟨by simp, nx, rest, rfl, hs⟩)

lemma sq_contentHead {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SCSingleQuoted n c a m) :
    ContentHead c a := by
  cases h with
  | mk => cases ‹GLit '\'' a _›; simp [ContentHead]

lemma dq_contentHead {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SCDoubleQuoted n c a m) :
    ContentHead c a := by
  cases h with
  | mk => cases ‹GLit '"' a _›; simp [ContentHead]

lemma seq_contentHead {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TFlowSequence n c a m ev) : ContentHead c a := by
  cases h with
  | empty _ _ _ _ _ _ hl _ _ => cases hl; simp [ContentHead]
  | nonempty _ _ _ _ _ _ _ _ hl _ _ _ => cases hl; simp [ContentHead]

lemma map_contentHead {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TFlowMapping n c a m ev) : ContentHead c a := by
  cases h with
  | empty _ _ _ _ _ _ hl _ _ => cases hl; simp [ContentHead]
  | nonempty _ _ _ _ _ _ _ _ hl _ _ _ => cases hl; simp [ContentHead]

lemma content_head {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TFlowContent n c a m ev) : ContentHead c a := by
  cases h with
  | plain _ _ _ _ hp => exact plain_contentHead hp
  | flowSeq _ _ _ _ _ hx => exact seq_contentHead hx
  | flowMap _ _ _ _ _ hx => exact map_contentHead hx
  | singleQ _ _ _ _ hx => exact sq_contentHead hx
  | doubleQ _ _ _ _ hx => exact dq_contentHead hx

lemma jsonContent_head {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TCFlowJsonContent n c a m ev) : ContentHead c a := by
  cases h with
  | flowSeq _ _ _ _ _ hx => exact seq_contentHead hx
  | flowMap _ _ _ _ _ hx => exact map_contentHead hx
  | singleQ _ _ _ _ hx => exact sq_contentHead hx
  | doubleQ _ _ _ _ hx => exact dq_contentHead hx

/-- Everything a content head excludes, in one place. -/
lemma contentHead_facts {c : YamlContext} {a : SurfPos} (h : ContentHead c a) :
    ∃ ch rest col, a = ⟨ch :: rest, col⟩ ∧ ch ≠ '*' ∧ ch ≠ '&' ∧ ch ≠ '!' ∧ ch ≠ ',' ∧ ch ≠ ']' ∧
      ch ≠ '}' ∧ ¬ (ch = ' ' ∨ ch = '\t') ∧ ¬ (ch = '\n' ∨ ch = '\r') ∧ ch ≠ '#' := by
  obtain ⟨chars, col⟩ := a
  cases chars with
  | nil => simp [ContentHead] at h
  | cons ch rest =>
    refine ⟨ch, rest, col, rfl, ?_⟩
    simp only [ContentHead] at h
    rcases h with ⟨hs, hi⟩ | ⟨h3, -⟩ | rfl | rfl | rfl | rfl
    · obtain ⟨hw, hb⟩ := nsChar_facts (plainSafe_nsChar hs)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hw, hb, ?_⟩ <;> rintro rfl <;> exact hi (by decide)
    · rcases h3 with rfl | rfl | rfl <;> simp
    all_goals simp

lemma contentHead_sepStop {c : YamlContext} {a : SurfPos} (h : ContentHead c a) : SepStop a := by
  obtain ⟨ch, rest, col, rfl, -, -, -, -, -, -, hw, hb, hh⟩ := contentHead_facts h
  exact ⟨hw, hb, hh⟩

lemma contentHead_notProp {c : YamlContext} {a : SurfPos} (h : ContentHead c a) : NotProp a := by
  obtain ⟨ch, rest, col, rfl, -, h2, h3, -⟩ := contentHead_facts h
  exact ⟨h2, h3⟩

lemma contentHead_not_estop {c : YamlContext} {a : SurfPos} (h : ContentHead c a) (he : EStop a) :
    False := by
  obtain ⟨ch, rest, col, rfl, -, -, -, h4, h5, h6, -⟩ := contentHead_facts h
  simp only [EStop] at he
  rcases he with h | h | h
  · exact h4 h
  · exact h5 h
  · exact h6 h

lemma contentHead_not_litStop {c : YamlContext} (hc : FlowCtx c) {a : SurfPos} (h : ContentHead c a)
    (hl : LitStop a) : False := by
  obtain ⟨chars, col⟩ := a
  cases chars with
  | nil => simp [LitStop] at hl
  | cons ch rest =>
    simp only [LitStop] at hl
    rcases hl with rfl | rfl | rfl | ⟨rfl, hcf⟩
    · exact contentHead_not_estop h (by simp [EStop])
    · exact contentHead_not_estop h (by simp [EStop])
    · exact contentHead_not_estop h (by simp [EStop])
    · simp only [ContentHead] at h
      rcases h with ⟨-, hi⟩ | ⟨-, nx, r, rfl, hs⟩ | h | h | h | h
      · exact hi (by decide)
      · obtain ⟨hw, hb⟩ := nsChar_facts (plainSafe_nsChar hs)
        have hfi := plainSafe_flow hc hs
        simp only [ColonFollow] at hcf
        rcases hcf with h | h | h | h | h
        · exact hw (Or.inl h)
        · exact hw (Or.inr h)
        · exact hb (Or.inl h)
        · exact hb (Or.inr h)
        · exact hfi h
      all_goals simp at h

lemma props_head {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TCNsProperties n c a m ev) :
    (∃ rest col, a = ⟨'!' :: rest, col⟩) ∨ (∃ rest col, a = ⟨'&' :: rest, col⟩) := by
  cases h with
  | tagFirst _ _ _ _ _ ht _ => exact Or.inl (tag_head ht.1)
  | anchorFirst _ _ _ _ _ ha _ => exact Or.inr (anchor_head ha.1)

lemma props_sepStop {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TCNsProperties n c a m ev) : SepStop a := by
  rcases props_head h with ⟨r, cl, rfl⟩ | ⟨r, cl, rfl⟩ <;> simp [SepStop]

/-- Heads of a flow node: alias, property, or content. -/
lemma node_head {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TFlowNode n c a m ev) :
    (∃ rest col, a = ⟨'*' :: rest, col⟩) ∨ (∃ rest col, a = ⟨'!' :: rest, col⟩) ∨
      (∃ rest col, a = ⟨'&' :: rest, col⟩) ∨ ContentHead c a := by
  cases h with
  | alias _ _ _ _ _ ha => exact Or.inl (alias_head ha.1)
  | content _ _ _ _ _ hc => exact Or.inr (Or.inr (Or.inr (content_head hc)))
  | propsContent _ _ _ _ _ _ _ _ hp _ _ => exact Or.inr ((props_head hp).imp id Or.inl)
  | propsEmpty _ _ _ _ _ hp => exact Or.inr ((props_head hp).imp id Or.inl)

lemma node_sepStop {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TFlowNode n c a m ev) : SepStop a := by
  rcases node_head h with ⟨r, cl, rfl⟩ | ⟨r, cl, rfl⟩ | ⟨r, cl, rfl⟩ | hc
  · simp [SepStop]
  · simp [SepStop]
  · simp [SepStop]
  · exact contentHead_sepStop hc

lemma node_not_estop {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TFlowNode n c a m ev) (he : EStop a) : False := by
  rcases node_head h with ⟨r, cl, rfl⟩ | ⟨r, cl, rfl⟩ | ⟨r, cl, rfl⟩ | hc
  · simp [EStop] at he
  · simp [EStop] at he
  · simp [EStop] at he
  · exact contentHead_not_estop hc he

lemma jsonNode_head {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TCFlowJsonNode n c a m ev) :
    (∃ rest col, a = ⟨'!' :: rest, col⟩) ∨ (∃ rest col, a = ⟨'&' :: rest, col⟩) ∨ ContentHead c a := by
  cases h with
  | content _ _ _ _ _ hc => exact Or.inr (Or.inr (jsonContent_head hc))
  | propsContent _ _ _ _ _ _ _ _ hp _ _ => exact (props_head hp).imp id Or.inl

lemma jsonNode_sepStop {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TCFlowJsonNode n c a m ev) : SepStop a := by
  rcases jsonNode_head h with ⟨r, cl, rfl⟩ | ⟨r, cl, rfl⟩ | hc
  · simp [SepStop]
  · simp [SepStop]
  · exact contentHead_sepStop hc

/-! ## Follow-sets for the induction, and strictness of spans -/

/-- A character that may follow a JSON-like key or any node in flow: `,` `]` `}` `:`. -/
def CStop (t : SurfPos) : Prop :=
  match t.chars with
  | [] => False
  | l :: _ => l = ',' ∨ l = ']' ∨ l = '}' ∨ l = ':'

/-- Optional separator, then a `CStop` character. -/
def NStop (n : Nat) (c : YamlContext) (m : SurfPos) : Prop :=
  ∃ t, GOpt (SSeparate n c) m t ∧ CStop t

/-- The closing bracket of a flow collection. -/
def CloseStop (t : SurfPos) : Prop :=
  match t.chars with
  | [] => False
  | l :: _ => l = ']' ∨ l = '}'

lemma litStop_cstop {t : SurfPos} (h : LitStop t) : CStop t := by
  obtain ⟨chars, col⟩ := t
  cases chars with
  | nil => simp [LitStop] at h
  | cons l rest =>
    simp only [LitStop, CStop] at h ⊢
    rcases h with h | h | h | ⟨h, -⟩ <;> simp [h]

lemma cstop_sepStop {t : SurfPos} (h : CStop t) : SepStop t := by
  obtain ⟨chars, col⟩ := t
  cases chars with
  | nil => simp [CStop] at h
  | cons l rest =>
    simp only [CStop] at h
    rcases h with rfl | rfl | rfl | rfl <;> simp [SepStop]

lemma cstop_notProp {t : SurfPos} (h : CStop t) : NotProp t := by
  obtain ⟨chars, col⟩ := t
  cases chars with
  | nil => trivial
  | cons l rest =>
    simp only [CStop] at h
    rcases h with rfl | rfl | rfl | rfl <;> simp [NotProp]

lemma cstop_tagStop {t : SurfPos} (h : CStop t) : TagStop t := by
  obtain ⟨chars, col⟩ := t
  cases chars with
  | nil => simp [TagStop]
  | cons l rest =>
    simp only [CStop] at h
    rcases h with rfl | rfl | rfl | rfl <;> simp [TagStop]

lemma cstop_notQuote {t : SurfPos} (h : CStop t) : NotQuote t := by
  obtain ⟨chars, col⟩ := t
  cases chars with
  | nil => intro r cl hh; cases hh
  | cons l rest =>
    simp only [CStop] at h
    rcases h with rfl | rfl | rfl | rfl <;> intro r cl hh <;> cases hh

lemma nstop_of_fstop {n : Nat} {c : YamlContext} {m : SurfPos} (h : FStop n c m) : NStop n c m :=
  let ⟨t, ho, hl⟩ := h; ⟨t, ho, litStop_cstop hl⟩

lemma closeStop_estop {t : SurfPos} (h : CloseStop t) : EStop t := by
  obtain ⟨chars, col⟩ := t
  cases chars with
  | nil => simp [CloseStop] at h
  | cons l rest => simp only [CloseStop, EStop] at h ⊢; rcases h with h | h <;> simp [h]

lemma nstop_tagStop {n : Nat} {c : YamlContext} {m : SurfPos} (h : NStop n c m) : TagStop m := by
  obtain ⟨t, ho, hl⟩ := h
  cases ho with
  | none => exact cstop_tagStop hl
  | some =>
    rcases sep_shape ‹SSeparate n c m t› with rfl | hh
    · exact cstop_tagStop hl
    · exact sepHead_tagStop hh

lemma pstop_of_nstop {n : Nat} {c : YamlContext} {m : SurfPos} (h : NStop n c m) : PStop n c m := by
  obtain ⟨t, ho, hl⟩ := h
  exact ⟨nstop_tagStop ⟨t, ho, hl⟩, t, ho, cstop_sepStop hl, cstop_notProp hl⟩

lemma nstop_notQuote {n : Nat} {c : YamlContext} {m : SurfPos} (h : NStop n c m) : NotQuote m := by
  obtain ⟨t, ho, hl⟩ := h
  cases ho with
  | none => exact cstop_notQuote hl
  | some =>
    rcases sep_shape ‹SSeparate n c m t› with rfl | hh
    · exact cstop_notQuote hl
    · obtain ⟨chars, col⟩ := m
      cases chars with
      | nil => intro r cl hh; cases hh
      | cons d rest =>
        intro r cl hh
        cases hh
        simp [SepHead] at hh

lemma first_len {c : YamlContext} {a a₁ : SurfPos} (h : SNsPlainFirst c a a₁) :
    a₁.chars.length < a.chars.length := by
  cases h <;> simp

lemma skipWS_len : ∀ (cs : List Char) (col : Nat), (skipWS cs col).chars.length ≤ cs.length := by
  intro cs
  induction cs with
  | nil => intro col; simp [skipWS]
  | cons d ds ih =>
    intro col
    simp only [skipWS]
    split
    · exact Nat.le_trans (ih _) (Nat.le_succ _)
    · split
      · exact Nat.le_trans (ih _) (Nat.le_succ _)
      · simp

lemma pstep_len {n : Nat} {c : YamlContext} {x z : SurfPos} (h : PStep n c x z) :
    z.chars.length ≤ x.chars.length := by
  rw [pstep_end h]
  simp only [stepEnd, skipWSP]
  have := skipWS_len x.chars x.col
  have h3 := @List.length_tail _ (skipWS x.chars x.col).chars
  omega

lemma psteps_len {n : Nat} {c : YamlContext} {a m : SurfPos} (h : GStar (PStep n c) a m) :
    m.chars.length ≤ a.chars.length := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons => rename_i hs _ ih; exact Nat.le_trans ih (pstep_len hs)

lemma plain_len {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SNsPlain n c a m) :
    m.chars.length < a.chars.length := by
  obtain ⟨a₁, hf, hs⟩ := plain_steps h
  exact Nat.lt_of_le_of_lt (psteps_len hs) (first_len hf)

lemma glit_len {ch : Char} {a b : SurfPos} (h : GLit ch a b) : b.chars.length < a.chars.length := by
  cases h; simp

lemma sq_len {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SCSingleQuoted n c a m) :
    m.chars.length < a.chars.length := by
  have hs := scSingleQuoted_suffix h
  cases h with
  | mk =>
    have := glit_len ‹GLit '\'' a _›
    have h2 := (gseq_suffix (fun _ _ h => snbSingleText_suffix h) (fun _ _ h => glit_suffix h)
      (GSeq.mk _ _ _ ‹SNbSingleText n c _ _› ‹GLit '\'' _ m›)).length_le
    omega

lemma dq_len {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SCDoubleQuoted n c a m) :
    m.chars.length < a.chars.length := by
  cases h with
  | mk =>
    have := glit_len ‹GLit '"' a _›
    have h2 := (gseq_suffix (fun _ _ h => snbDoubleText_suffix h) (fun _ _ h => glit_suffix h)
      (GSeq.mk _ _ _ ‹SNbDoubleText n c _ _› ‹GLit '"' _ m›)).length_le
    omega

lemma seq_len {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TFlowSequence n c a m ev) : m.chars.length < a.chars.length := by
  have hs := (tFlowSequence_suffix h).length_le
  cases h with
  | empty _ _ _ _ _ _ hl ho hr =>
    have := glit_len hl
    have := (gopt_suffix (fun _ _ => sSeparate_suffix) ho).length_le
    have := (glit_suffix hr).length_le
    omega
  | nonempty _ _ _ _ _ _ _ _ hl ho he hr =>
    have := glit_len hl
    have := (gopt_suffix (fun _ _ => sSeparate_suffix) ho).length_le
    have := (tFlowSeqEntries_suffix he).length_le
    have := (glit_suffix hr).length_le
    omega

lemma map_len {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TFlowMapping n c a m ev) : m.chars.length < a.chars.length := by
  cases h with
  | empty _ _ _ _ _ _ hl ho hr =>
    have := glit_len hl
    have := (gopt_suffix (fun _ _ => sSeparate_suffix) ho).length_le
    have := (glit_suffix hr).length_le
    omega
  | nonempty _ _ _ _ _ _ _ _ hl ho he hr =>
    have := glit_len hl
    have := (gopt_suffix (fun _ _ => sSeparate_suffix) ho).length_le
    have := (tFlowMapEntries_suffix he).length_le
    have := (glit_suffix hr).length_le
    omega

lemma content_len {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TFlowContent n c a m ev) : m.chars.length < a.chars.length := by
  cases h with
  | plain _ _ _ _ hp => exact plain_len hp
  | flowSeq _ _ _ _ _ hx => exact seq_len hx
  | flowMap _ _ _ _ _ hx => exact map_len hx
  | singleQ _ _ _ _ hx => exact sq_len hx
  | doubleQ _ _ _ _ hx => exact dq_len hx

lemma jsonContent_len {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TCFlowJsonContent n c a m ev) : m.chars.length < a.chars.length := by
  cases h with
  | flowSeq _ _ _ _ _ hx => exact seq_len hx
  | flowMap _ _ _ _ _ hx => exact map_len hx
  | singleQ _ _ _ _ hx => exact sq_len hx
  | doubleQ _ _ _ _ hx => exact dq_len hx

lemma props_len {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TCNsProperties n c a m ev) : m.chars.length < a.chars.length := by
  have hs := (tprops_suffix h).length_le
  cases h with
  | tagFirst _ _ _ _ _ ht ho =>
    have := tag_len ht.1
    cases ho with
    | none => exact this
    | some =>
      cases ‹TSeq (Lift (SSeparate n c)) TCNsAnchorProperty _ _ _› with
      | mk _ _ _ _ _ hsp ha =>
        have := (sSeparate_suffix hsp.1).length_le
        have := anchor_len ha.1
        omega
  | anchorFirst _ _ _ _ _ ha ho =>
    have := anchor_len ha.1
    cases ho with
    | none => exact this
    | some =>
      cases ‹TSeq (Lift (SSeparate n c)) TCNsTagProperty _ _ _› with
      | mk _ _ _ _ _ hsp ht =>
        have := (sSeparate_suffix hsp.1).length_le
        have := tag_len ht.1
        omega

lemma node_len {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TFlowNode n c a m ev) : m.chars.length < a.chars.length := by
  cases h with
  | alias _ _ _ _ _ ha =>
    cases ha.1 with
    | mk =>
      have := gchar_run_len (gplus_star ‹GPlus (GChar isNsAnchorChar) _ _›)
      simp at this ⊢; omega
  | content _ _ _ _ _ hc => exact content_len hc
  | propsContent _ _ _ _ _ _ _ _ hp hs hc =>
    have := props_len hp
    have := (sSeparate_suffix hs).length_le
    have := content_len hc
    omega
  | propsEmpty _ _ _ _ _ hp => exact props_len hp

/-- Same-end form of property determinism: one span, one trace. -/
lemma props_det_eq {n : Nat} {c : YamlContext} {s M : SurfPos} {ev₁ ev₂ : List Event}
    (h₁ : TCNsProperties n c s M ev₁) (h₂ : TCNsProperties n c s M ev₂) : ev₁ = ev₂ := by
  cases h₁ with
  | tagFirst _ u₁ _ _ e₁ ht₁ ho₁ =>
    cases h₂ with
    | tagFirst _ u₂ _ _ e₂ ht₂ ho₂ =>
      cases ho₁ with
      | none =>
        cases ho₂ with
        | none => rw [ht₁.2, ht₂.2]
        | some =>
          exfalso
          cases ‹TSeq (Lift (SSeparate n c)) TCNsAnchorProperty u₂ M _› with
          | mk _ v _ _ _ hs ha =>
            have hh := sep_sepHead hs.1 (by have := tag_col ht₂.1; omega)
            have l1 := (sSeparate_suffix hs.1).length_le
            have l2 := anchor_len ha.1
            have := tag_extend ht₂.1 hh ht₁.1 (by omega)
            subst this; omega
      | some =>
        cases ‹TSeq (Lift (SSeparate n c)) TCNsAnchorProperty u₁ M _› with
        | mk _ v₁ _ _ _ hs₁ ha₁ =>
          have hh₁ := sep_sepHead hs₁.1 (by have := tag_col ht₁.1; omega)
          cases ho₂ with
          | none =>
            exfalso
            have l1 := (sSeparate_suffix hs₁.1).length_le
            have l2 := anchor_len ha₁.1
            have := tag_extend ht₁.1 hh₁ ht₂.1 (by omega)
            subst this; omega
          | some =>
            cases ‹TSeq (Lift (SSeparate n c)) TCNsAnchorProperty u₂ M _› with
            | mk _ v₂ _ _ _ hs₂ ha₂ =>
              have hh₂ := sep_sepHead hs₂.1 (by have := tag_col ht₂.1; omega)
              cases tag_det ht₁.1 ht₂.1 (sepHead_tagStop hh₁) (sepHead_tagStop hh₂)
              have e1 := sep_det hs₁.1 (anchor_sepStop ha₁.1)
              have e2 := sep_det hs₂.1 (anchor_sepStop ha₂.1)
              rw [← e2] at e1; subst e1
              rw [ht₁.2, ht₂.2, ha₁.2, ha₂.2, hs₁.2, hs₂.2]
    | anchorFirst _ _ _ _ _ ha₂ _ =>
      obtain ⟨r₁, c₁, e₁⟩ := tag_head ht₁.1
      obtain ⟨r₂, c₂, e₂⟩ := anchor_head ha₂.1
      rw [e₁] at e₂; cases e₂
  | anchorFirst _ u₁ _ _ e₁ ha₁ ho₁ =>
    cases h₂ with
    | tagFirst _ _ _ _ _ ht₂ _ =>
      obtain ⟨r₁, c₁, e₁⟩ := anchor_head ha₁.1
      obtain ⟨r₂, c₂, e₂⟩ := tag_head ht₂.1
      rw [e₁] at e₂; cases e₂
    | anchorFirst _ u₂ _ _ e₂ ha₂ ho₂ =>
      cases anchor_det ha₁.1 ha₂.1
      rcases anchorOpt_end ha₁.1 ho₁ with ⟨rfl, rfl⟩ | ⟨v₁, hs₁, ht₁, rfl, hv₁, -⟩
      · rcases anchorOpt_end ha₂.1 ho₂ with ⟨-, rfl⟩ | ⟨v₂, hs₂, ht₂, -, -, -⟩
        · rw [ha₁.2, ha₂.2]
        · exfalso
          have := (sSeparate_suffix hs₂).length_le
          have := tag_len ht₂
          omega
      · rcases anchorOpt_end ha₂.1 ho₂ with ⟨rfl, -⟩ | ⟨v₂, hs₂, ht₂, rfl, hv₂, -⟩
        · exfalso
          have := (sSeparate_suffix hs₁).length_le
          have := tag_len ht₁
          omega
        · rw [← hv₁] at hv₂; subst hv₂
          rw [ha₁.2, ha₂.2]

/-! ## Entry shapes shared by sequences and mappings

The thirteen `TFlowSeqEntry` and thirteen `TFlowMapEntry` constructors have the same
shapes; both are mapped onto `EShape` so the pairwise analysis is done once. -/

/-- What follows a `:`: nothing, or a mandatory separator and a value node. -/
def Tail (n : Nat) (c : YamlContext) (s₃ m : SurfPos) (e : List Event) : Prop :=
  (s₃ = m ∧ e = []) ∨ ∃ s₄, SSeparate n c s₃ s₄ ∧ TFlowNode n c s₄ m e

/-- An entry that begins with a node: the node alone, a key with a `:` tail, or a
JSON-like key with an adjacent value. -/
inductive KShape (n : Nat) (c : YamlContext) : SurfPos → SurfPos → List Event → Prop where
  | node {s m : SurfPos} {ev : List Event} : TFlowNode n c s m ev → KShape n c s m ev
  | key {s s₁ s₂ s₃ m : SurfPos} {e₁ e₂ : List Event} :
      TFlowNode n c s s₁ e₁ → GOpt (SSeparate n c) s₁ s₂ → GLit ':' s₂ s₃ → Tail n c s₃ m e₂ →
      KShape n c s m (e₁ ++ e₂)
  | jkey {s s₁ s₂ s₃ s₄ m : SurfPos} {e₁ e₂ : List Event} :
      TCFlowJsonNode n c s s₁ e₁ → GOpt (SSeparate n c) s₁ s₂ → GLit ':' s₂ s₃ →
      GOpt (SSeparate n c) s₃ s₄ → TFlowNode n c s₄ m e₂ → KShape n c s m (e₁ ++ e₂)

/-- What follows `? s-separate`. -/
inductive QTail (n : Nat) (c : YamlContext) : SurfPos → SurfPos → List Event → Prop where
  | empty {s : SurfPos} : QTail n c s s []
  | k {s m : SurfPos} {ev : List Event} : KShape n c s m ev → QTail n c s m ev
  | colon {s s₃ m : SurfPos} {ev : List Event} : GLit ':' s s₃ → Tail n c s₃ m ev → QTail n c s m ev

/-- The shape of any flow sequence or mapping entry. -/
inductive EShape (n : Nat) (c : YamlContext) : SurfPos → SurfPos → List Event → Prop where
  | k {s m : SurfPos} {ev : List Event} : KShape n c s m ev → EShape n c s m ev
  | quest {s s₁ s₂ m : SurfPos} {ev : List Event} :
      GLit '?' s s₁ → SSeparate n c s₁ s₂ → QTail n c s₂ m ev → EShape n c s m ev
  | colon {s s₁ m : SurfPos} {ev : List Event} : GLit ':' s s₁ → Tail n c s₁ m ev → EShape n c s m ev

lemma seqEntry_shape {n : Nat} {c : YamlContext} {s m : SurfPos} {ev : List Event}
    (h : TFlowSeqEntry n c s m ev) : EShape n c s m ev := by
  match h with
  | .node _ _ _ _ _ h0 => exact .k (.node h0)
  | .pairValue _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 => exact .k (.key h0 h1 h2 (Or.inr ⟨_, h3, h4⟩))
  | .pairEmpty _ _ _ _ _ _ _ h0 h1 h2 =>
    have := EShape.k (KShape.key h0 h1 h2 (Or.inl ⟨rfl, rfl⟩)); simpa using this
  | .pairJsonAdjacentValue _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 => exact .k (.jkey h0 h1 h2 h3 h4)
  | .explicitPairJsonAdjacentValue _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 =>
    exact .quest h0 h1 (.k (.jkey h2 h3 h4 h5 h6))
  | .explicitPairValue _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 =>
    exact .quest h0 h1 (.k (.key h2 h3 h4 (Or.inr ⟨_, h5, h6⟩)))
  | .explicitPairEmpty _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 =>
    have := EShape.quest h0 h1 (QTail.k (KShape.key h2 h3 h4 (Or.inl ⟨rfl, rfl⟩)))
    simpa using this
  | .explicitPairKeyOnly _ _ _ _ _ _ _ h0 h1 h2 => exact .quest h0 h1 (.k (.node h2))
  | .explicitPairEmptyNodes _ _ _ _ _ h0 h1 => exact .quest h0 h1 .empty
  | .emptyKeyValue _ _ _ _ _ _ _ h0 h1 h2 => exact .colon h0 (Or.inr ⟨_, h1, h2⟩)
  | .emptyKeyEmpty _ _ _ _ h0 => exact .colon h0 (Or.inl ⟨rfl, rfl⟩)
  | .explicitEmptyKeyValue _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 =>
    exact .quest h0 h1 (.colon h2 (Or.inr ⟨_, h3, h4⟩))
  | .explicitEmptyKeyEmpty _ _ _ _ _ _ h0 h1 h2 => exact .quest h0 h1 (.colon h2 (Or.inl ⟨rfl, rfl⟩))

lemma mapEntry_shape {n : Nat} {c : YamlContext} {s m : SurfPos} {ev : List Event}
    (h : TFlowMapEntry n c s m ev) : EShape n c s m ev := by
  match h with
  | .explicitValue _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 =>
    exact .quest h0 h1 (.k (.key h2 h3 h4 (Or.inr ⟨_, h5, h6⟩)))
  | .explicitEmpty _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 =>
    have := EShape.quest h0 h1 (QTail.k (KShape.key h2 h3 h4 (Or.inl ⟨rfl, rfl⟩)))
    simpa using this
  | .explicitKeyOnly _ _ _ _ _ _ _ h0 h1 h2 => exact .quest h0 h1 (.k (.node h2))
  | .implicitValue _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 => exact .k (.key h0 h1 h2 (Or.inr ⟨_, h3, h4⟩))
  | .implicitEmpty _ _ _ _ _ _ _ h0 h1 h2 =>
    have := EShape.k (KShape.key h0 h1 h2 (Or.inl ⟨rfl, rfl⟩)); simpa using this
  | .jsonKeyAdjacentValue _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 => exact .k (.jkey h0 h1 h2 h3 h4)
  | .explicitJsonKeyAdjacentValue _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 =>
    exact .quest h0 h1 (.k (.jkey h2 h3 h4 h5 h6))
  | .bareKey _ _ _ _ _ h0 => exact .k (.node h0)
  | .emptyKeyValue _ _ _ _ _ _ _ h0 h1 h2 => exact .colon h0 (Or.inr ⟨_, h1, h2⟩)
  | .emptyKeyEmpty _ _ _ _ h0 => exact .colon h0 (Or.inl ⟨rfl, rfl⟩)
  | .explicitEmptyNodes _ _ _ _ _ h0 h1 => exact .quest h0 h1 .empty
  | .explicitEmptyKeyValue _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 =>
    exact .quest h0 h1 (.colon h2 (Or.inr ⟨_, h3, h4⟩))
  | .explicitEmptyKeyEmpty _ _ _ _ _ _ h0 h1 h2 => exact .quest h0 h1 (.colon h2 (Or.inl ⟨rfl, rfl⟩))

lemma kshape_head {n : Nat} {c : YamlContext} {s m : SurfPos} {ev : List Event}
    (h : KShape n c s m ev) :
    (∃ rest col, s = ⟨'*' :: rest, col⟩) ∨ (∃ rest col, s = ⟨'!' :: rest, col⟩) ∨
      (∃ rest col, s = ⟨'&' :: rest, col⟩) ∨ ContentHead c s := by
  cases h with
  | node hn => exact node_head hn
  | key hn _ _ _ => exact node_head hn
  | jkey hj _ _ _ _ => exact Or.inr (jsonNode_head hj)

lemma kshape_sepStop {n : Nat} {c : YamlContext} {s m : SurfPos} {ev : List Event}
    (h : KShape n c s m ev) : SepStop s := by
  rcases kshape_head h with ⟨r, cl, rfl⟩ | ⟨r, cl, rfl⟩ | ⟨r, cl, rfl⟩ | hc
  · simp [SepStop]
  · simp [SepStop]
  · simp [SepStop]
  · exact contentHead_sepStop hc

lemma kshape_not_estop {n : Nat} {c : YamlContext} {s m : SurfPos} {ev : List Event}
    (h : KShape n c s m ev) (he : EStop s) : False := by
  rcases kshape_head h with ⟨r, cl, rfl⟩ | ⟨r, cl, rfl⟩ | ⟨r, cl, rfl⟩ | hc
  · simp [EStop] at he
  · simp [EStop] at he
  · simp [EStop] at he
  · exact contentHead_not_estop hc he

lemma eshape_sepStop {n : Nat} {c : YamlContext} {s m : SurfPos} {ev : List Event}
    (h : EShape n c s m ev) : SepStop s := by
  cases h with
  | k hk => exact kshape_sepStop hk
  | quest hq _ _ => cases hq; simp [SepStop]
  | colon hq _ => cases hq; simp [SepStop]

lemma eshape_not_estop {n : Nat} {c : YamlContext} {s m : SurfPos} {ev : List Event}
    (h : EShape n c s m ev) (he : EStop s) : False := by
  cases h with
  | k hk => exact kshape_not_estop hk he
  | quest hq _ _ => cases hq; simp [EStop] at he
  | colon hq _ => cases hq; simp [EStop] at he

lemma eshape_not_close {n : Nat} {c : YamlContext} {s m : SurfPos} {ev : List Event}
    (h : EShape n c s m ev) (he : CloseStop s) : False :=
  eshape_not_estop h (closeStop_estop he)

/-- After a `:` tail that is legally followed, the position after the `:` starts a
separator or is an entry stop. -/
lemma tail_follow {n : Nat} {c : YamlContext} {s₃ m : SurfPos} {e : List Event}
    (ht : Tail n c s₃ m e) (hf : EFollow n c m) (hcol : 1 ≤ s₃.col) : SepHead s₃ ∨ EStop s₃ := by
  rcases ht with ⟨rfl, -⟩ | ⟨s₄, hs, hn⟩
  · obtain ⟨t, ho, he⟩ := hf
    cases ho with
    | none => exact Or.inr he
    | some => exact Or.inl (sep_sepHead ‹SSeparate n c s₃ t› hcol)
  · exact Or.inl (sep_sepHead hs hcol)

lemma safe_not_sepHead {c : YamlContext} {nx : Char} {r : List Char} {col : Nat}
    (hs : isNsPlainSafe c nx) (hh : SepHead ⟨nx :: r, col + 1⟩) : False := by
  obtain ⟨hw, hb⟩ := nsChar_facts (plainSafe_nsChar hs)
  simp only [SepHead] at hh
  rcases hh with h | h | h | h | ⟨-, h⟩
  · exact hw (Or.inl h)
  · exact hw (Or.inr h)
  · exact hb (Or.inl h)
  · exact hb (Or.inr h)
  · simp at h

lemma safe_not_estop {c : YamlContext} (hc : FlowCtx c) {nx : Char} {r : List Char} {col : Nat}
    (hs : isNsPlainSafe c nx) (he : EStop ⟨nx :: r, col⟩) : False := by
  have hfi := plainSafe_flow hc hs
  simp only [EStop] at he
  apply hfi
  rcases he with rfl | rfl | rfl <;> decide

lemma contentHead_quest {c : YamlContext} {rest : List Char} {col : Nat}
    (h : ContentHead c ⟨'?' :: rest, col⟩) (hh : SepHead ⟨rest, col + 1⟩) : False := by
  simp only [ContentHead] at h
  rcases h with ⟨-, hi⟩ | ⟨-, nx, r, rfl, hs⟩ | h | h | h | h
  · exact hi (by decide)
  · exact safe_not_sepHead hs hh
  all_goals simp at h

lemma contentHead_colon {c : YamlContext} (hc : FlowCtx c) {rest : List Char} {col : Nat}
    (h : ContentHead c ⟨':' :: rest, col⟩) (hh : SepHead ⟨rest, col + 1⟩ ∨ EStop ⟨rest, col + 1⟩) :
    False := by
  simp only [ContentHead] at h
  rcases h with ⟨-, hi⟩ | ⟨-, nx, r, rfl, hs⟩ | h | h | h | h
  · exact hi (by decide)
  · rcases hh with hh | hh
    · exact safe_not_sepHead hs hh
    · exact safe_not_estop hc hs hh
  all_goals simp at h

lemma kshape_vs_quest {n : Nat} {c : YamlContext} {s s₁ s₂ m : SurfPos} {ev : List Event}
    (hk : KShape n c s m ev) (hq : GLit '?' s s₁) (hs : SSeparate n c s₁ s₂) : False := by
  cases hq with
  | mk rest col =>
    rcases kshape_head hk with ⟨r, cl, h⟩ | ⟨r, cl, h⟩ | ⟨r, cl, h⟩ | hc
    · cases h
    · cases h
    · cases h
    · exact contentHead_quest hc (sep_sepHead hs (by simp))

lemma kshape_vs_colon {n : Nat} {c : YamlContext} (hc : FlowCtx c) {s s₁ m₁ m₂ : SurfPos}
    {ev₁ e : List Event} (hk : KShape n c s m₁ ev₁) (hq : GLit ':' s s₁) (ht : Tail n c s₁ m₂ e)
    (hf : EFollow n c m₂) : False := by
  cases hq with
  | mk rest col =>
    rcases kshape_head hk with ⟨r, cl, h⟩ | ⟨r, cl, h⟩ | ⟨r, cl, h⟩ | hch
    · cases h
    · cases h
    · cases h
    · exact contentHead_colon hc hch (tail_follow ht hf (by simp))

/-! ## Determinism predicates -/

def NodeDet (n : Nat) (c : YamlContext) (s : SurfPos) : Prop :=
  ∀ {m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}, TFlowNode n c s m₁ ev₁ → TFlowNode n c s m₂ ev₂ →
    Follow n c m₁ m₂ → m₁ = m₂ ∧ ev₁ = ev₂

def ContentDet (n : Nat) (c : YamlContext) (s : SurfPos) : Prop :=
  ∀ {m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}, TFlowContent n c s m₁ ev₁ → TFlowContent n c s m₂ ev₂ →
    Follow n c m₁ m₂ → m₁ = m₂ ∧ ev₁ = ev₂

def JsonDet (n : Nat) (c : YamlContext) (s : SurfPos) : Prop :=
  ∀ {m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}, TCFlowJsonNode n c s m₁ ev₁ → TCFlowJsonNode n c s m₂ ev₂ →
    (m₁ = m₂ ∨ (NStop n c m₁ ∧ NStop n c m₂)) → m₁ = m₂ ∧ ev₁ = ev₂

def CrossDet (n : Nat) (c : YamlContext) (s : SurfPos) : Prop :=
  ∀ {m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}, TFlowNode n c s m₁ ev₁ → TCFlowJsonNode n c s m₂ ev₂ →
    NStop n c m₁ → NStop n c m₂ → m₁ = m₂ ∧ ev₁ = ev₂

def SeqDet (n : Nat) (c : YamlContext) (s : SurfPos) : Prop :=
  ∀ {m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}, TFlowSequence n c s m₁ ev₁ → TFlowSequence n c s m₂ ev₂ →
    m₁ = m₂ ∧ ev₁ = ev₂

def MapDet (n : Nat) (c : YamlContext) (s : SurfPos) : Prop :=
  ∀ {m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}, TFlowMapping n c s m₁ ev₁ → TFlowMapping n c s m₂ ev₂ →
    m₁ = m₂ ∧ ev₁ = ev₂

def SeqEntriesDet (n : Nat) (c : YamlContext) (s : SurfPos) : Prop :=
  ∀ {m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}, TFlowSeqEntries n c s m₁ ev₁ →
    TFlowSeqEntries n c s m₂ ev₂ → CloseStop m₁ → CloseStop m₂ → m₁ = m₂ ∧ ev₁ = ev₂

def MapEntriesDet (n : Nat) (c : YamlContext) (s : SurfPos) : Prop :=
  ∀ {m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}, TFlowMapEntries n c s m₁ ev₁ →
    TFlowMapEntries n c s m₂ ev₂ → CloseStop m₁ → CloseStop m₂ → m₁ = m₂ ∧ ev₁ = ev₂

/-! ## Entry shapes are deterministic under the entry follow -/

lemma colon_follow {n : Nat} {c : YamlContext} {s₂ s₃ m : SurfPos} {e : List Event}
    (hl : GLit ':' s₂ s₃) (ht : Tail n c s₃ m e) (hf : EFollow n c m) :
    ∃ rest col, s₂ = ⟨':' :: rest, col⟩ ∧ s₃ = ⟨rest, col + 1⟩ ∧ ColonFollow rest := by
  cases hl with
  | mk rest col =>
    refine ⟨rest, col, rfl, rfl, ?_⟩
    rcases tail_follow ht hf (by simp) with hh | he
    · exact sepHead_colonFollow hh
    · cases rest with
      | nil => trivial
      | cons d ds =>
        simp only [EStop] at he
        simp only [ColonFollow]
        rcases he with rfl | rfl | rfl <;> simp [isFlowIndicatorProp]

lemma key_fstop {n : Nat} {c : YamlContext} {s₁ s₂ s₃ m : SurfPos} {e : List Event}
    (ho : GOpt (SSeparate n c) s₁ s₂) (hl : GLit ':' s₂ s₃) (ht : Tail n c s₃ m e)
    (hf : EFollow n c m) : FStop n c s₁ := by
  obtain ⟨rest, col, rfl, rfl, hcf⟩ := colon_follow hl ht hf
  exact fstop_of_colon ho hl hcf

lemma colon_nstop {n : Nat} {c : YamlContext} {s₁ s₂ s₃ : SurfPos}
    (ho : GOpt (SSeparate n c) s₁ s₂) (hl : GLit ':' s₂ s₃) : NStop n c s₁ := by
  cases hl; exact ⟨_, ho, by simp [CStop]⟩

lemma colon_sepStop {s₂ s₃ : SurfPos} (hl : GLit ':' s₂ s₃) : SepStop s₂ := by
  cases hl; simp [SepStop]

lemma colon_not_estop {s₂ s₃ : SurfPos} (hl : GLit ':' s₂ s₃) (he : EStop s₂) : False := by
  cases hl; simp [EStop] at he

/-- A node that is legally followed cannot end where a key ends (a `:` would follow). -/
lemma node_key_contra {n : Nat} {c : YamlContext} {m s₂ s₃ : SurfPos}
    (hf : EFollow n c m) (ho : GOpt (SSeparate n c) m s₂) (hl : GLit ':' s₂ s₃) : False := by
  obtain ⟨t, hot, he⟩ := hf
  rw [gopt_sep_det hot (estop_sepStop he), ← gopt_sep_det ho (colon_sepStop hl)] at he
  exact colon_not_estop hl he

lemma tail_det {n : Nat} {c : YamlContext} (hc : FlowCtx c) {s₃ m₁ m₂ : SurfPos} {e₁ e₂ : List Event}
    (HN : ∀ s', s'.chars.length ≤ s₃.chars.length → NodeDet n c s')
    (h₁ : Tail n c s₃ m₁ e₁) (h₂ : Tail n c s₃ m₂ e₂) (f₁ : EFollow n c m₁) (f₂ : EFollow n c m₂) :
    m₁ = m₂ ∧ e₁ = e₂ := by
  rcases h₁ with ⟨rfl, rfl⟩ | ⟨s₄, hs, hn⟩
  · rcases h₂ with ⟨rfl, rfl⟩ | ⟨s₄, hs, hn⟩
    · exact ⟨rfl, rfl⟩
    · exfalso
      obtain ⟨t, hot, he⟩ := f₁
      rw [gopt_sep_det hot (estop_sepStop he), ← sep_det hs (node_sepStop hn)] at he
      exact node_not_estop hn he
  · rcases h₂ with ⟨rfl, rfl⟩ | ⟨s₄', hs', hn'⟩
    · exfalso
      obtain ⟨t, hot, he⟩ := f₂
      rw [gopt_sep_det hot (estop_sepStop he), ← sep_det hs (node_sepStop hn)] at he
      exact node_not_estop hn he
    · have e := sep_det hs (node_sepStop hn)
      rw [← sep_det hs' (node_sepStop hn')] at e
      subst e
      exact HN _ (sSeparate_suffix hs).length_le hn hn'
        (Or.inr ⟨hc, efollow_fstop f₁, efollow_fstop f₂⟩)

lemma kshape_det {n : Nat} {c : YamlContext} (hc : FlowCtx c) {s m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}
    (HN0 : NodeDet n c s) (HJ0 : JsonDet n c s) (HX0 : CrossDet n c s)
    (HN : ∀ s', s'.chars.length < s.chars.length → NodeDet n c s')
    (h₁ : KShape n c s m₁ ev₁) (h₂ : KShape n c s m₂ ev₂) (f₁ : EFollow n c m₁) (f₂ : EFollow n c m₂) :
    m₁ = m₂ ∧ ev₁ = ev₂ := by
  have HNle : ∀ {s₂ s₃ : SurfPos}, GLit ':' s₂ s₃ → s₂.chars.length ≤ s.chars.length →
      ∀ s', s'.chars.length ≤ s₃.chars.length → NodeDet n c s' := by
    intro s₂ s₃ hl hle s' hs'
    exact HN s' (by have := glit_len hl; omega)
  cases h₁ with
  | node hn₁ =>
    cases h₂ with
    | node hn₂ => exact HN0 hn₁ hn₂ (Or.inr ⟨hc, efollow_fstop f₁, efollow_fstop f₂⟩)
    | key hn₂ ho₂ hl₂ ht₂ =>
      exfalso
      obtain ⟨rfl, -⟩ := HN0 hn₁ hn₂ (Or.inr ⟨hc, efollow_fstop f₁, key_fstop ho₂ hl₂ ht₂ f₂⟩)
      exact node_key_contra f₁ ho₂ hl₂
    | jkey hj₂ ho₂ hl₂ ho₂' hn₂' =>
      exfalso
      obtain ⟨rfl, -⟩ := HX0 hn₁ hj₂ (nstop_of_fstop (efollow_fstop f₁)) (colon_nstop ho₂ hl₂)
      exact node_key_contra f₁ ho₂ hl₂
  | key hn₁ ho₁ hl₁ ht₁ =>
    cases h₂ with
    | node hn₂ =>
      exfalso
      obtain ⟨rfl, -⟩ := HN0 hn₂ hn₁ (Or.inr ⟨hc, efollow_fstop f₂, key_fstop ho₁ hl₁ ht₁ f₁⟩)
      exact node_key_contra f₂ ho₁ hl₁
    | key hn₂ ho₂ hl₂ ht₂ =>
      obtain ⟨rfl, rfl⟩ := HN0 hn₁ hn₂ (Or.inr ⟨hc, key_fstop ho₁ hl₁ ht₁ f₁, key_fstop ho₂ hl₂ ht₂ f₂⟩)
      have e := gopt_sep_det ho₁ (colon_sepStop hl₁)
      rw [← gopt_sep_det ho₂ (colon_sepStop hl₂)] at e
      subst e
      cases glit_det hl₁ hl₂
      obtain ⟨rfl, rfl⟩ := tail_det hc
        (HNle hl₁ (Nat.le_trans (gopt_suffix (fun _ _ => sSeparate_suffix) ho₁).length_le
          (tFlowNode_suffix hn₁).length_le)) ht₁ ht₂ f₁ f₂
      exact ⟨rfl, rfl⟩
    | jkey hj₂ ho₂ hl₂ ho₂' hn₂' =>
      obtain ⟨rfl, rfl⟩ := HX0 hn₁ hj₂ (nstop_of_fstop (key_fstop ho₁ hl₁ ht₁ f₁)) (colon_nstop ho₂ hl₂)
      have e := gopt_sep_det ho₁ (colon_sepStop hl₁)
      rw [← gopt_sep_det ho₂ (colon_sepStop hl₂)] at e
      subst e
      cases glit_det hl₁ hl₂
      rcases ht₁ with ⟨rfl, rfl⟩ | ⟨s₄, hs, hn⟩
      · exfalso
        obtain ⟨t, hot, he⟩ := f₁
        rw [gopt_sep_det hot (estop_sepStop he), ← gopt_sep_det ho₂' (node_sepStop hn₂')] at he
        exact node_not_estop hn₂' he
      · have e := sep_det hs (node_sepStop hn)
        rw [← gopt_sep_det ho₂' (node_sepStop hn₂')] at e
        subst e
        obtain ⟨rfl, rfl⟩ := HNle hl₁ (Nat.le_trans (gopt_suffix (fun _ _ => sSeparate_suffix) ho₁).length_le
          (tFlowNode_suffix hn₁).length_le) _ (sSeparate_suffix hs).length_le hn hn₂'
          (Or.inr ⟨hc, efollow_fstop f₁, efollow_fstop f₂⟩)
        exact ⟨rfl, rfl⟩
  | jkey hj₁ ho₁ hl₁ ho₁' hn₁' =>
    cases h₂ with
    | node hn₂ =>
      exfalso
      obtain ⟨rfl, -⟩ := HX0 hn₂ hj₁ (nstop_of_fstop (efollow_fstop f₂)) (colon_nstop ho₁ hl₁)
      exact node_key_contra f₂ ho₁ hl₁
    | key hn₂ ho₂ hl₂ ht₂ =>
      obtain ⟨rfl, rfl⟩ := HX0 hn₂ hj₁ (nstop_of_fstop (key_fstop ho₂ hl₂ ht₂ f₂)) (colon_nstop ho₁ hl₁)
      have e := gopt_sep_det ho₁ (colon_sepStop hl₁)
      rw [← gopt_sep_det ho₂ (colon_sepStop hl₂)] at e
      subst e
      cases glit_det hl₁ hl₂
      rcases ht₂ with ⟨rfl, rfl⟩ | ⟨s₄, hs, hn⟩
      · exfalso
        obtain ⟨t, hot, he⟩ := f₂
        rw [gopt_sep_det hot (estop_sepStop he), ← gopt_sep_det ho₁' (node_sepStop hn₁')] at he
        exact node_not_estop hn₁' he
      · have e := sep_det hs (node_sepStop hn)
        rw [← gopt_sep_det ho₁' (node_sepStop hn₁')] at e
        subst e
        obtain ⟨rfl, rfl⟩ := HNle hl₁ (Nat.le_trans (gopt_suffix (fun _ _ => sSeparate_suffix) ho₁).length_le
          (tCFlowJsonNode_suffix hj₁).length_le) _ (sSeparate_suffix hs).length_le hn₁' hn
          (Or.inr ⟨hc, efollow_fstop f₁, efollow_fstop f₂⟩)
        exact ⟨rfl, rfl⟩
    | jkey hj₂ ho₂ hl₂ ho₂' hn₂' =>
      obtain ⟨rfl, rfl⟩ := HJ0 hj₁ hj₂ (Or.inr ⟨colon_nstop ho₁ hl₁, colon_nstop ho₂ hl₂⟩)
      have e := gopt_sep_det ho₁ (colon_sepStop hl₁)
      rw [← gopt_sep_det ho₂ (colon_sepStop hl₂)] at e
      subst e
      cases glit_det hl₁ hl₂
      have e := gopt_sep_det ho₁' (node_sepStop hn₁')
      rw [← gopt_sep_det ho₂' (node_sepStop hn₂')] at e
      subst e
      obtain ⟨rfl, rfl⟩ := HNle hl₁ (Nat.le_trans (gopt_suffix (fun _ _ => sSeparate_suffix) ho₁).length_le
        (tCFlowJsonNode_suffix hj₁).length_le) _ (gopt_suffix (fun _ _ => sSeparate_suffix) ho₁').length_le
        hn₁' hn₂' (Or.inr ⟨hc, efollow_fstop f₁, efollow_fstop f₂⟩)
      exact ⟨rfl, rfl⟩

lemma quest_not_colon {s s₁ s₂ : SurfPos} (hq : GLit '?' s s₁) (hl : GLit ':' s s₂) : False := by
  cases hq; cases hl

/-- Entry shapes are deterministic up to the trailing separator under the entry follow. -/
lemma eshape_det {n : Nat} {c : YamlContext} (hc : FlowCtx c) {s m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}
    (HN0 : NodeDet n c s) (HJ0 : JsonDet n c s) (HX0 : CrossDet n c s)
    (HN : ∀ s', s'.chars.length < s.chars.length → NodeDet n c s')
    (HJ : ∀ s', s'.chars.length < s.chars.length → JsonDet n c s')
    (HX : ∀ s', s'.chars.length < s.chars.length → CrossDet n c s')
    (h₁ : EShape n c s m₁ ev₁) (h₂ : EShape n c s m₂ ev₂) (f₁ : EFollow n c m₁) (f₂ : EFollow n c m₂) :
    skipSep m₁ = skipSep m₂ ∧ ev₁ = ev₂ := by
  cases h₁ with
  | k hk₁ =>
    cases h₂ with
    | k hk₂ =>
      obtain ⟨rfl, rfl⟩ := kshape_det hc HN0 HJ0 HX0 HN hk₁ hk₂ f₁ f₂
      exact ⟨rfl, rfl⟩
    | quest hq hs _ => exact (kshape_vs_quest hk₁ hq hs).elim
    | colon hl ht => exact (kshape_vs_colon hc hk₁ hl ht f₂).elim
  | quest hq₁ hs₁ ht₁ =>
    cases h₂ with
    | k hk₂ => exact (kshape_vs_quest hk₂ hq₁ hs₁).elim
    | colon hl _ => exact (quest_not_colon hq₁ hl).elim
    | quest hq₂ hs₂ ht₂ =>
      cases glit_det hq₁ hq₂
      rename_i s₁ s₂ s₂'
      have hlt : s₂.chars.length < s.chars.length := by
        have := glit_len hq₁; have := (sSeparate_suffix hs₁).length_le; omega
      have hlt' : s₂'.chars.length < s.chars.length := by
        have := glit_len hq₁; have := (sSeparate_suffix hs₂).length_le; omega
      have hsk : skipSep s₂ = skipSep s₂' := by rw [← sep_skip hs₁, ← sep_skip hs₂]
      cases ht₁ with
      | empty =>
        cases ht₂ with
        | empty => exact ⟨hsk, rfl⟩
        | k hk₂ =>
          exfalso
          obtain ⟨t, hot, he⟩ := f₁
          rw [gopt_sep_det hot (estop_sepStop he), hsk, skipSep_stop (kshape_sepStop hk₂)] at he
          exact kshape_not_estop hk₂ he
        | colon hl₂ _ =>
          exfalso
          obtain ⟨t, hot, he⟩ := f₁
          rw [gopt_sep_det hot (estop_sepStop he), hsk, skipSep_stop (colon_sepStop hl₂)] at he
          exact colon_not_estop hl₂ he
      | k hk₁ =>
        cases ht₂ with
        | empty =>
          exfalso
          obtain ⟨t, hot, he⟩ := f₂
          rw [gopt_sep_det hot (estop_sepStop he), ← hsk, skipSep_stop (kshape_sepStop hk₁)] at he
          exact kshape_not_estop hk₁ he
        | k hk₂ =>
          have e : s₂ = s₂' := by
            rw [← skipSep_stop (kshape_sepStop hk₁), ← skipSep_stop (kshape_sepStop hk₂)]; exact hsk
          subst e
          obtain ⟨rfl, rfl⟩ := kshape_det hc (HN _ hlt) (HJ _ hlt) (HX _ hlt)
            (fun s' h => HN s' (Nat.lt_trans h hlt)) hk₁ hk₂ f₁ f₂
          exact ⟨rfl, rfl⟩
        | colon hl₂ ht₂ =>
          exfalso
          have e : s₂ = s₂' := by
            rw [← skipSep_stop (kshape_sepStop hk₁), ← skipSep_stop (colon_sepStop hl₂)]; exact hsk
          subst e
          exact kshape_vs_colon hc hk₁ hl₂ ht₂ f₂
      | colon hl₁ ht₁ =>
        cases ht₂ with
        | empty =>
          exfalso
          obtain ⟨t, hot, he⟩ := f₂
          rw [gopt_sep_det hot (estop_sepStop he), ← hsk, skipSep_stop (colon_sepStop hl₁)] at he
          exact colon_not_estop hl₁ he
        | k hk₂ =>
          exfalso
          have e : s₂ = s₂' := by
            rw [← skipSep_stop (colon_sepStop hl₁), ← skipSep_stop (kshape_sepStop hk₂)]; exact hsk
          subst e
          exact kshape_vs_colon hc hk₂ hl₁ ht₁ f₁
        | colon hl₂ ht₂ =>
          have e : s₂ = s₂' := by
            rw [← skipSep_stop (colon_sepStop hl₁), ← skipSep_stop (colon_sepStop hl₂)]; exact hsk
          subst e
          cases glit_det hl₁ hl₂
          obtain ⟨rfl, rfl⟩ := tail_det hc
            (fun s' h => HN s' (by have := glit_len hl₁; omega)) ht₁ ht₂ f₁ f₂
          exact ⟨rfl, rfl⟩
  | colon hl₁ ht₁ =>
    cases h₂ with
    | k hk₂ => exact (kshape_vs_colon hc hk₂ hl₁ ht₁ f₁).elim
    | quest hq _ _ => exact (quest_not_colon hq hl₁).elim
    | colon hl₂ ht₂ =>
      cases glit_det hl₁ hl₂
      obtain ⟨rfl, rfl⟩ := tail_det hc
        (fun s' h => HN s' (by have := glit_len hl₁; omega)) ht₁ ht₂ f₁ f₂
      exact ⟨rfl, rfl⟩
/-- The first entry of an entry list gives the list its head. -/
lemma TFlowSeqEntries_head {n : Nat} {c : YamlContext} {s m : SurfPos} {ev : List Event}
    (h : TFlowSeqEntries n c s m ev) : ∃ m' ev', TFlowSeqEntry n c s m' ev' := by
  cases h with
  | single _ _ _ _ _ _ he _ => exact ⟨_, _, he⟩
  | consMore _ _ _ _ _ _ _ _ _ _ he _ _ _ _ => exact ⟨_, _, he⟩
  | consEnd _ _ _ _ _ _ _ _ he _ _ _ => exact ⟨_, _, he⟩

lemma TFlowSeqEntries_det {n : Nat} {c : YamlContext} {s : SurfPos}
    (HE : ∀ {m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}, TFlowSeqEntry n c s m₁ ev₁ → TFlowSeqEntry n c s m₂ ev₂ →
      EFollow n c m₁ → EFollow n c m₂ → skipSep m₁ = skipSep m₂ ∧ ev₁ = ev₂)
    (IH : ∀ s', s'.chars.length < s.chars.length → SeqEntriesDet n c s') : SeqEntriesDet n c s := by
  intro m₁ m₂ ev₁ ev₂ h₁ h₂ c₁ c₂
  have c₁' := closeStop_estop c₁
  have c₂' := closeStop_estop c₂
  cases h₁ with
  | single _ _ _ _ _ _ he₁ ho₁ =>
    cases h₂ with
    | single _ _ _ _ _ _ he₂ ho₂ =>
      obtain ⟨hsk, rfl⟩ := HE he₁ he₂ ⟨_, ho₁, c₁'⟩ ⟨_, ho₂, c₂'⟩
      rw [gopt_sep_det ho₁ (estop_sepStop c₁'), gopt_sep_det ho₂ (estop_sepStop c₂'), hsk]
      exact ⟨rfl, rfl⟩
    | consMore _ _ _ _ _ _ _ _ _ _ he₂ ho₂ hl₂ _ _ =>
      exfalso
      obtain ⟨hsk, -⟩ := HE he₁ he₂ ⟨_, ho₁, c₁'⟩ ⟨_, ho₂, litStop_of_lit hl₂ (by simp)⟩
      rw [gopt_sep_det ho₁ (estop_sepStop c₁'), hsk, ← gopt_sep_det ho₂ (estop_sepStop (litStop_of_lit hl₂ (by simp)))] at c₁
      cases hl₂; simp [CloseStop] at c₁
    | consEnd _ _ _ _ _ _ _ _ he₂ ho₂ hl₂ _ =>
      exfalso
      obtain ⟨hsk, -⟩ := HE he₁ he₂ ⟨_, ho₁, c₁'⟩ ⟨_, ho₂, litStop_of_lit hl₂ (by simp)⟩
      rw [gopt_sep_det ho₁ (estop_sepStop c₁'), hsk, ← gopt_sep_det ho₂ (estop_sepStop (litStop_of_lit hl₂ (by simp)))] at c₁
      cases hl₂; simp [CloseStop] at c₁
  | consMore _ _ _ _ _ _ _ _ _ _ he₁ ho₁ hl₁ ho₁' hr₁ =>
    have e₁ := litStop_of_lit hl₁ (by simp)
    cases h₂ with
    | single _ _ _ _ _ _ he₂ ho₂ =>
      exfalso
      obtain ⟨hsk, -⟩ := HE he₁ he₂ ⟨_, ho₁, e₁⟩ ⟨_, ho₂, c₂'⟩
      rw [gopt_sep_det ho₂ (estop_sepStop c₂'), ← hsk, ← gopt_sep_det ho₁ (estop_sepStop e₁)] at c₂
      cases hl₁; simp [CloseStop] at c₂
    | consMore _ _ _ _ _ _ _ _ _ _ he₂ ho₂ hl₂ ho₂' hr₂ =>
      have e₂ := litStop_of_lit hl₂ (by simp)
      obtain ⟨hsk, rfl⟩ := HE he₁ he₂ ⟨_, ho₁, e₁⟩ ⟨_, ho₂, e₂⟩
      have e := gopt_sep_det ho₁ (estop_sepStop e₁)
      rw [hsk, ← gopt_sep_det ho₂ (estop_sepStop e₂)] at e
      subst e
      cases glit_det hl₁ hl₂
      have e := gopt_sep_det ho₁' (eshape_sepStop (seqEntry_shape (TFlowSeqEntries_head hr₁).choose_spec.choose_spec))
      rw [← gopt_sep_det ho₂' (eshape_sepStop (seqEntry_shape (TFlowSeqEntries_head hr₂).choose_spec.choose_spec))] at e
      subst e
      have l1 := (tFlowSeqEntry_suffix he₁).length_le
      have l2 := (gopt_suffix (fun _ _ => sSeparate_suffix) ho₁).length_le
      have l3 := glit_len hl₁
      have l4 := (gopt_suffix (fun _ _ => sSeparate_suffix) ho₁').length_le
      obtain ⟨rfl, rfl⟩ := IH _ (by omega) hr₁ hr₂ c₁ c₂
      exact ⟨rfl, rfl⟩
    | consEnd _ _ _ _ _ _ _ _ he₂ ho₂ hl₂ ho₂' =>
      exfalso
      have e₂ := litStop_of_lit hl₂ (by simp)
      obtain ⟨hsk, -⟩ := HE he₁ he₂ ⟨_, ho₁, e₁⟩ ⟨_, ho₂, e₂⟩
      have e := gopt_sep_det ho₁ (estop_sepStop e₁)
      rw [hsk, ← gopt_sep_det ho₂ (estop_sepStop e₂)] at e
      subst e
      cases glit_det hl₁ hl₂
      have e := gopt_sep_det ho₁' (eshape_sepStop (seqEntry_shape (TFlowSeqEntries_head hr₁).choose_spec.choose_spec))
      rw [← gopt_sep_det ho₂' (estop_sepStop c₂')] at e
      subst e
      exact eshape_not_close (seqEntry_shape (TFlowSeqEntries_head hr₁).choose_spec.choose_spec) c₂
  | consEnd _ _ _ _ _ _ _ _ he₁ ho₁ hl₁ ho₁' =>
    have e₁ := litStop_of_lit hl₁ (by simp)
    cases h₂ with
    | single _ _ _ _ _ _ he₂ ho₂ =>
      exfalso
      obtain ⟨hsk, -⟩ := HE he₁ he₂ ⟨_, ho₁, e₁⟩ ⟨_, ho₂, c₂'⟩
      rw [gopt_sep_det ho₂ (estop_sepStop c₂'), ← hsk, ← gopt_sep_det ho₁ (estop_sepStop e₁)] at c₂
      cases hl₁; simp [CloseStop] at c₂
    | consMore _ _ _ _ _ _ _ _ _ _ he₂ ho₂ hl₂ ho₂' hr₂ =>
      exfalso
      have e₂ := litStop_of_lit hl₂ (by simp)
      obtain ⟨hsk, -⟩ := HE he₁ he₂ ⟨_, ho₁, e₁⟩ ⟨_, ho₂, e₂⟩
      have e := gopt_sep_det ho₁ (estop_sepStop e₁)
      rw [hsk, ← gopt_sep_det ho₂ (estop_sepStop e₂)] at e
      subst e
      cases glit_det hl₁ hl₂
      have e := gopt_sep_det ho₂' (eshape_sepStop (seqEntry_shape (TFlowSeqEntries_head hr₂).choose_spec.choose_spec))
      rw [← gopt_sep_det ho₁' (estop_sepStop c₁')] at e
      subst e
      exact eshape_not_close (seqEntry_shape (TFlowSeqEntries_head hr₂).choose_spec.choose_spec) c₁
    | consEnd _ _ _ _ _ _ _ _ he₂ ho₂ hl₂ ho₂' =>
      have e₂ := litStop_of_lit hl₂ (by simp)
      obtain ⟨hsk, rfl⟩ := HE he₁ he₂ ⟨_, ho₁, e₁⟩ ⟨_, ho₂, e₂⟩
      have e := gopt_sep_det ho₁ (estop_sepStop e₁)
      rw [hsk, ← gopt_sep_det ho₂ (estop_sepStop e₂)] at e
      subst e
      cases glit_det hl₁ hl₂
      rw [gopt_sep_det ho₁' (estop_sepStop c₁'), gopt_sep_det ho₂' (estop_sepStop c₂')]
      exact ⟨rfl, rfl⟩

/-- The first entry of an entry list gives the list its head. -/
lemma TFlowMapEntries_head {n : Nat} {c : YamlContext} {s m : SurfPos} {ev : List Event}
    (h : TFlowMapEntries n c s m ev) : ∃ m' ev', TFlowMapEntry n c s m' ev' := by
  cases h with
  | single _ _ _ _ _ _ he _ => exact ⟨_, _, he⟩
  | consMore _ _ _ _ _ _ _ _ _ _ he _ _ _ _ => exact ⟨_, _, he⟩
  | consEnd _ _ _ _ _ _ _ _ he _ _ _ => exact ⟨_, _, he⟩

lemma TFlowMapEntries_det {n : Nat} {c : YamlContext} {s : SurfPos}
    (HE : ∀ {m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}, TFlowMapEntry n c s m₁ ev₁ → TFlowMapEntry n c s m₂ ev₂ →
      EFollow n c m₁ → EFollow n c m₂ → skipSep m₁ = skipSep m₂ ∧ ev₁ = ev₂)
    (IH : ∀ s', s'.chars.length < s.chars.length → MapEntriesDet n c s') : MapEntriesDet n c s := by
  intro m₁ m₂ ev₁ ev₂ h₁ h₂ c₁ c₂
  have c₁' := closeStop_estop c₁
  have c₂' := closeStop_estop c₂
  cases h₁ with
  | single _ _ _ _ _ _ he₁ ho₁ =>
    cases h₂ with
    | single _ _ _ _ _ _ he₂ ho₂ =>
      obtain ⟨hsk, rfl⟩ := HE he₁ he₂ ⟨_, ho₁, c₁'⟩ ⟨_, ho₂, c₂'⟩
      rw [gopt_sep_det ho₁ (estop_sepStop c₁'), gopt_sep_det ho₂ (estop_sepStop c₂'), hsk]
      exact ⟨rfl, rfl⟩
    | consMore _ _ _ _ _ _ _ _ _ _ he₂ ho₂ hl₂ _ _ =>
      exfalso
      obtain ⟨hsk, -⟩ := HE he₁ he₂ ⟨_, ho₁, c₁'⟩ ⟨_, ho₂, litStop_of_lit hl₂ (by simp)⟩
      rw [gopt_sep_det ho₁ (estop_sepStop c₁'), hsk, ← gopt_sep_det ho₂ (estop_sepStop (litStop_of_lit hl₂ (by simp)))] at c₁
      cases hl₂; simp [CloseStop] at c₁
    | consEnd _ _ _ _ _ _ _ _ he₂ ho₂ hl₂ _ =>
      exfalso
      obtain ⟨hsk, -⟩ := HE he₁ he₂ ⟨_, ho₁, c₁'⟩ ⟨_, ho₂, litStop_of_lit hl₂ (by simp)⟩
      rw [gopt_sep_det ho₁ (estop_sepStop c₁'), hsk, ← gopt_sep_det ho₂ (estop_sepStop (litStop_of_lit hl₂ (by simp)))] at c₁
      cases hl₂; simp [CloseStop] at c₁
  | consMore _ _ _ _ _ _ _ _ _ _ he₁ ho₁ hl₁ ho₁' hr₁ =>
    have e₁ := litStop_of_lit hl₁ (by simp)
    cases h₂ with
    | single _ _ _ _ _ _ he₂ ho₂ =>
      exfalso
      obtain ⟨hsk, -⟩ := HE he₁ he₂ ⟨_, ho₁, e₁⟩ ⟨_, ho₂, c₂'⟩
      rw [gopt_sep_det ho₂ (estop_sepStop c₂'), ← hsk, ← gopt_sep_det ho₁ (estop_sepStop e₁)] at c₂
      cases hl₁; simp [CloseStop] at c₂
    | consMore _ _ _ _ _ _ _ _ _ _ he₂ ho₂ hl₂ ho₂' hr₂ =>
      have e₂ := litStop_of_lit hl₂ (by simp)
      obtain ⟨hsk, rfl⟩ := HE he₁ he₂ ⟨_, ho₁, e₁⟩ ⟨_, ho₂, e₂⟩
      have e := gopt_sep_det ho₁ (estop_sepStop e₁)
      rw [hsk, ← gopt_sep_det ho₂ (estop_sepStop e₂)] at e
      subst e
      cases glit_det hl₁ hl₂
      have e := gopt_sep_det ho₁' (eshape_sepStop (mapEntry_shape (TFlowMapEntries_head hr₁).choose_spec.choose_spec))
      rw [← gopt_sep_det ho₂' (eshape_sepStop (mapEntry_shape (TFlowMapEntries_head hr₂).choose_spec.choose_spec))] at e
      subst e
      have l1 := (tFlowMapEntry_suffix he₁).length_le
      have l2 := (gopt_suffix (fun _ _ => sSeparate_suffix) ho₁).length_le
      have l3 := glit_len hl₁
      have l4 := (gopt_suffix (fun _ _ => sSeparate_suffix) ho₁').length_le
      obtain ⟨rfl, rfl⟩ := IH _ (by omega) hr₁ hr₂ c₁ c₂
      exact ⟨rfl, rfl⟩
    | consEnd _ _ _ _ _ _ _ _ he₂ ho₂ hl₂ ho₂' =>
      exfalso
      have e₂ := litStop_of_lit hl₂ (by simp)
      obtain ⟨hsk, -⟩ := HE he₁ he₂ ⟨_, ho₁, e₁⟩ ⟨_, ho₂, e₂⟩
      have e := gopt_sep_det ho₁ (estop_sepStop e₁)
      rw [hsk, ← gopt_sep_det ho₂ (estop_sepStop e₂)] at e
      subst e
      cases glit_det hl₁ hl₂
      have e := gopt_sep_det ho₁' (eshape_sepStop (mapEntry_shape (TFlowMapEntries_head hr₁).choose_spec.choose_spec))
      rw [← gopt_sep_det ho₂' (estop_sepStop c₂')] at e
      subst e
      exact eshape_not_close (mapEntry_shape (TFlowMapEntries_head hr₁).choose_spec.choose_spec) c₂
  | consEnd _ _ _ _ _ _ _ _ he₁ ho₁ hl₁ ho₁' =>
    have e₁ := litStop_of_lit hl₁ (by simp)
    cases h₂ with
    | single _ _ _ _ _ _ he₂ ho₂ =>
      exfalso
      obtain ⟨hsk, -⟩ := HE he₁ he₂ ⟨_, ho₁, e₁⟩ ⟨_, ho₂, c₂'⟩
      rw [gopt_sep_det ho₂ (estop_sepStop c₂'), ← hsk, ← gopt_sep_det ho₁ (estop_sepStop e₁)] at c₂
      cases hl₁; simp [CloseStop] at c₂
    | consMore _ _ _ _ _ _ _ _ _ _ he₂ ho₂ hl₂ ho₂' hr₂ =>
      exfalso
      have e₂ := litStop_of_lit hl₂ (by simp)
      obtain ⟨hsk, -⟩ := HE he₁ he₂ ⟨_, ho₁, e₁⟩ ⟨_, ho₂, e₂⟩
      have e := gopt_sep_det ho₁ (estop_sepStop e₁)
      rw [hsk, ← gopt_sep_det ho₂ (estop_sepStop e₂)] at e
      subst e
      cases glit_det hl₁ hl₂
      have e := gopt_sep_det ho₂' (eshape_sepStop (mapEntry_shape (TFlowMapEntries_head hr₂).choose_spec.choose_spec))
      rw [← gopt_sep_det ho₁' (estop_sepStop c₁')] at e
      subst e
      exact eshape_not_close (mapEntry_shape (TFlowMapEntries_head hr₂).choose_spec.choose_spec) c₁
    | consEnd _ _ _ _ _ _ _ _ he₂ ho₂ hl₂ ho₂' =>
      have e₂ := litStop_of_lit hl₂ (by simp)
      obtain ⟨hsk, rfl⟩ := HE he₁ he₂ ⟨_, ho₁, e₁⟩ ⟨_, ho₂, e₂⟩
      have e := gopt_sep_det ho₁ (estop_sepStop e₁)
      rw [hsk, ← gopt_sep_det ho₂ (estop_sepStop e₂)] at e
      subst e
      cases glit_det hl₁ hl₂
      rw [gopt_sep_det ho₁' (estop_sepStop c₁'), gopt_sep_det ho₂' (estop_sepStop c₂')]
      exact ⟨rfl, rfl⟩


lemma flowCtx_inFlowCtx (c : YamlContext) : FlowCtx (inFlowCtx c) := by
  cases c <;> first | decide | simp [inFlowCtx, FlowCtx]

lemma lit_eq {a a' : Char} {s b b' : SurfPos} (h : GLit a s b) (h' : GLit a' s b') : a = a' := by
  cases h; cases h'; rfl

lemma lit_sepStop {ch : Char} {a b : SurfPos} (h : GLit ch a b) (hw : ¬ (ch = ' ' ∨ ch = '\t'))
    (hb : ¬ (ch = '\n' ∨ ch = '\r')) (hs : ch ≠ '#') : SepStop a := by
  cases h; simp [SepStop, hw, hb, hs]

lemma seq_det {n : Nat} {c : YamlContext} {s : SurfPos}
    (IHE : ∀ s', s'.chars.length < s.chars.length → SeqEntriesDet n (inFlowCtx c) s') : SeqDet n c s := by
  intro m₁ m₂ ev₁ ev₂ h₁ h₂
  cases h₁ with
  | empty _ _ _ _ _ _ hl₁ ho₁ hr₁ =>
    cases h₂ with
    | empty _ _ _ _ _ _ hl₂ ho₂ hr₂ =>
      cases glit_det hl₁ hl₂
      have e := gopt_sep_det ho₁ (lit_sepStop hr₁ (by decide) (by decide) (by decide))
      rw [← gopt_sep_det ho₂ (lit_sepStop hr₂ (by decide) (by decide) (by decide))] at e
      subst e
      cases glit_det hr₁ hr₂
      exact ⟨rfl, rfl⟩
    | nonempty _ _ _ _ _ _ _ _ hl₂ ho₂ he₂ hr₂ =>
      exfalso
      cases glit_det hl₁ hl₂
      have hsh := seqEntry_shape (TFlowSeqEntries_head he₂).choose_spec.choose_spec
      have e := gopt_sep_det ho₁ (lit_sepStop hr₁ (by decide) (by decide) (by decide))
      rw [← gopt_sep_det ho₂ (eshape_sepStop hsh)] at e
      subst e
      exact eshape_not_close hsh (by cases hr₁; simp [CloseStop])
  | nonempty _ _ _ _ _ _ _ _ hl₁ ho₁ he₁ hr₁ =>
    have hsh₁ := seqEntry_shape (TFlowSeqEntries_head he₁).choose_spec.choose_spec
    cases h₂ with
    | empty _ _ _ _ _ _ hl₂ ho₂ hr₂ =>
      exfalso
      cases glit_det hl₁ hl₂
      have e := gopt_sep_det ho₂ (lit_sepStop hr₂ (by decide) (by decide) (by decide))
      rw [← gopt_sep_det ho₁ (eshape_sepStop hsh₁)] at e
      subst e
      exact eshape_not_close hsh₁ (by cases hr₂; simp [CloseStop])
    | nonempty _ _ _ _ _ _ _ _ hl₂ ho₂ he₂ hr₂ =>
      cases glit_det hl₁ hl₂
      have hsh₂ := seqEntry_shape (TFlowSeqEntries_head he₂).choose_spec.choose_spec
      have e := gopt_sep_det ho₁ (eshape_sepStop hsh₁)
      rw [← gopt_sep_det ho₂ (eshape_sepStop hsh₂)] at e
      subst e
      have l1 := glit_len hl₁
      have l2 := (gopt_suffix (fun _ _ => sSeparate_suffix) ho₁).length_le
      obtain ⟨rfl, rfl⟩ := IHE _ (by omega) he₁ he₂ (by cases hr₁; simp [CloseStop])
        (by cases hr₂; simp [CloseStop])
      cases glit_det hr₁ hr₂
      exact ⟨rfl, rfl⟩

lemma map_det {n : Nat} {c : YamlContext} {s : SurfPos}
    (IHE : ∀ s', s'.chars.length < s.chars.length → MapEntriesDet n (inFlowCtx c) s') : MapDet n c s := by
  intro m₁ m₂ ev₁ ev₂ h₁ h₂
  cases h₁ with
  | empty _ _ _ _ _ _ hl₁ ho₁ hr₁ =>
    cases h₂ with
    | empty _ _ _ _ _ _ hl₂ ho₂ hr₂ =>
      cases glit_det hl₁ hl₂
      have e := gopt_sep_det ho₁ (lit_sepStop hr₁ (by decide) (by decide) (by decide))
      rw [← gopt_sep_det ho₂ (lit_sepStop hr₂ (by decide) (by decide) (by decide))] at e
      subst e
      cases glit_det hr₁ hr₂
      exact ⟨rfl, rfl⟩
    | nonempty _ _ _ _ _ _ _ _ hl₂ ho₂ he₂ hr₂ =>
      exfalso
      cases glit_det hl₁ hl₂
      have hsh := mapEntry_shape (TFlowMapEntries_head he₂).choose_spec.choose_spec
      have e := gopt_sep_det ho₁ (lit_sepStop hr₁ (by decide) (by decide) (by decide))
      rw [← gopt_sep_det ho₂ (eshape_sepStop hsh)] at e
      subst e
      exact eshape_not_close hsh (by cases hr₁; simp [CloseStop])
  | nonempty _ _ _ _ _ _ _ _ hl₁ ho₁ he₁ hr₁ =>
    have hsh₁ := mapEntry_shape (TFlowMapEntries_head he₁).choose_spec.choose_spec
    cases h₂ with
    | empty _ _ _ _ _ _ hl₂ ho₂ hr₂ =>
      exfalso
      cases glit_det hl₁ hl₂
      have e := gopt_sep_det ho₂ (lit_sepStop hr₂ (by decide) (by decide) (by decide))
      rw [← gopt_sep_det ho₁ (eshape_sepStop hsh₁)] at e
      subst e
      exact eshape_not_close hsh₁ (by cases hr₂; simp [CloseStop])
    | nonempty _ _ _ _ _ _ _ _ hl₂ ho₂ he₂ hr₂ =>
      cases glit_det hl₁ hl₂
      have hsh₂ := mapEntry_shape (TFlowMapEntries_head he₂).choose_spec.choose_spec
      have e := gopt_sep_det ho₁ (eshape_sepStop hsh₁)
      rw [← gopt_sep_det ho₂ (eshape_sepStop hsh₂)] at e
      subst e
      have l1 := glit_len hl₁
      have l2 := (gopt_suffix (fun _ _ => sSeparate_suffix) ho₁).length_le
      obtain ⟨rfl, rfl⟩ := IHE _ (by omega) he₁ he₂ (by cases hr₁; simp [CloseStop])
        (by cases hr₂; simp [CloseStop])
      cases glit_det hr₁ hr₂
      exact ⟨rfl, rfl⟩

/-! ## Content and node determinism -/

lemma plain_head {n : Nat} {c : YamlContext} {a m : SurfPos} (h : SNsPlain n c a m) :
    ∃ ch rest col, a = ⟨ch :: rest, col⟩ ∧ (¬ isIndicatorProp ch ∨ ch = '-' ∨ ch = ':' ∨ ch = '?') := by
  obtain ⟨a₁, hf, -⟩ := plain_steps h
  cases hf with
  | nonIndicator ch rest col hs hi => exact ⟨ch, rest, col, rfl, Or.inl hi⟩
  | dashSafe nx rest col hs => exact ⟨'-', _, _, rfl, Or.inr (Or.inl rfl)⟩
  | colonSafe nx rest col hs => exact ⟨':', _, _, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
  | questionSafe nx rest col hs => exact ⟨'?', _, _, rfl, Or.inr (Or.inr (Or.inr rfl))⟩

lemma plain_not_lit {n : Nat} {c : YamlContext} {ch : Char} {a m b : SurfPos} (h : SNsPlain n c a m)
    (hl : GLit ch a b) (hi : isIndicatorProp ch) (hne : ch ≠ '-' ∧ ch ≠ ':' ∧ ch ≠ '?') : False := by
  obtain ⟨ch', rest, col, rfl, hd⟩ := plain_head h
  cases hl
  rcases hd with hd | rfl | rfl | rfl
  · exact hd hi
  · exact hne.1 rfl
  · exact hne.2.1 rfl
  · exact hne.2.2 rfl

lemma seq_lit {n : Nat} {c : YamlContext} {s m : SurfPos} {ev : List Event}
    (h : TFlowSequence n c s m ev) : ∃ b, GLit '[' s b := by
  cases h with
  | empty _ _ _ _ _ _ hl _ _ => exact ⟨_, hl⟩
  | nonempty _ _ _ _ _ _ _ _ hl _ _ _ => exact ⟨_, hl⟩

lemma map_lit {n : Nat} {c : YamlContext} {s m : SurfPos} {ev : List Event}
    (h : TFlowMapping n c s m ev) : ∃ b, GLit '{' s b := by
  cases h with
  | empty _ _ _ _ _ _ hl _ _ => exact ⟨_, hl⟩
  | nonempty _ _ _ _ _ _ _ _ hl _ _ _ => exact ⟨_, hl⟩

lemma sq_lit {n : Nat} {c : YamlContext} {s m : SurfPos} (h : SCSingleQuoted n c s m) :
    ∃ b, GLit '\'' s b := by
  cases h with
  | mk => exact ⟨_, ‹GLit '\'' s _›⟩

lemma dq_lit {n : Nat} {c : YamlContext} {s m : SurfPos} (h : SCDoubleQuoted n c s m) :
    ∃ b, GLit '"' s b := by
  cases h with
  | mk => exact ⟨_, ‹GLit '"' s _›⟩

lemma content_det {n : Nat} {c : YamlContext} {s : SurfPos} (HS : SeqDet n c s) (HM : MapDet n c s) :
    ContentDet n c s := by
  intro m₁ m₂ ev₁ ev₂ h₁ h₂ hf
  cases h₁ with
  | plain _ _ _ _ hp₁ =>
    cases h₂ with
    | plain _ _ _ _ hp₂ =>
      rcases hf with rfl | ⟨hc, f₁, f₂⟩
      · exact ⟨rfl, rfl⟩
      · cases plain_det hc hp₁ hp₂ f₁ f₂; exact ⟨rfl, rfl⟩
    | flowSeq _ _ _ _ _ hx =>
      exact (plain_not_lit hp₁ (seq_lit hx).choose_spec (by decide) (by decide)).elim
    | flowMap _ _ _ _ _ hx =>
      exact (plain_not_lit hp₁ (map_lit hx).choose_spec (by decide) (by decide)).elim
    | singleQ _ _ _ _ hx =>
      exact (plain_not_lit hp₁ (sq_lit hx).choose_spec (by decide) (by decide)).elim
    | doubleQ _ _ _ _ hx =>
      exact (plain_not_lit hp₁ (dq_lit hx).choose_spec (by decide) (by decide)).elim
  | flowSeq _ _ _ _ _ hx₁ =>
    cases h₂ with
    | plain _ _ _ _ hp₂ =>
      exact (plain_not_lit hp₂ (seq_lit hx₁).choose_spec (by decide) (by decide)).elim
    | flowSeq _ _ _ _ _ hx₂ => obtain ⟨rfl, rfl⟩ := HS hx₁ hx₂; exact ⟨rfl, rfl⟩
    | flowMap _ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (seq_lit hx₁).choose_spec (map_lit hx₂).choose_spec) (by decide)
    | singleQ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (seq_lit hx₁).choose_spec (sq_lit hx₂).choose_spec) (by decide)
    | doubleQ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (seq_lit hx₁).choose_spec (dq_lit hx₂).choose_spec) (by decide)
  | flowMap _ _ _ _ _ hx₁ =>
    cases h₂ with
    | plain _ _ _ _ hp₂ =>
      exact (plain_not_lit hp₂ (map_lit hx₁).choose_spec (by decide) (by decide)).elim
    | flowSeq _ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (map_lit hx₁).choose_spec (seq_lit hx₂).choose_spec) (by decide)
    | flowMap _ _ _ _ _ hx₂ => obtain ⟨rfl, rfl⟩ := HM hx₁ hx₂; exact ⟨rfl, rfl⟩
    | singleQ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (map_lit hx₁).choose_spec (sq_lit hx₂).choose_spec) (by decide)
    | doubleQ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (map_lit hx₁).choose_spec (dq_lit hx₂).choose_spec) (by decide)
  | singleQ _ _ _ _ hx₁ =>
    cases h₂ with
    | plain _ _ _ _ hp₂ =>
      exact (plain_not_lit hp₂ (sq_lit hx₁).choose_spec (by decide) (by decide)).elim
    | flowSeq _ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (sq_lit hx₁).choose_spec (seq_lit hx₂).choose_spec) (by decide)
    | flowMap _ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (sq_lit hx₁).choose_spec (map_lit hx₂).choose_spec) (by decide)
    | singleQ _ _ _ _ hx₂ =>
      rcases hf with rfl | ⟨hc, f₁, f₂⟩
      · exact ⟨rfl, rfl⟩
      · cases sq_det hx₁ hx₂ (nstop_notQuote (nstop_of_fstop f₁)) (nstop_notQuote (nstop_of_fstop f₂))
        exact ⟨rfl, rfl⟩
    | doubleQ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (sq_lit hx₁).choose_spec (dq_lit hx₂).choose_spec) (by decide)
  | doubleQ _ _ _ _ hx₁ =>
    cases h₂ with
    | plain _ _ _ _ hp₂ =>
      exact (plain_not_lit hp₂ (dq_lit hx₁).choose_spec (by decide) (by decide)).elim
    | flowSeq _ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (dq_lit hx₁).choose_spec (seq_lit hx₂).choose_spec) (by decide)
    | flowMap _ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (dq_lit hx₁).choose_spec (map_lit hx₂).choose_spec) (by decide)
    | singleQ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (dq_lit hx₁).choose_spec (sq_lit hx₂).choose_spec) (by decide)
    | doubleQ _ _ _ _ hx₂ => cases dq_det hx₁ hx₂; exact ⟨rfl, rfl⟩

lemma contentHead_indicator {c : YamlContext} {ch : Char} {r : List Char} {col : Nat}
    (hi : isIndicatorProp ch) (hne : ch ≠ '-' ∧ ch ≠ ':' ∧ ch ≠ '?')
    (hq : ch ≠ '[' ∧ ch ≠ '{' ∧ ch ≠ '"' ∧ ch ≠ '\'') (h : ContentHead c ⟨ch :: r, col⟩) : False := by
  simp only [ContentHead] at h
  rcases h with ⟨-, h⟩ | ⟨h, -⟩ | h | h | h | h
  · exact h hi
  · rcases h with h | h | h
    · exact hne.1 h
    · exact hne.2.1 h
    · exact hne.2.2 h
  · exact hq.1 h
  · exact hq.2.1 h
  · exact hq.2.2.1 h
  · exact hq.2.2.2 h

lemma contentHead_not_star {c : YamlContext} {r : List Char} {col : Nat}
    (h : ContentHead c ⟨'*' :: r, col⟩) : False :=
  contentHead_indicator (by decide) (by decide) (by decide) h

lemma contentHead_not_bang {c : YamlContext} {r : List Char} {col : Nat}
    (h : ContentHead c ⟨'!' :: r, col⟩) : False :=
  contentHead_indicator (by decide) (by decide) (by decide) h

lemma contentHead_not_amp {c : YamlContext} {r : List Char} {col : Nat}
    (h : ContentHead c ⟨'&' :: r, col⟩) : False :=
  contentHead_indicator (by decide) (by decide) (by decide) h

lemma contentHead_props {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (hp : TCNsProperties n c a m ev) (hc : ContentHead c a) : False := by
  rcases props_head hp with ⟨r, cl, rfl⟩ | ⟨r, cl, rfl⟩
  · exact contentHead_not_bang hc
  · exact contentHead_not_amp hc

lemma alias_props {n : Nat} {c : YamlContext} {a m m' : SurfPos} {ev : List Event}
    (ha : SCNsAliasNode a m) (hp : TCNsProperties n c a m' ev) : False := by
  obtain ⟨r, cl, rfl⟩ := alias_head ha
  rcases props_head hp with ⟨r', cl', h⟩ | ⟨r', cl', h⟩ <;> cases h

lemma alias_contentHead {c : YamlContext} {a m : SurfPos} (ha : SCNsAliasNode a m)
    (hc : ContentHead c a) : False := by
  obtain ⟨r, cl, rfl⟩ := alias_head ha
  exact contentHead_not_star hc

lemma jsonContent_lit {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TCFlowJsonContent n c a m ev) : ∃ ch b, GLit ch a b ∧ (ch = '[' ∨ ch = '{' ∨ ch = '"' ∨ ch = '\'') := by
  cases h with
  | flowSeq _ _ _ _ _ hx => exact ⟨_, _, (seq_lit hx).choose_spec, by simp⟩
  | flowMap _ _ _ _ _ hx => exact ⟨_, _, (map_lit hx).choose_spec, by simp⟩
  | singleQ _ _ _ _ hx => exact ⟨_, _, (sq_lit hx).choose_spec, by simp⟩
  | doubleQ _ _ _ _ hx => exact ⟨_, _, (dq_lit hx).choose_spec, by simp⟩

lemma jsonContent_not_cstop {n : Nat} {c : YamlContext} {a m : SurfPos} {ev : List Event}
    (h : TCFlowJsonContent n c a m ev) (hs : CStop a) : False := by
  obtain ⟨ch, b, hl, hch⟩ := jsonContent_lit h
  cases hl
  simp only [CStop] at hs
  rcases hch with rfl | rfl | rfl | rfl <;> simp at hs

lemma jsonContent_det {n : Nat} {c : YamlContext} {s : SurfPos} (HS : SeqDet n c s) (HM : MapDet n c s)
    {m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event} (h₁ : TCFlowJsonContent n c s m₁ ev₁)
    (h₂ : TCFlowJsonContent n c s m₂ ev₂) (hf : m₁ = m₂ ∨ (NStop n c m₁ ∧ NStop n c m₂)) :
    m₁ = m₂ ∧ ev₁ = ev₂ := by
  cases h₁ with
  | flowSeq _ _ _ _ _ hx₁ =>
    cases h₂ with
    | flowSeq _ _ _ _ _ hx₂ => obtain ⟨rfl, rfl⟩ := HS hx₁ hx₂; exact ⟨rfl, rfl⟩
    | flowMap _ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (seq_lit hx₁).choose_spec (map_lit hx₂).choose_spec) (by decide)
    | singleQ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (seq_lit hx₁).choose_spec (sq_lit hx₂).choose_spec) (by decide)
    | doubleQ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (seq_lit hx₁).choose_spec (dq_lit hx₂).choose_spec) (by decide)
  | flowMap _ _ _ _ _ hx₁ =>
    cases h₂ with
    | flowSeq _ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (map_lit hx₁).choose_spec (seq_lit hx₂).choose_spec) (by decide)
    | flowMap _ _ _ _ _ hx₂ => obtain ⟨rfl, rfl⟩ := HM hx₁ hx₂; exact ⟨rfl, rfl⟩
    | singleQ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (map_lit hx₁).choose_spec (sq_lit hx₂).choose_spec) (by decide)
    | doubleQ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (map_lit hx₁).choose_spec (dq_lit hx₂).choose_spec) (by decide)
  | singleQ _ _ _ _ hx₁ =>
    cases h₂ with
    | flowSeq _ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (sq_lit hx₁).choose_spec (seq_lit hx₂).choose_spec) (by decide)
    | flowMap _ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (sq_lit hx₁).choose_spec (map_lit hx₂).choose_spec) (by decide)
    | singleQ _ _ _ _ hx₂ =>
      rcases hf with rfl | ⟨f₁, f₂⟩
      · exact ⟨rfl, rfl⟩
      · cases sq_det hx₁ hx₂ (nstop_notQuote f₁) (nstop_notQuote f₂); exact ⟨rfl, rfl⟩
    | doubleQ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (sq_lit hx₁).choose_spec (dq_lit hx₂).choose_spec) (by decide)
  | doubleQ _ _ _ _ hx₁ =>
    cases h₂ with
    | flowSeq _ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (dq_lit hx₁).choose_spec (seq_lit hx₂).choose_spec) (by decide)
    | flowMap _ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (dq_lit hx₁).choose_spec (map_lit hx₂).choose_spec) (by decide)
    | singleQ _ _ _ _ hx₂ =>
      exact absurd (lit_eq (dq_lit hx₁).choose_spec (sq_lit hx₂).choose_spec) (by decide)
    | doubleQ _ _ _ _ hx₂ => cases dq_det hx₁ hx₂; exact ⟨rfl, rfl⟩

lemma content_json_det {n : Nat} {c : YamlContext} {s : SurfPos} (HS : SeqDet n c s) (HM : MapDet n c s)
    {m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event} (h₁ : TFlowContent n c s m₁ ev₁)
    (h₂ : TCFlowJsonContent n c s m₂ ev₂) (f₁ : NStop n c m₁) (f₂ : NStop n c m₂) :
    m₁ = m₂ ∧ ev₁ = ev₂ := by
  cases h₁ with
  | plain _ _ _ _ hp₁ =>
    exfalso
    obtain ⟨ch, b, hl, hch⟩ := jsonContent_lit h₂
    rcases hch with rfl | rfl | rfl | rfl <;> exact plain_not_lit hp₁ hl (by decide) (by decide)
  | flowSeq _ _ _ _ _ hx₁ => exact jsonContent_det HS HM (.flowSeq _ _ _ _ _ hx₁) h₂ (Or.inr ⟨f₁, f₂⟩)
  | flowMap _ _ _ _ _ hx₁ => exact jsonContent_det HS HM (.flowMap _ _ _ _ _ hx₁) h₂ (Or.inr ⟨f₁, f₂⟩)
  | singleQ _ _ _ _ hx₁ => exact jsonContent_det HS HM (.singleQ _ _ _ _ hx₁) h₂ (Or.inr ⟨f₁, f₂⟩)
  | doubleQ _ _ _ _ hx₁ => exact jsonContent_det HS HM (.doubleQ _ _ _ _ hx₁) h₂ (Or.inr ⟨f₁, f₂⟩)

lemma props_pstop_content {n : Nat} {c : YamlContext} {s s₁ s₂ : SurfPos} {ev : List Event}
    (hp : TCNsProperties n c s s₁ ev) (hs : SSeparate n c s₁ s₂) (hch : ContentHead c s₂) :
    PStop n c s₁ :=
  pstop_of_sep hs (by have := props_col hp; omega) (contentHead_sepStop hch) (contentHead_notProp hch)

lemma node_det {n : Nat} {c : YamlContext} {s : SurfPos} (HC0 : ContentDet n c s)
    (IHC : ∀ s', s'.chars.length < s.chars.length → ContentDet n c s') : NodeDet n c s := by
  intro m₁ m₂ ev₁ ev₂ h₁ h₂ hf
  cases h₁ with
  | alias _ _ _ _ _ ha₁ =>
    cases h₂ with
    | alias _ _ _ _ _ ha₂ =>
      cases alias_det ha₁.1 ha₂.1
      rw [ha₁.2, ha₂.2]
      exact ⟨rfl, rfl⟩
    | content _ _ _ _ _ hc₂ => exact (alias_contentHead ha₁.1 (content_head hc₂)).elim
    | propsContent _ _ _ _ _ _ _ _ hp₂ _ _ => exact (alias_props ha₁.1 hp₂).elim
    | propsEmpty _ _ _ _ _ hp₂ => exact (alias_props ha₁.1 hp₂).elim
  | content _ _ _ _ _ hc₁ =>
    cases h₂ with
    | alias _ _ _ _ _ ha₂ => exact (alias_contentHead ha₂.1 (content_head hc₁)).elim
    | content _ _ _ _ _ hc₂ => exact HC0 hc₁ hc₂ hf
    | propsContent _ _ _ _ _ _ _ _ hp₂ _ _ => exact (contentHead_props hp₂ (content_head hc₁)).elim
    | propsEmpty _ _ _ _ _ hp₂ => exact (contentHead_props hp₂ (content_head hc₁)).elim
  | propsContent _ _ _ _ _ _ _ _ hp₁ hs₁ hc₁ =>
    cases h₂ with
    | alias _ _ _ _ _ ha₂ => exact (alias_props ha₂.1 hp₁).elim
    | content _ _ _ _ _ hc₂ => exact (contentHead_props hp₁ (content_head hc₂)).elim
    | propsContent _ _ _ _ _ _ _ _ hp₂ hs₂ hc₂ =>
      obtain ⟨rfl, rfl⟩ := props_det hp₁ hp₂ (props_pstop_content hp₁ hs₁ (content_head hc₁))
        (props_pstop_content hp₂ hs₂ (content_head hc₂))
      have e := sep_det hs₁ (contentHead_sepStop (content_head hc₁))
      rw [← sep_det hs₂ (contentHead_sepStop (content_head hc₂))] at e
      subst e
      obtain ⟨rfl, rfl⟩ := IHC _ (by have := props_len hp₁; have := (sSeparate_suffix hs₁).length_le; omega)
        hc₁ hc₂ hf
      exact ⟨rfl, rfl⟩
    | propsEmpty _ _ _ _ _ hp₂ =>
      exfalso
      rcases hf with rfl | ⟨hc, f₁, f₂⟩
      · exact props_ext hp₁ hs₁ (contentHead_sepStop (content_head hc₁))
          (contentHead_notProp (content_head hc₁)) hp₂ (content_len hc₁)
      · obtain ⟨rfl, -⟩ := props_det hp₁ hp₂ (props_pstop_content hp₁ hs₁ (content_head hc₁))
          (pstop_of_fstop f₂)
        obtain ⟨t, ho, hl⟩ := f₂
        rw [gopt_sep_det ho (litStop_sepStop hl), ← sep_det hs₁ (contentHead_sepStop (content_head hc₁))] at hl
        exact contentHead_not_litStop hc (content_head hc₁) hl
  | propsEmpty _ _ _ _ _ hp₁ =>
    cases h₂ with
    | alias _ _ _ _ _ ha₂ => exact (alias_props ha₂.1 hp₁).elim
    | content _ _ _ _ _ hc₂ => exact (contentHead_props hp₁ (content_head hc₂)).elim
    | propsContent _ _ _ _ _ _ _ _ hp₂ hs₂ hc₂ =>
      exfalso
      rcases hf with rfl | ⟨hc, f₁, f₂⟩
      · exact props_ext hp₂ hs₂ (contentHead_sepStop (content_head hc₂))
          (contentHead_notProp (content_head hc₂)) hp₁ (content_len hc₂)
      · obtain ⟨rfl, -⟩ := props_det hp₂ hp₁ (props_pstop_content hp₂ hs₂ (content_head hc₂))
          (pstop_of_fstop f₁)
        obtain ⟨t, ho, hl⟩ := f₁
        rw [gopt_sep_det ho (litStop_sepStop hl), ← sep_det hs₂ (contentHead_sepStop (content_head hc₂))] at hl
        exact contentHead_not_litStop hc (content_head hc₂) hl
    | propsEmpty _ _ _ _ _ hp₂ =>
      rcases hf with rfl | ⟨hc, f₁, f₂⟩
      · exact ⟨rfl, props_det_eq hp₁ hp₂⟩
      · exact props_det hp₁ hp₂ (pstop_of_fstop f₁) (pstop_of_fstop f₂)

lemma json_det {n : Nat} {c : YamlContext} {s : SurfPos} (HS : SeqDet n c s) (HM : MapDet n c s)
    (IHS : ∀ s', s'.chars.length < s.chars.length → SeqDet n c s')
    (IHM : ∀ s', s'.chars.length < s.chars.length → MapDet n c s') : JsonDet n c s := by
  intro m₁ m₂ ev₁ ev₂ h₁ h₂ hf
  cases h₁ with
  | content _ _ _ _ _ hc₁ =>
    cases h₂ with
    | content _ _ _ _ _ hc₂ => exact jsonContent_det HS HM hc₁ hc₂ hf
    | propsContent _ _ _ _ _ _ _ _ hp₂ _ _ => exact (contentHead_props hp₂ (jsonContent_head hc₁)).elim
  | propsContent _ _ _ _ _ _ _ _ hp₁ hs₁ hc₁ =>
    cases h₂ with
    | content _ _ _ _ _ hc₂ => exact (contentHead_props hp₁ (jsonContent_head hc₂)).elim
    | propsContent _ _ _ _ _ _ _ _ hp₂ hs₂ hc₂ =>
      obtain ⟨rfl, rfl⟩ := props_det hp₁ hp₂ (props_pstop_content hp₁ hs₁ (jsonContent_head hc₁))
        (props_pstop_content hp₂ hs₂ (jsonContent_head hc₂))
      have e := sep_det hs₁ (contentHead_sepStop (jsonContent_head hc₁))
      rw [← sep_det hs₂ (contentHead_sepStop (jsonContent_head hc₂))] at e
      subst e
      have l1 := props_len hp₁
      have l2 := (sSeparate_suffix hs₁).length_le
      obtain ⟨rfl, rfl⟩ := jsonContent_det (IHS _ (by omega)) (IHM _ (by omega)) hc₁ hc₂ hf
      exact ⟨rfl, rfl⟩

lemma cross_det {n : Nat} {c : YamlContext} {s : SurfPos} (HS : SeqDet n c s) (HM : MapDet n c s)
    (IHS : ∀ s', s'.chars.length < s.chars.length → SeqDet n c s')
    (IHM : ∀ s', s'.chars.length < s.chars.length → MapDet n c s') : CrossDet n c s := by
  intro m₁ m₂ ev₁ ev₂ h₁ h₂ f₁ f₂
  cases h₁ with
  | alias _ _ _ _ _ ha₁ =>
    cases h₂ with
    | content _ _ _ _ _ hc₂ => exact (alias_contentHead ha₁.1 (jsonContent_head hc₂)).elim
    | propsContent _ _ _ _ _ _ _ _ hp₂ _ _ => exact (alias_props ha₁.1 hp₂).elim
  | content _ _ _ _ _ hc₁ =>
    cases h₂ with
    | content _ _ _ _ _ hc₂ => exact content_json_det HS HM hc₁ hc₂ f₁ f₂
    | propsContent _ _ _ _ _ _ _ _ hp₂ _ _ => exact (contentHead_props hp₂ (content_head hc₁)).elim
  | propsContent _ _ _ _ _ _ _ _ hp₁ hs₁ hc₁ =>
    cases h₂ with
    | content _ _ _ _ _ hc₂ => exact (contentHead_props hp₁ (jsonContent_head hc₂)).elim
    | propsContent _ _ _ _ _ _ _ _ hp₂ hs₂ hc₂ =>
      obtain ⟨rfl, rfl⟩ := props_det hp₁ hp₂ (props_pstop_content hp₁ hs₁ (content_head hc₁))
        (props_pstop_content hp₂ hs₂ (jsonContent_head hc₂))
      have e := sep_det hs₁ (contentHead_sepStop (content_head hc₁))
      rw [← sep_det hs₂ (contentHead_sepStop (jsonContent_head hc₂))] at e
      subst e
      have l1 := props_len hp₁
      have l2 := (sSeparate_suffix hs₁).length_le
      obtain ⟨rfl, rfl⟩ := content_json_det (IHS _ (by omega)) (IHM _ (by omega)) hc₁ hc₂ f₁ f₂
      exact ⟨rfl, rfl⟩
  | propsEmpty _ _ _ _ _ hp₁ =>
    cases h₂ with
    | content _ _ _ _ _ hc₂ => exact (contentHead_props hp₁ (jsonContent_head hc₂)).elim
    | propsContent _ _ _ _ _ _ _ _ hp₂ hs₂ hc₂ =>
      exfalso
      obtain ⟨rfl, -⟩ := props_det hp₁ hp₂ (pstop_of_nstop f₁)
        (props_pstop_content hp₂ hs₂ (jsonContent_head hc₂))
      obtain ⟨t, ho, hl⟩ := f₁
      rw [gopt_sep_det ho (cstop_sepStop hl), ← sep_det hs₂ (contentHead_sepStop (jsonContent_head hc₂))] at hl
      exact jsonContent_not_cstop hc₂ hl

/-! ## The induction and the public uniqueness lemmas -/

/-- Every determinism predicate of the flow fragment at one start position. -/
def AllDet (n : Nat) (s : SurfPos) : Prop :=
  ∀ c, (NodeDet n c s ∧ ContentDet n c s ∧ JsonDet n c s ∧ CrossDet n c s ∧ SeqDet n c s ∧ MapDet n c s) ∧
    (FlowCtx c → SeqEntriesDet n c s ∧ MapEntriesDet n c s)

lemma allDet_step {n : Nat} {s : SurfPos}
    (IHlt : ∀ s' : SurfPos, s'.chars.length < s.chars.length → AllDet n s') : AllDet n s := by
  intro c
  have HSE : ∀ s', s'.chars.length < s.chars.length → SeqEntriesDet n (inFlowCtx c) s' :=
    fun s' h => ((IHlt s' h (inFlowCtx c)).2 (flowCtx_inFlowCtx c)).1
  have HME : ∀ s', s'.chars.length < s.chars.length → MapEntriesDet n (inFlowCtx c) s' :=
    fun s' h => ((IHlt s' h (inFlowCtx c)).2 (flowCtx_inFlowCtx c)).2
  have HS : SeqDet n c s := seq_det HSE
  have HM : MapDet n c s := map_det HME
  have HC : ContentDet n c s := content_det HS HM
  have IHC : ∀ s', s'.chars.length < s.chars.length → ContentDet n c s' :=
    fun s' h => ((IHlt s' h c).1).2.1
  have HN : NodeDet n c s := node_det HC IHC
  have IHS : ∀ s', s'.chars.length < s.chars.length → SeqDet n c s' :=
    fun s' h => ((IHlt s' h c).1).2.2.2.2.1
  have IHM : ∀ s', s'.chars.length < s.chars.length → MapDet n c s' :=
    fun s' h => ((IHlt s' h c).1).2.2.2.2.2
  have HJ : JsonDet n c s := json_det HS HM IHS IHM
  have HX : CrossDet n c s := cross_det HS HM IHS IHM
  have HNlt : ∀ s', s'.chars.length < s.chars.length → NodeDet n c s' :=
    fun s' h => ((IHlt s' h c).1).1
  have HJlt : ∀ s', s'.chars.length < s.chars.length → JsonDet n c s' :=
    fun s' h => ((IHlt s' h c).1).2.2.1
  have HXlt : ∀ s', s'.chars.length < s.chars.length → CrossDet n c s' :=
    fun s' h => ((IHlt s' h c).1).2.2.2.1
  refine ⟨⟨HN, HC, HJ, HX, HS, HM⟩, fun hc => ?_⟩
  have HE1 : ∀ {m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}, TFlowSeqEntry n c s m₁ ev₁ →
      TFlowSeqEntry n c s m₂ ev₂ → EFollow n c m₁ → EFollow n c m₂ →
      skipSep m₁ = skipSep m₂ ∧ ev₁ = ev₂ :=
    fun h₁ h₂ f₁ f₂ =>
      eshape_det hc HN HJ HX HNlt HJlt HXlt (seqEntry_shape h₁) (seqEntry_shape h₂) f₁ f₂
  have HE2 : ∀ {m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}, TFlowMapEntry n c s m₁ ev₁ →
      TFlowMapEntry n c s m₂ ev₂ → EFollow n c m₁ → EFollow n c m₂ →
      skipSep m₁ = skipSep m₂ ∧ ev₁ = ev₂ :=
    fun h₁ h₂ f₁ f₂ =>
      eshape_det hc HN HJ HX HNlt HJlt HXlt (mapEntry_shape h₁) (mapEntry_shape h₂) f₁ f₂
  have IHSE : ∀ s', s'.chars.length < s.chars.length → SeqEntriesDet n c s' :=
    fun s' h => ((IHlt s' h c).2 hc).1
  have IHME : ∀ s', s'.chars.length < s.chars.length → MapEntriesDet n c s' :=
    fun s' h => ((IHlt s' h c).2 hc).2
  exact ⟨TFlowSeqEntries_det HE1 IHSE, TFlowMapEntries_det HE2 IHME⟩

lemma allDet (n : Nat) : ∀ N (s : SurfPos), s.chars.length ≤ N → AllDet n s := by
  intro N
  induction N with
  | zero =>
    intro s hs
    exact allDet_step (fun s' h => absurd (Nat.lt_of_lt_of_le h hs) (Nat.not_lt_zero _))
  | succ N IH =>
    intro s hs
    exact allDet_step (fun s' h => IH s' (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le h hs)))

/-- Span determinism of a flow node under the flow follow-set. -/
lemma tFlowNode_det {n : Nat} {c : YamlContext} {s m₁ m₂ : SurfPos} {ev₁ ev₂ : List Event}
    (h₁ : TFlowNode n c s m₁ ev₁) (h₂ : TFlowNode n c s m₂ ev₂) (hf : Follow n c m₁ m₂) :
    m₁ = m₂ ∧ ev₁ = ev₂ :=
  (allDet n _ s (Nat.le_refl _) c).1.1 h₁ h₂ hf

lemma tFlowNode_unique {n : Nat} {c : YamlContext} {s s' : SurfPos} {ev₁ ev₂ : List Event} :
    TFlowNode n c s s' ev₁ → TFlowNode n c s s' ev₂ → ev₁ = ev₂ :=
  fun h₁ h₂ => (tFlowNode_det h₁ h₂ (Or.inl rfl)).2

lemma tFlowContent_unique {n : Nat} {c : YamlContext} {s s' : SurfPos} {ev₁ ev₂ : List Event} :
    TFlowContent n c s s' ev₁ → TFlowContent n c s s' ev₂ → ev₁ = ev₂ :=
  fun h₁ h₂ => ((allDet n _ s (Nat.le_refl _) c).1.2.1 h₁ h₂ (Or.inl rfl)).2

lemma tCFlowJsonNode_unique {n : Nat} {c : YamlContext} {s s' : SurfPos} {ev₁ ev₂ : List Event} :
    TCFlowJsonNode n c s s' ev₁ → TCFlowJsonNode n c s s' ev₂ → ev₁ = ev₂ :=
  fun h₁ h₂ => ((allDet n _ s (Nat.le_refl _) c).1.2.2.1 h₁ h₂ (Or.inl rfl)).2

lemma tCFlowJsonContent_unique {n : Nat} {c : YamlContext} {s s' : SurfPos} {ev₁ ev₂ : List Event} :
    TCFlowJsonContent n c s s' ev₁ → TCFlowJsonContent n c s s' ev₂ → ev₁ = ev₂ :=
  fun h₁ h₂ =>
    (jsonContent_det (allDet n _ s (Nat.le_refl _) c).1.2.2.2.2.1
      (allDet n _ s (Nat.le_refl _) c).1.2.2.2.2.2 h₁ h₂ (Or.inl rfl)).2

lemma tFlowSequence_unique {n : Nat} {c : YamlContext} {s s' : SurfPos} {ev₁ ev₂ : List Event} :
    TFlowSequence n c s s' ev₁ → TFlowSequence n c s s' ev₂ → ev₁ = ev₂ :=
  fun h₁ h₂ => ((allDet n _ s (Nat.le_refl _) c).1.2.2.2.2.1 h₁ h₂).2

lemma tFlowMapping_unique {n : Nat} {c : YamlContext} {s s' : SurfPos} {ev₁ ev₂ : List Event} :
    TFlowMapping n c s s' ev₁ → TFlowMapping n c s s' ev₂ → ev₁ = ev₂ :=
  fun h₁ h₂ => ((allDet n _ s (Nat.le_refl _) c).1.2.2.2.2.2 h₁ h₂).2

/-- Entry lists are unique once the closing bracket is in view. The follow is what the proof
needs, not a refutation of the unconditional statement: entries are not prefix-free (inside
`[a:b]` the span `a:` is both the plain node `a:` and the key `a` with an empty value — same
trace `[]`, different split), so the induction cannot align the two derivations' intermediate
positions without knowing what comes next. -/
lemma tFlowSeqEntries_unique {n : Nat} {c : YamlContext} (hc : FlowCtx c) {s s' : SurfPos}
    {ev₁ ev₂ : List Event} (h₁ : TFlowSeqEntries n c s s' ev₁) (h₂ : TFlowSeqEntries n c s s' ev₂)
    (hs : CloseStop s') : ev₁ = ev₂ :=
  (((allDet n _ s (Nat.le_refl _) c).2 hc).1 h₁ h₂ hs hs).2

lemma tFlowMapEntries_unique {n : Nat} {c : YamlContext} (hc : FlowCtx c) {s s' : SurfPos}
    {ev₁ ev₂ : List Event} (h₁ : TFlowMapEntries n c s s' ev₁) (h₂ : TFlowMapEntries n c s s' ev₂)
    (hs : CloseStop s') : ev₁ = ev₂ :=
  (((allDet n _ s (Nat.le_refl _) c).2 hc).2 h₁ h₂ hs hs).2

/-- A single entry is deterministic up to its trailing separator under the entry follow. -/
lemma tFlowSeqEntry_det {n : Nat} {c : YamlContext} (hc : FlowCtx c) {s m₁ m₂ : SurfPos}
    {ev₁ ev₂ : List Event} (h₁ : TFlowSeqEntry n c s m₁ ev₁) (h₂ : TFlowSeqEntry n c s m₂ ev₂)
    (f₁ : EFollow n c m₁) (f₂ : EFollow n c m₂) : skipSep m₁ = skipSep m₂ ∧ ev₁ = ev₂ := by
  have A := allDet n _ s (Nat.le_refl _) c
  have Alt : ∀ s' : SurfPos, s'.chars.length < s.chars.length → AllDet n s' :=
    fun s' _ => allDet n _ s' (Nat.le_refl _)
  exact eshape_det hc A.1.1 A.1.2.2.1 A.1.2.2.2.1 (fun s' h => (Alt s' h c).1.1)
    (fun s' h => (Alt s' h c).1.2.2.1) (fun s' h => (Alt s' h c).1.2.2.2.1)
    (seqEntry_shape h₁) (seqEntry_shape h₂) f₁ f₂

lemma tFlowMapEntry_det {n : Nat} {c : YamlContext} (hc : FlowCtx c) {s m₁ m₂ : SurfPos}
    {ev₁ ev₂ : List Event} (h₁ : TFlowMapEntry n c s m₁ ev₁) (h₂ : TFlowMapEntry n c s m₂ ev₂)
    (f₁ : EFollow n c m₁) (f₂ : EFollow n c m₂) : skipSep m₁ = skipSep m₂ ∧ ev₁ = ev₂ := by
  have A := allDet n _ s (Nat.le_refl _) c
  have Alt : ∀ s' : SurfPos, s'.chars.length < s.chars.length → AllDet n s' :=
    fun s' _ => allDet n _ s' (Nat.le_refl _)
  exact eshape_det hc A.1.1 A.1.2.2.1 A.1.2.2.2.1 (fun s' h => (Alt s' h c).1.1)
    (fun s' h => (Alt s' h c).1.2.2.1) (fun s' h => (Alt s' h c).1.2.2.2.1)
    (mapEntry_shape h₁) (mapEntry_shape h₂) f₁ f₂

lemma tFlowSeqEntry_unique {n : Nat} {c : YamlContext} (hc : FlowCtx c) {s s' : SurfPos}
    {ev₁ ev₂ : List Event} (h₁ : TFlowSeqEntry n c s s' ev₁) (h₂ : TFlowSeqEntry n c s s' ev₂)
    (hf : EFollow n c s') : ev₁ = ev₂ :=
  (tFlowSeqEntry_det hc h₁ h₂ hf hf).2

lemma tFlowMapEntry_unique {n : Nat} {c : YamlContext} (hc : FlowCtx c) {s s' : SurfPos}
    {ev₁ ev₂ : List Event} (h₁ : TFlowMapEntry n c s s' ev₁) (h₂ : TFlowMapEntry n c s s' ev₂)
    (hf : EFollow n c s') : ev₁ = ev₂ :=
  (tFlowMapEntry_det hc h₁ h₂ hf hf).2

lemma tCNsProperties_unique {n : Nat} {c : YamlContext} {s s' : SurfPos} {ev₁ ev₂ : List Event} :
    TCNsProperties n c s s' ev₁ → TCNsProperties n c s s' ev₂ → ev₁ = ev₂ :=
  fun h₁ h₂ => props_det_eq h₁ h₂

lemma tCNsTagProperty_unique {s s' : SurfPos} {ev₁ ev₂ : List Event} :
    TCNsTagProperty s s' ev₁ → TCNsTagProperty s s' ev₂ → ev₁ = ev₂ :=
  fun h₁ h₂ => h₁.2.trans h₂.2.symm

lemma tCNsAnchorProperty_unique {s s' : SurfPos} {ev₁ ev₂ : List Event} :
    TCNsAnchorProperty s s' ev₁ → TCNsAnchorProperty s s' ev₂ → ev₁ = ev₂ :=
  fun h₁ h₂ => h₁.2.trans h₂.2.symm

lemma tCNsAliasNode_unique {s s' : SurfPos} {ev₁ ev₂ : List Event} :
    TCNsAliasNode s s' ev₁ → TCNsAliasNode s s' ev₂ → ev₁ = ev₂ :=
  fun h₁ h₂ => h₁.2.trans h₂.2.symm

end

end L4YAML.Proofs.Serialization.TraceOf
