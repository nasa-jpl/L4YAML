/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.DirectiveRuns

@[expose] public section Blanket

/-! # Live document starts in scanner output (capstone 7.7, stream S3, obligation (β))

    In the filtered token stream the token at index 1 and the token right after
    every `.documentEnd` is never one of the parser's dead followers
    (`.key`, `.value`, `.blockEnd`, `.flowEntry`, `.flowSequenceEnd`,
    `.flowMappingEnd`, `.streamStart`).  The scanner only emits those tokens
    with an opener still open (`pushMappingIndent`/`pushSequenceIndent` emit the
    block opener first, flow indicators need `flowLevel > 0`, and `...`/`---`
    inside a flow collection or a quoted scalar is a `documentMarker…` error),
    so in the RAW token list (placeholders included) the last real token before
    any dead token is neither `.streamStart` nor `.documentEnd`.

    List level first: `Shape` on the raw list, `LiveF` on the filtered one and
    the bridge between them.  The scanner invariant `LiveInv` follows. -/

namespace L4YAML.Proofs.DocStartLive

open L4YAML L4YAML.Scanner
open L4YAML.Proofs.DirectiveRuns

/-- Tokens `parseDocument` can leave unconsumed at a document start. -/
def liveTok : YamlToken → Bool
  | .key | .value | .blockEnd | .flowEntry | .flowSequenceEnd | .flowMappingEnd
  | .streamStart => false
  | _ => true

/-- A document boundary (or nothing at all) as the last real token. -/
def Bnd : Option YamlToken → Bool
  | none | some .streamStart | some .documentEnd => true
  | _ => false

/-- The last non-placeholder token of a raw list. -/
def lastReal (L : List YamlToken) : Option YamlToken :=
  L.foldl (fun acc t => if nonPh t then some t else acc) none

@[simp] lemma lastReal_nil : lastReal [] = none := rfl

lemma lastReal_snoc (L : List YamlToken) (t : YamlToken) :
    lastReal (L ++ [t]) = if nonPh t then some t else lastReal L := by
  simp [lastReal, List.foldl_append]

lemma lastReal_append_ph (L M : List YamlToken) (hM : ∀ t ∈ M, nonPh t = false) :
    lastReal (L ++ M) = lastReal L := by
  induction M generalizing L with
  | nil => simp
  | cons t M ih =>
    have ht : nonPh t = false := hM t (by simp)
    have := ih (L ++ [t]) (fun u hu => hM u (by simp [hu]))
    rw [List.append_cons, this, lastReal_snoc, ht]; rfl

/-- Raw shape: every dead real token at `j > 0` has a non-boundary real token
    before it. -/
def Shape (L : List YamlToken) : Prop :=
  ∀ j t, 0 < j → L[j]? = some t → liveTok t = false → nonPh t = true →
    Bnd (lastReal (L.take j)) = false

lemma Shape_nil : Shape [] := by intro j t _ h; simp at h

lemma Shape_snoc (L : List YamlToken) (t : YamlToken) (hL : Shape L)
    (ht : liveTok t = false → nonPh t = true → Bnd (lastReal L) = false) :
    Shape (L ++ [t]) := by
  intro j u hj hu hl hp
  rcases Nat.lt_trichotomy j L.length with hlt | heq | hgt
  · rw [List.getElem?_append_left hlt] at hu
    rw [take_append_of_le _ _ _ (Nat.le_of_lt hlt)]
    exact hL j u hj hu hl hp
  · subst heq
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hu
    simp at hu; subst hu
    rw [take_append_of_le _ _ _ (Nat.le_refl _), List.take_length]
    exact ht hl hp
  · rw [List.getElem?_append_right (Nat.le_of_lt hgt)] at hu
    have : j - L.length ≠ 0 := by omega
    simp [List.getElem?_cons, this] at hu

lemma Shape_append_ph (L M : List YamlToken) (hL : Shape L) (hM : ∀ t ∈ M, nonPh t = false) :
    Shape (L ++ M) := by
  induction M generalizing L with
  | nil => simpa using hL
  | cons t M ih =>
    rw [List.append_cons]
    exact ih (L ++ [t]) (Shape_snoc L t hL (fun _ hp => by rw [hM t (by simp)] at hp; cases hp))
      (fun u hu => hM u (by simp [hu]))

/-- Snoc induction on token lists (core has no `reverseRecOn`). -/
lemma snoc_induction {P : List YamlToken → Prop} (h0 : P [])
    (hs : ∀ L t, P L → P (L ++ [t])) : ∀ L, P L := by
  intro L
  induction hn : L.length generalizing L with
  | zero => rw [List.length_eq_zero_iff] at hn; subst hn; exact h0
  | succ n ih =>
    rcases List.eq_nil_or_concat L with rfl | ⟨M, b, hL⟩
    · simp at hn
    · rw [List.concat_eq_append] at hL; subst hL
      exact hs M b (ih M (by simpa using hn))

/-- Filtered shape: a dead token at `k > 0` sits right after a non-boundary token. -/
def LiveF (F : List YamlToken) : Prop :=
  ∀ k t, 0 < k → F[k]? = some t → liveTok t = false →
    ∃ u, F[k - 1]? = some u ∧ Bnd (some u) = false

lemma filter_getLast (L : List YamlToken) : (L.filter nonPh).getLast? = lastReal L := by
  induction L using snoc_induction with
  | h0 => rfl
  | hs L t ih =>
    rw [List.filter_append, lastReal_snoc]
    cases h : nonPh t with
    | true => simp [h]
    | false => simpa [h] using ih

lemma LiveF_snoc (F : List YamlToken) (t : YamlToken) (hF : LiveF F)
    (ht : F ≠ [] → liveTok t = false → ∃ u, F.getLast? = some u ∧ Bnd (some u) = false) :
    LiveF (F ++ [t]) := by
  intro k u hk hu hl
  rcases Nat.lt_trichotomy k F.length with hlt | heq | hgt
  · rw [List.getElem?_append_left hlt] at hu
    rw [List.getElem?_append_left (by omega)]
    exact hF k u hk hu hl
  · subst heq
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hu
    simp at hu; subst hu
    obtain ⟨v, hv, hb⟩ := ht (List.ne_nil_of_length_pos hk) hl
    refine ⟨v, ?_, hb⟩
    rw [List.getElem?_append_left (by omega), ← hv, List.getLast?_eq_getElem?]
  · rw [List.getElem?_append_right (Nat.le_of_lt hgt)] at hu
    have : k - F.length ≠ 0 := by omega
    simp [this] at hu

/-- The bridge: a raw list of the right shape filters to a live one. -/
lemma LiveF_of_Shape (L : List YamlToken) (h : Shape L) : LiveF (L.filter nonPh) := by
  induction L using snoc_induction with
  | h0 => intro k t _ h; simp at h
  | hs L t ih =>
    have hL : Shape L := by
      intro j u hj hu hl hp
      have hj' : j < L.length := List.getElem?_eq_some_iff.mp hu |>.1
      have := h j u hj (by rw [List.getElem?_append_left hj']; exact hu) hl hp
      rwa [take_append_of_le _ _ _ (Nat.le_of_lt hj')] at this
    rw [List.filter_append]
    cases hp : nonPh t with
    | false => simpa [hp] using ih hL
    | true =>
      simp only [hp, List.filter_cons_of_pos, List.filter_nil]
      refine LiveF_snoc _ t (ih hL) (fun hne hl => ?_)
      have hL0 : 0 < L.length := by
        rcases L with _ | ⟨a, L⟩
        · exact absurd rfl hne
        · simp
      have hb := h L.length t hL0 (by simp) hl hp
      rw [take_append_of_le _ _ _ (Nat.le_refl _), List.take_length, ← filter_getLast] at hb
      cases hv : (L.filter nonPh).getLast? with
      | none => rw [hv] at hb; cases hb
      | some v => exact ⟨v, rfl, by rw [hv] at hb; exact hb⟩

/-! ## Towards the scanner invariant (β2): extension by live tokens -/

lemma lastReal_append_cases (L M : List YamlToken) :
    lastReal (L ++ M) = lastReal L ∨
      ∃ t ∈ M, nonPh t = true ∧ lastReal (L ++ M) = some t := by
  induction M using snoc_induction with
  | h0 => simp
  | hs M t ih =>
    rw [← List.append_assoc, lastReal_snoc]
    cases ht : nonPh t with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases ih with h | ⟨u, hu, hn, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨u, by simp [hu], hn, h⟩
    | true => exact Or.inr ⟨t, by simp, ht, by simp⟩

/-- Every real token appended is live and not a boundary. -/
def LiveExt (M : List YamlToken) : Prop :=
  ∀ t ∈ M, nonPh t = true → liveTok t = true ∧ Bnd (some t) = false

lemma Shape_append_live (L M : List YamlToken) (hL : Shape L) (hM : LiveExt M) : Shape (L ++ M) := by
  induction M using snoc_induction with
  | h0 => simpa using hL
  | hs M t ih =>
    rw [← List.append_assoc]
    refine Shape_snoc _ t (ih (fun u hu => hM u (by simp [hu]))) (fun hl hp => ?_)
    exact absurd (hM t (by simp) hp).1 (by simp [hl])

lemma Bnd_lastReal_append_live (L M : List YamlToken) (hM : LiveExt M)
    (h : Bnd (lastReal (L ++ M)) = true) : lastReal (L ++ M) = lastReal L := by
  rcases lastReal_append_cases L M with h' | ⟨t, ht, hn, h'⟩
  · exact h'
  · rw [h'] at h; exact absurd h (by simp [(hM t ht hn).2])

/-- The simple-key slot is reachable from the saved state: the real token before it
    is no boundary, or the save happened in block context strictly deeper than the
    current indent (so `scanValuePrepare` will open a mapping first). -/
end L4YAML.Proofs.DocStartLive
