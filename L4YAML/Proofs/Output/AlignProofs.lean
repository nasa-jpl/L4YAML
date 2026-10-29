module

public import L4YAML.Output.Align

@[expose] public section Blanket

/-!
# AlignProofs — what the column aligner guarantees

* `applyEditsFrom_filter` / `applyEdits_filter`: edit application preserves
  every non-blank character, in order — so the text outside the rewritten
  blank runs is untouched, and (`applyEdits_count_newline`) the line
  structure is preserved.
* `format_ok_filter`: a successful `format` is such a whitespace-only edit.
* `format_ok_scanShape`: a successful `format` yields the same token values
  and the same comments as its input — the fail-closed check is sound.
* `minGap_le_gap`: a cell that takes part in alignment is never squeezed
  below `minGap` blanks.
-/

namespace L4YAML.Align

/-- The predicate "is not a blank". -/
abbrev nonBlank (c : Char) : Bool := !isWhite c

lemma filter_replicate_space (n : Nat) :
    (List.replicate n ' ').filter nonBlank = [] := by
  simp [nonBlank, isWhite]

lemma filter_all_white (l : List Char) (h : l.all isWhite = true) :
    l.filter nonBlank = [] := by
  rw [List.filter_eq_nil_iff]
  intro c hc
  have := (List.all_eq_true.mp h) c hc
  simp [nonBlank, this]

lemma split_three (l : List Char) (pos a b : Nat) (hpa : pos ≤ a) (hab : a ≤ b) :
    l = l.take (a - pos) ++ ((l.drop (a - pos)).take (b - a) ++ l.drop (b - pos)) := by
  have h1 := List.take_append_drop (a - pos) l
  have h2 := List.take_append_drop (b - a) (l.drop (a - pos))
  rw [List.drop_drop] at h2
  have : a - pos + (b - a) = b - pos := by omega
  rw [this] at h2
  rw [← h2] at h1
  exact h1.symm

/-- Edit application preserves the non-blank characters, in order. -/
lemma applyEditsFrom_filter (pos : Nat) (es : List Edit) (l : List Char) :
    (applyEditsFrom pos es l).filter nonBlank = l.filter nonBlank := by
  induction es generalizing pos l with
  | nil => rfl
  | cons e es ih =>
    rw [applyEditsFrom]
    split
    · rename_i hord
      dsimp only
      split
      · rename_i hmid
        rw [congrArg (List.filter nonBlank) (split_three l pos e.start e.stop hord.1 hord.2)]
        simp only [List.filter_append]
        rw [ih, filter_replicate_space, filter_all_white _ hmid]
        simp
      · exact ih pos l
    · exact ih pos l

lemma applyEdits_filter (edits : Array Edit) (s : String) :
    (applyEdits edits s).toList.filter nonBlank = s.toList.filter nonBlank := by
  unfold applyEdits
  rw [String.toList_ofList]
  exact applyEditsFrom_filter _ _ _

lemma count_filter_of_pos (p : Char → Bool) (a : Char) (ha : p a = true) (l : List Char) :
    (l.filter p).count a = l.count a := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : c = a
    · subst h
      simp [ha, ih]
    · simp only [List.filter_cons]
      split
      · simp [ih, h]
      · simp [ih, h]

/-- The number of lines is preserved (`\n` is never blank). -/
lemma applyEdits_count_newline (edits : Array Edit) (s : String) :
    (applyEdits edits s).toList.count '\n' = s.toList.count '\n' := by
  have h := applyEdits_filter edits s
  have hnl : nonBlank '\n' = true := by decide
  rw [← count_filter_of_pos nonBlank '\n' hnl, h, count_filter_of_pos nonBlank '\n' hnl]

lemma alignText_filter (cfg : AlignConfig) (s : String)
    (toks : Array (Positioned YamlToken)) :
    (alignText cfg s toks).toList.filter nonBlank = s.toList.filter nonBlank :=
  applyEdits_filter _ _

/-- A successful `format` only rewrote blanks. -/
lemma format_ok_filter (cfg : AlignConfig) (s out : String) (h : format cfg s = .ok out) :
    out.toList.filter nonBlank = s.toList.filter nonBlank := by
  dsimp only [format] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
        exact alignText_filter _ _ _
      · cases h

/-- A successful `format` has the same tokens and comments as its input. -/
lemma format_ok_scanShape (cfg : AlignConfig) (s out : String) (h : format cfg s = .ok out) :
    scanShape out = scanShape s := by
  dsimp only [format] at h
  split at h
  · cases h
  · rename_i toks cms hs
    split at h
    · cases h
    · rename_i toks' cms' hs'
      split at h
      · rename_i heq
        cases h
        unfold scanShape
        rw [hs, hs']
        simp only [heq.1, heq.2]
      · cases h

/-- A cell that takes part in alignment keeps at least `minGap` blanks. -/
lemma minGap_le_gap (cells : List Nat) (maxCell round used minGap t : Nat)
    (hc : used + minGap ∈ cells) (hfit : used + minGap ≤ maxCell)
    (ht : groupTarget cells maxCell round = some t) :
    minGap ≤ gapWidth true t used minGap :=
  minGap_le_gapWidth true t used minGap
    (fun _ => le_groupTarget cells maxCell round _ t hc hfit ht)

end L4YAML.Align

end Blanket
