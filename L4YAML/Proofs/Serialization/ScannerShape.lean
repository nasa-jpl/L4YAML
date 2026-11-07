module

public import L4YAML.Proofs.Serialization.ParseCheckFrom
public import L4YAML.Proofs.Scanner.DirectiveRuns
public import L4YAML.Proofs.Scanner.DocStartLive
public import L4YAML.Proofs.Scanner.FlowSync
import all L4YAML.Proofs.Serialization.TokenEvents

@[expose] public section Blanket

/-! # Scanner-output shape: S3's premises for `parseStream_ok_checkFrom`

`parseStream_ok_checkFrom` (S5, `ParseCheckFrom.lean`) takes scanner facts about
`scanFiltered input = .ok ts` as premises.  This module discharges them for real
scanner output.

* (b) `DirectivesClosed ts` — `scanFiltered_DirectivesClosed`, from
  `DirectiveRuns.scanFiltered_closedList` (the `directiveWithoutDocument` /
  `directiveAfterContent` refusals, carried through the scan loop as `DirInv`).
* (c) `streamEnd`-last — `scanFiltered_streamEnd_last`: the output is non-empty and
  its last token is `.streamEnd` (`scanLoop` emits it last, and the placeholder
  filter keeps it).  This alone does not make S5's consumed prefix the whole
  array: `parseStreamLoop` stops before consuming `.streamEnd`, so S5's witness
  `k` may be `ts.size - 1`.  The separate argument is `scanFiltered_streamEnd_index`
  (`.streamEnd` is the only such token, so that `k` is `ts.size - 1`) plus
  `tokenEvents_dropLast_streamEnd` (`.streamEnd` adds no event); together,
  `scanFiltered_parseStream_ok_checkFrom_full` carries S5's verdict to all of `ts`.
-/

namespace L4YAML.Proofs.Serialization.ScannerShape

open L4YAML L4YAML.Scanner L4YAML.TokenParser
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.ParseCheckFrom
open L4YAML.Proofs.DirectiveRuns L4YAML.Proofs.ScannerCorrectness

lemma isDirectiveTok_eq_isDirTok (o : Option YamlToken) : isDirectiveTok o = isDirTok o := by
  cases o with
  | none => rfl
  | some t => cases t <;> rfl

lemma tok_eq_toks (ts : Toks) (i : Nat) : ParseCheckFrom.tok ts i = (toks ts)[i]? := by
  simp [ParseCheckFrom.tok, toks]

/-- S3 obligation (b): every `%YAML`/`%TAG` token in `scanFiltered` output is followed by
another directive token or `---`. -/
lemma scanFiltered_DirectivesClosed (input : String) (ts : Toks)
    (h : scanFiltered input = .ok ts) : DirectivesClosed ts := by
  intro i hi
  rw [tok_eq_toks, isDirectiveTok_eq_isDirTok] at hi
  have hc := scanFiltered_closedList input ts h i hi
  rw [tok_eq_toks, isDirectiveTok_eq_isDirTok]
  exact hc

/-- `parseStream_ok_checkFrom` on scanner output, with premise (b) discharged by the scanner.
What remains to be supplied from outside is (a) `TagUsesShaped ts` — the scanner refuses every
other handle shape at runtime (`invalidTagHandle`), but that refusal is not yet a lemma. -/
lemma scanFiltered_parseStream_ok_checkFrom (input : String) (ts : Toks)
    (docs : Array YamlDocument) (hs : scanFiltered input = .ok ts) (hT : TagUsesShaped ts)
    (h : parseStream ts = .ok docs) :
    ∃ k, k ≤ ts.size ∧
      (k = ts.size ∨ ParseCheckFrom.tok ts k = some .streamEnd ∨ LoopDead ts k) ∧
      checkFrom {} (tokenEvents (ts.extract 0 k)) = true :=
  parseStream_ok_checkFrom ts docs hT (scanFiltered_DirectivesClosed input ts hs) h

/-! ## (c) `streamEnd` is the last token -/

/-- Raw `scan` output ends in `.streamEnd`: the token list is some prefix plus `[.streamEnd]`. -/
lemma scan_toks_streamEnd (input : String) (raw : Array (Positioned YamlToken))
    (h : scan input = .ok raw) : ∃ L, toks raw = L ++ [.streamEnd] := by
  unfold scan at h
  obtain ⟨s', hs'⟩ := scanLoop_success_emits_streamEnd _ _ raw h
  exact ⟨vals s', by rw [hs']; exact vals_emit s' .streamEnd⟩

/-- Filtering placeholders keeps the final `.streamEnd`. -/
lemma scanFiltered_toks_streamEnd (input : String) (ts : Toks) (h : scanFiltered input = .ok ts) :
    ∃ L, toks ts = L ++ [.streamEnd] := by
  unfold scanFiltered at h
  split at h
  · rename_i raw h0
    simp only [Except.ok.injEq] at h; subst h
    obtain ⟨L, hL⟩ := scan_toks_streamEnd input raw h0
    refine ⟨L.filter nonPh, ?_⟩
    rw [toks_filter, hL, List.filter_append]
    rfl
  · contradiction

/-- S3 obligation (c): `scanFiltered` output is non-empty and its last token is `.streamEnd`
(so nothing follows it: `TokenGrammar`'s `j + 1 = ts.size`). -/
lemma scanFiltered_streamEnd_last (input : String) (ts : Toks) (h : scanFiltered input = .ok ts) :
    0 < ts.size ∧ ParseCheckFrom.tok ts (ts.size - 1) = some .streamEnd := by
  obtain ⟨L, hL⟩ := scanFiltered_toks_streamEnd input ts h
  have hlen : ts.size = L.length + 1 := by
    have := congrArg List.length hL
    simpa [toks_length] using this
  refine ⟨by omega, ?_⟩
  rw [tok_eq_toks, hL, hlen]
  simp

/-- The filter keeps the one `.streamEnd` and introduces none. -/
lemma scanFiltered_toks_streamEnd_unique (input : String) (ts : Toks)
    (h : scanFiltered input = .ok ts) :
    ∃ L, toks ts = L ++ [.streamEnd] ∧ .streamEnd ∉ L := by
  unfold scanFiltered at h
  split at h
  · rename_i raw h0
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨L, hL, hn⟩ := scan_streamEnd_unique input raw h0
    refine ⟨L.filter nonPh, ?_, fun hm => hn (List.mem_filter.1 hm).1⟩
    rw [toks_filter, hL, List.filter_append]
    rfl
  · contradiction

/-- On scanner output the only index holding `.streamEnd` is the last one. -/
lemma scanFiltered_streamEnd_index (input : String) (ts : Toks) (h : scanFiltered input = .ok ts)
    (k : Nat) (hk : ParseCheckFrom.tok ts k = some .streamEnd) : k = ts.size - 1 := by
  obtain ⟨L, hL, hn⟩ := scanFiltered_toks_streamEnd_unique input ts h
  have hlen : ts.size = L.length + 1 := by
    have := congrArg List.length hL
    simpa [toks_length] using this
  rw [tok_eq_toks, hL] at hk
  by_cases hlt : k < L.length
  · rw [List.getElem?_append_left hlt] at hk
    exact absurd (List.mem_of_getElem? hk) hn
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hk
    rcases Nat.lt_or_ge (k - L.length) 1 with hlt1 | hge1
    · omega
    · rw [List.getElem?_eq_none (by simpa using hge1)] at hk
      cases hk

/-- `.streamEnd` contributes no event: `tokenEvent .streamEnd = none` and it is neither a `%TAG`
    directive nor `---`, so the fold ignores it. -/
lemma go_append_streamEnd (l : List (Positioned YamlToken)) (p : Positioned YamlToken)
    (hp : p.val = .streamEnd) : ∀ pending, go (l ++ [p]) pending = go l pending := by
  induction l with
  | nil => intro pending; simp [go, hp, tokenEvent]
  | cons t ts ih =>
    intro pending
    simp only [List.cons_append, go]
    split
    · split <;> simp [ih]
    · simp [ih]
    · split <;> simp [ih]

/-- Dropping a final `.streamEnd` leaves `tokenEvents` unchanged. -/
lemma tokenEvents_dropLast_streamEnd (ts : Toks) (L : List YamlToken)
    (hL : toks ts = L ++ [.streamEnd]) :
    tokenEvents (ts.extract 0 (ts.size - 1)) = tokenEvents ts := by
  rcases List.eq_nil_or_concat ts.toList with hnil | ⟨l', p, hcat⟩
  · have := congrArg List.length hL; simp [toks, hnil] at this
  · rw [List.concat_eq_append] at hcat
    have hp : p.val = .streamEnd := by
      have := congrArg List.getLast? hL
      simpa [toks, hcat] using this
    have h1 : (ts.extract 0 (ts.size - 1)).toList = ts.toList.dropLast := by
      simp [List.dropLast_eq_take]
    unfold tokenEvents
    rw [h1, hcat, List.dropLast_concat]
    exact (go_append_streamEnd l' p hp []).symm

/-- S5's token-level result on scanner output, carried to the full token array. `parseStreamLoop`
    stops before consuming `.streamEnd`, so S5's witness `k` may be `ts.size - 1`, not `ts.size`;
    since `.streamEnd` is the last token and the only one (`scanFiltered_streamEnd_index`) and adds
    no event (`go_append_streamEnd`), the checker's verdict on that prefix is its verdict on all of
    `ts`. The `LoopDead` disjunct is the loop's no-progress exit tied to where it can sit (S3 (d):
    `StuckAt` alone is refuted at every `.value` index); its first two shapes are the scanner's (β),
    the `.afterDocument` one the bracket-depth residue (γ). -/
lemma scanFiltered_parseStream_ok_checkFrom_full (input : String) (ts : Toks)
    (docs : Array YamlDocument) (hs : scanFiltered input = .ok ts)
    (hT : TagUsesShaped ts) (h : parseStream ts = .ok docs) :
    checkFrom {} (tokenEvents ts) = true ∨
      ∃ k, k ≤ ts.size ∧ LoopDead ts k ∧ checkFrom {} (tokenEvents (ts.extract 0 k)) = true := by
  obtain ⟨k, hk, hc, hchk⟩ := scanFiltered_parseStream_ok_checkFrom input ts docs hs hT h
  rcases hc with rfl | hse | hst
  · left; simpa using hchk
  · left
    obtain ⟨L, hL, _⟩ := scanFiltered_toks_streamEnd_unique input ts hs
    rw [scanFiltered_streamEnd_index input ts hs k hse, tokenEvents_dropLast_streamEnd ts L hL] at hchk
    exact hchk
  · right; exact ⟨k, hk, hst, hchk⟩

end L4YAML.Proofs.Serialization.ScannerShape

end Blanket
