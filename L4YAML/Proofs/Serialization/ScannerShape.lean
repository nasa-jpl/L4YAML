module

public import L4YAML.Proofs.Serialization.ParseCheckFrom
public import L4YAML.Proofs.Scanner.DirectiveRuns

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
  filter keeps it), so the consumed prefix `k = ts.size` is the whole array.
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
      (k = ts.size ∨ ParseCheckFrom.tok ts k = some .streamEnd ∨ StuckAt ts k) ∧
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

end L4YAML.Proofs.Serialization.ScannerShape

end Blanket
