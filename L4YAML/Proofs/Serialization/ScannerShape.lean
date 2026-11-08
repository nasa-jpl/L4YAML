module

public import L4YAML.Proofs.Serialization.ParseCheckFrom
public import L4YAML.Proofs.Scanner.DirectiveRuns
public import L4YAML.Proofs.Scanner.DocStartLive
public import L4YAML.Proofs.Scanner.FlowSync
public import L4YAML.Proofs.Scanner.DocStartLiveInv
public import L4YAML.Proofs.Scanner.TagShape
import all L4YAML.Proofs.Serialization.TokenEvents

@[expose] public section Blanket

/-! # Scanner-output shape: S3's premises for `parseStream_ok_checkFrom`

`parseStream_ok_checkFrom` (S5, `ParseCheckFrom.lean`) takes scanner facts about
`scanFiltered input = .ok ts` as premises.  This module discharges them for real
scanner output.

* (a) `TagUsesShaped ts` — `scanFiltered_TagUsesShaped`, from `TagShape.scanFiltered_emitOk`
  (the per-token `TagInv` carried over `scanLoop`: the only arm that builds a `.tag` is
  `scanTag`, whose handles are `""`, `"!!"`, `"!"` or `"!" ++ word-chars ++ "!"`), bridged
  to the parser's `BuiltinTagHandle ∨ isNamedHandle` by `tagOk_shaped`.
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
* (β2b) `LoopDead`'s index-1 / after-`...` shapes excluded — `LoopDead_scanFiltered`, from
  `DocStartLiveInv.scanFiltered_liveF` (the `LiveInv` carrier over `scanLoop`): a dead token
  there would need a non-boundary token before it.  What `scanFiltered_parseStream_ok_checkFrom_full`
  still carries is `DeadResidue` — the `.afterDocument` shape (γ); the `.comment` disjunct is
  closed by `scanFiltered_noComment` (`TagShape.emitOk`).
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

/-! ## (a) every tag use has a shaped handle -/

/-- The scanner-side token predicate (`TagShape.emitOk`: `""` or `isTagHandleShaped`) implies the
parser-side one (`BuiltinTagHandle ∨ isNamedHandle`); the named case is `ns-word-char ⊆
alphanumeric-or-dash` (`TagShape.wordChar_alnum`). -/
lemma tagOk_shaped (h suf : String) (ht : TagShape.emitOk (.tag h suf) = true) :
    BuiltinTagHandle h ∨ isNamedHandle h = true := by
  simp only [TagShape.emitOk, Bool.or_eq_true, beq_iff_eq] at ht
  rcases ht with rfl | ht
  · exact Or.inl (Or.inl rfl)
  · unfold isTagHandleShaped at ht
    simp only [Bool.or_eq_true, beq_iff_eq] at ht
    rcases ht with (rfl | rfl) | ht
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inr rfl))
    · right
      unfold isNamedHandle
      generalize h.toList = L at ht ⊢
      split at ht
      · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ht ⊢
        refine ⟨⟨ht.1.1, ht.1.2⟩, fun x hx => ?_⟩
        have := TagShape.wordChar_alnum x (ht.2 x hx)
        simpa using this
      · cases ht

/-- (a) discharged: every `.tag` on `scanFiltered` output has a builtin or named handle
(`TagShape.scanFiltered_emitOk` carried over `scanLoop`, bridged by `tagOk_shaped`). -/
lemma scanFiltered_TagUsesShaped (input : String) (ts : Toks) (hs : scanFiltered input = .ok ts) :
    TagUsesShaped ts := by
  intro p hp h suf hpv
  have hok := TagShape.scanFiltered_emitOk input ts hs p.val
    (List.mem_map.2 ⟨p, Array.mem_toList_iff.2 hp, rfl⟩)
  rw [hpv] at hok
  exact tagOk_shaped h suf hok

/-- `parseStream_ok_checkFrom` on scanner output, with premises (a) and (b) discharged by the
scanner (`scanFiltered_TagUsesShaped`, `scanFiltered_DirectivesClosed`). -/
lemma scanFiltered_parseStream_ok_checkFrom (input : String) (ts : Toks)
    (docs : Array YamlDocument) (hs : scanFiltered input = .ok ts)
    (h : parseStream ts = .ok docs) :
    ∃ k, k ≤ ts.size ∧
      (k = ts.size ∨ ParseCheckFrom.tok ts k = some .streamEnd ∨ LoopDead ts k) ∧
      checkFrom {} (tokenEvents (ts.extract 0 k)) = true :=
  parseStream_ok_checkFrom ts docs (scanFiltered_TagUsesShaped input ts hs)
    (scanFiltered_DirectivesClosed input ts hs) h

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

/-- A dead token at index 1, or right after a `.documentEnd`, contradicts `LiveF`: the token before
it would have to be a non-boundary one. -/
lemma liveF_dead_contra (F : List YamlToken) (hL : DocStartLive.LiveF F) (hhd : F[0]? = some .streamStart)
    (k : Nat) (t : YamlToken) (hkt : F[k]? = some t) (hlt : DocStartLive.liveTok t = false)
    (hpos : k = 1 ∨ F[k - 1]? = some .documentEnd) : False := by
  have hkpos : 0 < k := by
    rcases hpos with h | h
    · omega
    · cases k with
      | zero => simp only [Nat.zero_sub] at h; rw [hhd] at h; cases h
      | succ => omega
  obtain ⟨u, hu, hBu⟩ := hL k t hkpos hkt hlt
  rcases hpos with rfl | h
  · simp only [Nat.sub_self] at hu; rw [hhd] at hu
    simp only [Option.some.injEq] at hu; subst hu; simp [DocStartLive.Bnd] at hBu
  · rw [h] at hu; simp only [Option.some.injEq] at hu; subst hu; simp [DocStartLive.Bnd] at hBu

/-- The residue of `LoopDead` after (β2) and the `.comment` lemma: the `.afterDocument` shape (γ). -/
def DeadResidue (o : Option YamlToken) : Prop :=
  ∃ t, o = some t ∧ StreamState.validNextToken .afterDocument t = true

/-- The scanner emits no `.comment` token (`TagShape.emitOk`, carried over `scanLoop`). -/
lemma scanFiltered_noComment (input : String) (ts : Toks) (hs : scanFiltered input = .ok ts)
    (k : Nat) (text : String) : ParseCheckFrom.tok ts k ≠ some (.comment text) := by
  intro h
  rw [tok_eq_toks] at h
  have := TagShape.scanFiltered_emitOk input ts hs _ (List.mem_of_getElem? h)
  simp [TagShape.emitOk] at this

/-- (β2): on scanner output the loop's no-progress exit cannot sit at index 1 or right after a
`...` — the token there is live (`scanFiltered_liveF`), and a dead token at `k` would need a
non-boundary token at `k - 1`. What remains of `LoopDead` is `DeadResidue`, or the loop stopped
at `.streamEnd` / the end of the array. -/
lemma LoopDead_scanFiltered (input : String) (ts : Toks) (hs : scanFiltered input = .ok ts)
    (k : Nat) (hk : k ≤ ts.size) (hd : LoopDead ts k) :
    k = ts.size ∨ ParseCheckFrom.tok ts k = some .streamEnd ∨
      DeadResidue (ParseCheckFrom.tok ts k) := by
  obtain ⟨hL, hhd⟩ := DocStartLiveInv.scanFiltered_liveF input ts hs
  obtain ⟨hdead, hne, hpos⟩ := hd
  have hlen : (toks ts).length = ts.size := by simp [toks]
  rcases hpos with hk1 | hde | ⟨t, ht, hγ⟩
  all_goals try (right; right; unfold DeadResidue; exact ⟨t, ht, hγ⟩)
  all_goals
    have hpos' : k = 1 ∨ (toks ts)[k - 1]? = some .documentEnd := by
      first
        | exact Or.inl hk1
        | exact Or.inr (by rw [← tok_eq_toks]; exact hde)
    rcases hdead with hdt | ⟨hbe, hk0, hbe'⟩
    · cases htk : ParseCheckFrom.tok ts k with
      | none =>
        left
        rw [tok_eq_toks] at htk
        have := List.getElem?_eq_none_iff.1 htk
        omega
      | some t =>
        rw [htk] at hdt hne
        have htk' : (toks ts)[k]? = some t := by rw [← tok_eq_toks]; exact htk
        cases t <;> simp [deadTok] at hdt
        all_goals first
          | exact absurd rfl hne
          | exact Or.inr (Or.inl rfl)
          | exact absurd htk (scanFiltered_noComment input ts hs k _)
          | exact (liveF_dead_contra _ hL hhd k _ htk' (by decide) hpos').elim
          | (exfalso
             have hmem := List.mem_of_getElem? htk'
             unfold scanFiltered at hs
             split at hs
             · simp only [Except.ok.injEq] at hs; subst hs
               rw [toks_filter] at hmem
               have := (List.mem_filter.1 hmem).2
               simp [nonPh] at this
             · contradiction)
    · exfalso
      rw [tok_eq_toks] at hbe'
      rcases hpos' with rfl | h
      · simp only [Nat.sub_self] at hbe'; rw [hhd] at hbe'; cases hbe'
      · rw [h] at hbe'; cases hbe'

/-- S5's token-level result on scanner output, carried to the full token array. `parseStreamLoop`
    stops before consuming `.streamEnd`, so S5's witness `k` may be `ts.size - 1`, not `ts.size`;
    since `.streamEnd` is the last token and the only one (`scanFiltered_streamEnd_index`) and adds
    no event (`go_append_streamEnd`), the checker's verdict on that prefix is its verdict on all of
    `ts`. The `LoopDead` disjunct is the loop's no-progress exit tied to where it can sit (S3 (d):
    `StuckAt` alone is refuted at every `.value` index); its first two shapes (index 1, right after
    `...`) are excluded by the scanner (β2, `LoopDead_scanFiltered`), leaving the `.afterDocument`
    one — the bracket-depth residue (γ). -/
lemma scanFiltered_parseStream_ok_checkFrom_full (input : String) (ts : Toks)
    (docs : Array YamlDocument) (hs : scanFiltered input = .ok ts)
    (h : parseStream ts = .ok docs) :
    checkFrom {} (tokenEvents ts) = true ∨
      ∃ k, k ≤ ts.size ∧ LoopDead ts k ∧ DeadResidue (ParseCheckFrom.tok ts k) ∧
        checkFrom {} (tokenEvents (ts.extract 0 k)) = true := by
  obtain ⟨k, hk, hc, hchk⟩ := scanFiltered_parseStream_ok_checkFrom input ts docs hs h
  have hc' : k = ts.size ∨ ParseCheckFrom.tok ts k = some .streamEnd ∨
      (LoopDead ts k ∧ DeadResidue (ParseCheckFrom.tok ts k)) := by
    rcases hc with h1 | h2 | hst
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · rcases LoopDead_scanFiltered input ts hs k hk hst with h1 | h2 | hγ
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨hst, hγ⟩)
  rcases hc' with rfl | hse | ⟨hst, hγ⟩
  · left; simpa using hchk
  · left
    obtain ⟨L, hL, _⟩ := scanFiltered_toks_streamEnd_unique input ts hs
    rw [scanFiltered_streamEnd_index input ts hs k hse, tokenEvents_dropLast_streamEnd ts L hL] at hchk
    exact hchk
  · right; exact ⟨k, hk, hst, hγ, hchk⟩

end L4YAML.Proofs.Serialization.ScannerShape

end Blanket
