module

public import L4YAML.Proofs.Serialization.ParseCheckFrom
public import L4YAML.Proofs.Scanner.DirectiveRuns
public import L4YAML.Proofs.Scanner.DocStartLive
public import L4YAML.Proofs.Scanner.FlowSync
public import L4YAML.Proofs.Scanner.DocStartLiveInv
public import L4YAML.Proofs.Scanner.TagShape
public import L4YAML.Proofs.Scanner.StructDepth
public import L4YAML.Proofs.Serialization.TraceOf.LeafBridge
public import L4YAML.Proofs.Serialization.TraceOf.DocBridge
public import L4YAML.Proofs.Serialization.TraceOf.FlowBridge
public import L4YAML.Proofs.Scanner.AliasTrailingContent
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
* Scanner-shape facts on the parser's view of the array, from the `scanLoop` carriers:
  `liveF_dead_contra` (β2b, `DocStartLiveInv.scanFiltered_liveF`), `scanFiltered_noComment`
  (`TagShape.emitOk`), `scanFiltered_bal_tok` (γ1, `StructDepth.scanFiltered_bal`).  They were
  the discharge of `parseStreamLoop`'s no-progress exit (`LoopDead` / `DeadResidue`, items
  446–452); since (γ2α) that exit is an error, `scanFiltered_parseStream_ok_checkFrom_full`
  concludes `checkFrom {} (tokenEvents ts) = true` outright, and these facts stand alone.
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
      (k = ts.size ∨ ParseCheckFrom.tok ts k = some .streamEnd) ∧
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

/-- The scanner emits no `.comment` token (`TagShape.emitOk`, carried over `scanLoop`). -/
lemma scanFiltered_noComment (input : String) (ts : Toks) (hs : scanFiltered input = .ok ts)
    (k : Nat) (text : String) : ParseCheckFrom.tok ts k ≠ some (.comment text) := by
  intro h
  rw [tok_eq_toks] at h
  have := TagShape.scanFiltered_emitOk input ts hs _ (List.mem_of_getElem? h)
  simp [TagShape.emitOk] at this

/-- (γ1) on the parser's view of the token array: a structural dead token at index `k` of
    `scanFiltered` output sits at positive `StructDepth.depth`. -/
lemma scanFiltered_bal_tok (input : String) (ts : Toks) (hs : scanFiltered input = .ok ts)
    (k : Nat) (t : YamlToken) (hk : ParseCheckFrom.tok ts k = some t)
    (hd : StructDepth.structDead t = true) : 0 < StructDepth.depth ((toks ts).take k) := by
  rw [tok_eq_toks] at hk
  exact StructDepth.scanFiltered_bal input ts hs k t hk hd

/-- S5's token-level result on scanner output, carried to the full token array. `parseStreamLoop`
    stops before consuming `.streamEnd`, so S5's witness `k` may be `ts.size - 1`, not `ts.size`;
    since `.streamEnd` is the last token and the only one (`scanFiltered_streamEnd_index`) and adds
    no event (`go_append_streamEnd`), the checker's verdict on that prefix is its verdict on all of
    `ts`.  The loop's no-progress exit is an error since (γ2α), so there is no residue: the
    `LoopDead` / `DeadResidue` alternative of items 446–452 is gone. -/
lemma scanFiltered_parseStream_ok_checkFrom_full (input : String) (ts : Toks)
    (docs : Array YamlDocument) (hs : scanFiltered input = .ok ts)
    (h : parseStream ts = .ok docs) :
    checkFrom {} (tokenEvents ts) = true := by
  obtain ⟨k, hk, hc, hchk⟩ := scanFiltered_parseStream_ok_checkFrom input ts docs hs h
  rcases hc with rfl | hse
  · simpa using hchk
  · obtain ⟨L, hL, _⟩ := scanFiltered_toks_streamEnd_unique input ts hs
    rw [scanFiltered_streamEnd_index input ts hs k hse, tokenEvents_dropLast_streamEnd ts L hL] at hchk
    exact hchk

/-! ## The leaf arms of the content dispatcher land on the annotated leaves (S3 slice (1))

`scanNextToken_dispatchContent`'s `&` / `*` / `!` arms, composed onto
`TraceOf.LeafBridge.scanAnchorOrAlias_trace` / `scanTag_trace`: the token the arm
pushes is the leaf token, and the lexeme it consumed is the annotated leaf relation
whose trace is `tokenEvent` of that token.  These are the per-arm facts the later
slices of `scan_trace` walk through `scanLoop` with. -/

open L4YAML.Surface L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Serialization.TraceOf L4YAML.Proofs.Serialization.TraceOf.LeafBridge in
lemma dispatchContent_anchor_trace (s : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr s sp) (hpeek : s.peek? = some '&') (s'' : ScannerState)
    (h : scanNextToken_dispatchContent s '&' = .ok s'') :
    ∃ sp' name,
      s''.tokens = s.tokens.push (Positioned.mk s.currentPos (.anchor name) s.currentPos) ∧
      ScannerSurfCorr s'' sp' ∧ TCNsAnchorProperty sp sp' [.defineAnchor name] := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · split at h
    · simp at h
    generalize h_fn : scanAnchorOrAlias s true = result at h
    cases result with
    | error e => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h
      obtain ⟨sp', name, htok, hcorr', hA, _⟩ :=
        scanAnchorOrAlias_trace s sp true hcorr (by simpa using hpeek) s_a h_fn
      exact ⟨sp', name, by simpa using htok,
        ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩,
        hA rfl⟩
  · exact absurd (by decide : ('&' == '&') = true) (by assumption)

open L4YAML.Surface L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Serialization.TraceOf L4YAML.Proofs.Serialization.TraceOf.LeafBridge in
lemma dispatchContent_alias_trace (s : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr s sp) (hpeek : s.peek? = some '*') (s'' : ScannerState)
    (h : scanNextToken_dispatchContent s '*' = .ok s'') :
    ∃ sp' name,
      s''.tokens = s.tokens.push (Positioned.mk s.currentPos (.alias name) s.currentPos) ∧
      ScannerSurfCorr s'' sp' ∧ TCNsAliasNode sp sp' [.useAlias name] := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · exact absurd (by assumption : ('*' == '&') = true) (by decide)
  · split at h
    · split at h
      · simp at h
      split at h
      · simp at h
      · have h_fn := aliasArm_scan_ok h
        obtain ⟨sp', name, htok, hcorr', _, hA⟩ :=
          scanAnchorOrAlias_trace s sp false hcorr (by simpa using hpeek) s'' h_fn
        exact ⟨sp', name, by simpa using htok, hcorr', hA rfl⟩
    · exact absurd (by decide : ('*' == '*') = true) (by assumption)

open L4YAML.Surface L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Serialization.TraceOf L4YAML.Proofs.Serialization.TraceOf.LeafBridge in
lemma dispatchContent_tag_trace (s : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr s sp) (hpeek : s.peek? = some '!') (s'' : ScannerState)
    (h : scanNextToken_dispatchContent s '!' = .ok s'') :
    ∃ sp' handle suffix,
      s''.tokens = s.tokens.push (Positioned.mk s.currentPos (.tag handle suffix) s.currentPos) ∧
      ScannerSurfCorr s'' sp' ∧
      TCNsTagProperty sp sp' ((tokenEvent (.tag handle suffix)).toList) := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · exact absurd (by assumption : ('!' == '&') = true) (by decide)
  · split at h
    · exact absurd (by assumption : ('!' == '*') = true) (by decide)
    · split at h
      · split at h
        · simp at h
        generalize h_fn : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact scanTag_trace s sp hcorr hpeek s_t h_fn
      · exact absurd (by decide : ('!' == '!') = true) (by assumption)

/-! ## S3 slice (2): the structural dispatcher's `---` / `...` / `%` arms (item 463) -/

section DocBridgeConsumers
open L4YAML.Surface L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge L4YAML.Proofs.StructureProduction
open L4YAML.CharPredicates

/-- The `---` arm of `scanNextToken_dispatchStructural` is `scanDocumentStart_trace`. -/
lemma dispatchStructural_documentStart_trace (s : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr s sp) (hflow : s.inFlow = false)
    (rest : List Char) (hchars : sp.chars = '-' :: '-' :: '-' :: rest) (hcol : sp.col = 0)
    (hds : atDocumentStart s = true) (s'' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s'')) :
    ∃ (sp' : SurfPos) (ends : List (Positioned YamlToken)) (ds : Positioned YamlToken),
      SCDirectivesEnd sp sp' ∧ ScannerSurfCorr s'' sp' ∧
      s''.tokens.toList = s.tokens.toList ++ ends ++ [ds] ∧
      (∀ t ∈ ends, t.val = .blockEnd) ∧ ds.val = .documentStart ∧
      ∀ p, goOut (ends ++ [ds]) p = (.beginDocument :: p.reverse.map .declareTag, []) := by
  have hscol : s.col = 0 := by rw [← hcorr.col_eq]; exact hcol
  unfold scanNextToken_dispatchStructural at h
  simp only [hflow, hscol, hds, Bool.false_and, Bool.and_false, beq_self_eq_true,
    Bool.and_true, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
    Option.some.injEq] at h
  subst h
  exact scanDocumentStart_trace s sp hcorr rest hchars hcol

/-- The `...` arm of `scanNextToken_dispatchStructural` is `scanDocumentEnd_trace`. -/
lemma dispatchStructural_documentEnd_trace (s : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr s sp) (hflow : s.inFlow = false)
    (rest : List Char) (hchars : sp.chars = '.' :: '.' :: '.' :: rest) (hcol : sp.col = 0)
    (hnds : atDocumentStart s = false) (hde : atDocumentEnd s = true) (s'' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s'')) :
    ∃ (sp' : SurfPos) (ends : List (Positioned YamlToken)) (de : Positioned YamlToken),
      SCDocumentEnd sp sp' ∧ ScannerSurfCorr s'' sp' ∧
      s''.tokens.toList = s.tokens.toList ++ ends ++ [de] ∧
      (∀ t ∈ ends, t.val = .blockEnd) ∧ de.val = .documentEnd ∧
      ∀ p, goOut (ends ++ [de]) p = ([.endDocument], p) := by
  have hscol : s.col = 0 := by rw [← hcorr.col_eq]; exact hcol
  unfold scanNextToken_dispatchStructural at h
  simp only [hflow, hscol, hnds, hde, Bool.false_and, Bool.and_false, beq_self_eq_true,
    Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
  generalize hfn : scanDocumentEnd s = result at h
  cases result with
  | error e => simp at h
  | ok s_e =>
    simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact scanDocumentEnd_trace s sp hcorr rest hchars hcol s_e hfn

/-- The `%` arm of `scanNextToken_dispatchStructural` is `scanDirective_trace`. -/
lemma dispatchStructural_directive_trace (s : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr s sp) (hflow : s.inFlow = false) (hcol : sp.col = 0)
    (hpeek : s.peek? = some '%')
    (hnds : atDocumentStart s = false) (hnde : atDocumentEnd s = false) (s'' : ScannerState)
    (h : scanNextToken_dispatchStructural s '%' = .ok (some s'')) :
    ∃ sp', ScannedDirective sp sp' ∧ ScannerSurfCorr s'' sp' ∧
      (sp'.chars = [] ∨ ∃ ch rest', sp'.chars = ch :: rest' ∧ isLineBreakBool ch = true) ∧
      ∃ new : List (Positioned YamlToken),
        s''.tokens.toList = s.tokens.toList ++ new ∧
        (∀ p, goOut new p = ([], (EventsOf.declaredHandle (span sp sp')).toList ++ p)) ∧
        (∀ sp'' : SurfPos, sp''.chars.length ≤ sp'.chars.length →
          EventsOf.declaredHandle (span sp sp'') = EventsOf.declaredHandle (span sp sp')) := by
  have hscol : s.col = 0 := by rw [← hcorr.col_eq]; exact hcol
  unfold scanNextToken_dispatchStructural at h
  simp only [hflow, hscol, hnds, hnde, Bool.false_and, Bool.and_false, beq_self_eq_true,
    Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
  generalize hfn : scanDirective s = result at h
  cases result with
  | error e => simp at h
  | ok s_d =>
    simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact scanDirective_trace s sp hcorr hpeek s_d hfn

end DocBridgeConsumers

/-! ## S3 slice (3), first PR: the flow-indicator dispatcher's `[` / `{` / `]` / `}` / `,` arms and the
content dispatcher's `"` / `'` arms (item 464) -/

section FlowBridgeConsumers
open L4YAML.Surface L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.FlowBridge

/-- The `[` arm of `scanNextToken_dispatchFlowIndicators` is `scanFlowSequenceStart_trace`. -/
lemma dispatchFlowIndicators_flowSeqStart_trace (s : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr s sp) (hpeek : s.peek? = some '[') (s'' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s '[' = .ok (some s'')) :
    ∃ sp', s''.tokens = s.tokens.push (indicatorTok s .flowSequenceStart) ∧
      ScannerSurfCorr s'' sp' ∧ Lift (GLit '[') sp sp' [] := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hfa : scanNextToken_checkFlowAdjacency s '[' = r at h
  cases r with
  | error e => simp at h
  | ok u =>
    simp only [beq_self_eq_true, ↓reduceIte, Except.ok.injEq, Option.some.injEq] at h
    subst h
    exact scanFlowSequenceStart_trace s sp hcorr hpeek

/-- The `{` arm of `scanNextToken_dispatchFlowIndicators` is `scanFlowMappingStart_trace`. -/
lemma dispatchFlowIndicators_flowMapStart_trace (s : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr s sp) (hpeek : s.peek? = some '{') (s'' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s '{' = .ok (some s'')) :
    ∃ sp', s''.tokens = s.tokens.push (indicatorTok s .flowMappingStart) ∧
      ScannerSurfCorr s'' sp' ∧ Lift (GLit '{') sp sp' [] := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hfa : scanNextToken_checkFlowAdjacency s '{' = r at h
  cases r with
  | error e => simp at h
  | ok u =>
    simp only [beq_self_eq_true, ↓reduceIte, Except.ok.injEq, Option.some.injEq,
      show ('{' == '[') = false by decide, show ('{' == ']') = false by decide,
      Bool.false_eq_true] at h
    subst h
    exact scanFlowMappingStart_trace s sp hcorr hpeek

/-- The `]` arm of `scanNextToken_dispatchFlowIndicators` is `scanFlowSequenceEnd_trace`
(inside a flow sequence; `validateFlowClose` accepted). -/
lemma dispatchFlowIndicators_flowSeqEnd_trace (s : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr s sp) (hpeek : s.peek? = some ']') (s'' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s ']' = .ok (some s'')) :
    ∃ sp', s''.tokens = s.tokens.push (indicatorTok s .flowSequenceEnd) ∧
      ScannerSurfCorr s'' sp' ∧ Lift (GLit ']') sp sp' [] := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hfa : scanNextToken_checkFlowAdjacency s ']' = r at h
  cases r with
  | error e => simp at h
  | ok u =>
    simp only [beq_self_eq_true, ↓reduceIte, show (']' == '[') = false by decide,
      Bool.false_eq_true] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · generalize hvc : validateFlowClose (scanFlowSequenceEnd s) = vr at h
        cases vr with
        | error e => simp at h
        | ok u' =>
          simp only [Except.ok.injEq, Option.some.injEq] at h
          subst h
          exact scanFlowSequenceEnd_trace s sp hcorr hpeek

/-- The `}` arm of `scanNextToken_dispatchFlowIndicators` is `scanFlowMappingEnd_trace`. -/
lemma dispatchFlowIndicators_flowMapEnd_trace (s : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr s sp) (hpeek : s.peek? = some '}') (s'' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s '}' = .ok (some s'')) :
    ∃ sp', s''.tokens = s.tokens.push (indicatorTok s .flowMappingEnd) ∧
      ScannerSurfCorr s'' sp' ∧ Lift (GLit '}') sp sp' [] := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hfa : scanNextToken_checkFlowAdjacency s '}' = r at h
  cases r with
  | error e => simp at h
  | ok u =>
    simp only [beq_self_eq_true, ↓reduceIte, show ('}' == '[') = false by decide,
      show ('}' == ']') = false by decide, show ('}' == '{') = false by decide,
      Bool.false_eq_true] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · generalize hvc : validateFlowClose (scanFlowMappingEnd s) = vr at h
        cases vr with
        | error e => simp at h
        | ok u' =>
          simp only [Except.ok.injEq, Option.some.injEq] at h
          subst h
          exact scanFlowMappingEnd_trace s sp hcorr hpeek

/-- The `,` arm of `scanNextToken_dispatchFlowIndicators` is `scanFlowEntry_trace`. -/
lemma dispatchFlowIndicators_flowEntry_trace (s : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr s sp) (hpeek : s.peek? = some ',') (s'' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s ',' = .ok (some s'')) :
    ∃ sp', s''.tokens = s.tokens.push (indicatorTok s .flowEntry) ∧
      ScannerSurfCorr s'' sp' ∧ Lift (GLit ',') sp sp' [] := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hfa : scanNextToken_checkFlowAdjacency s ',' = r at h
  cases r with
  | error e => simp at h
  | ok u =>
    simp only [beq_self_eq_true, ↓reduceIte, show (',' == '[') = false by decide,
      show (',' == ']') = false by decide, show (',' == '{') = false by decide,
      show (',' == '}') = false by decide, Bool.false_eq_true] at h
    split at h
    · simp at h
    · generalize hfe : scanFlowEntry s = fr at h
      cases fr with
      | error e => simp at h
      | ok s_e =>
        simp only [Except.ok.injEq, Option.some.injEq] at h
        subst h
        exact scanFlowEntry_trace s sp hcorr hpeek s_e hfe

/-- The `"` arm of `scanNextToken_dispatchContent` is `scanDoubleQuoted_trace` (the arm's
`simpleKey.endLine` touch-up leaves the tokens alone). -/
lemma dispatchContent_doubleQuoted_trace (s : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr s sp) (hpeek : s.peek? = some '"') (s'' : ScannerState)
    (h : scanNextToken_dispatchContent s '"' = .ok s'') :
    ∃ sp' v, s''.tokens = s.tokens.push (indicatorTok s (.scalar v .doubleQuoted)) ∧
      ScannerSurfCorr s'' sp' ∧ TFlowContent 0 .blockIn sp sp' [] := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, Except.bind, pure, Except.pure, Pure.pure,
    show ('"' == '&') = false by decide, show ('"' == '*') = false by decide,
    show ('"' == '!') = false by decide, show ('"' == '|') = false by decide,
    show ('"' == '>') = false by decide, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    beq_self_eq_true] at h
  generalize hdq : scanDoubleQuoted s = dr at h
  cases dr with
  | error e => simp at h
  | ok s_q =>
    obtain ⟨sp', v, htok, hcorr', htr⟩ := scanDoubleQuoted_trace s sp hcorr hpeek s_q hdq
    refine ⟨sp', v, ?_, ?_, htr⟩
    · have : s''.tokens = s_q.tokens := by
        simp only [Except.ok.injEq] at h; subst h; split <;> rfl
      rw [this, htok]
    · have : s'' = s_q ∨ s'' = { s_q with simpleKey := { s_q.simpleKey with endLine := s_q.line } } := by
        simp only [Except.ok.injEq] at h; subst h; split
        · exact Or.inr rfl
        · exact Or.inl rfl
      rcases this with rfl | rfl
      · exact hcorr'
      · exact ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix,
          hcorr'.indent_cols_nonneg⟩

/-- The `'` arm of `scanNextToken_dispatchContent` is `scanSingleQuoted_trace`. -/
lemma dispatchContent_singleQuoted_trace (s : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr s sp) (hpeek : s.peek? = some '\'') (s'' : ScannerState)
    (h : scanNextToken_dispatchContent s '\'' = .ok s'') :
    ∃ sp' v, s''.tokens = s.tokens.push (indicatorTok s (.scalar v .singleQuoted)) ∧
      ScannerSurfCorr s'' sp' ∧ TFlowContent 0 .blockIn sp sp' [] := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, Except.bind, pure, Except.pure, Pure.pure,
    show ('\'' == '&') = false by decide, show ('\'' == '*') = false by decide,
    show ('\'' == '!') = false by decide, show ('\'' == '|') = false by decide,
    show ('\'' == '>') = false by decide, show ('\'' == '"') = false by decide,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true] at h
  generalize hsq : scanSingleQuoted s = dr at h
  cases dr with
  | error e => simp at h
  | ok s_q =>
    obtain ⟨sp', v, htok, hcorr', htr⟩ := scanSingleQuoted_trace s sp hcorr hpeek s_q hsq
    refine ⟨sp', v, ?_, ?_, htr⟩
    · have : s''.tokens = s_q.tokens := by
        simp only [Except.ok.injEq] at h; subst h; split <;> rfl
      rw [this, htok]
    · have : s'' = s_q ∨ s'' = { s_q with simpleKey := { s_q.simpleKey with endLine := s_q.line } } := by
        simp only [Except.ok.injEq] at h; subst h; split
        · exact Or.inr rfl
        · exact Or.inl rfl
      rcases this with rfl | rfl
      · exact hcorr'
      · exact ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix,
          hcorr'.indent_cols_nonneg⟩

end FlowBridgeConsumers

end L4YAML.Proofs.Serialization.ScannerShape

end Blanket
