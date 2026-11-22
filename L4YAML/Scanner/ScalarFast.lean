/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Scanner.Scalar
@[expose] public section Blanket

/-!
# Scanner — Linear-time scalar loops

`collectDoubleQuotedLoop`, `collectSingleQuotedLoop` and
`collectPlainScalarLoop` (`Scalar.lean`) are the *specification* loops: dozens
of lemmas unfold them step by step.  As executables they are quadratic in the
number of line breaks of a multi-line scalar:

- double-quoted rebuilds the kept prefix through a `List Char` at every
  fold (`String.ofList (content.toList.take protectedLen)`);
- single-quoted re-trims the whole accumulator at every fold
  (`trimTrailingWS content`);
- plain keeps the pre-fold `content` alive for the no-gain rewind, so the
  `content ++ folded` append sees a shared string and copies it.

This file gives each loop a **twin** that does the same work with a uniquely
referenced accumulator, proves the twin equal to the specification loop, and
registers the `scanX` equalities with `@[csimp]`, so compiled code (the Lean
API, `native_decide`, the FFI) runs the twins while every proof keeps reading
the specification loops.  Nothing observable changes: the `csimp` lemmas are
kernel-checked equalities.

- Quoted twins carry the accumulator as `content ++ pending`, where `pending`
  is the trailing white run a fold may trim — the double-quoted `protectedLen`
  is `content.length`, the single-quoted `trimTrailingWS` boundary is the
  `content`/`pending` split.  A fold drops `pending` in O(1).
- The plain twin remembers only the pre-fold *length*; on a no-gain rewind it
  rebuilds the pre-fold content from the (necessarily unextended) result.  That
  happens at most once per scalar, so the scan stays linear.
-/

namespace L4YAML.Scanner

open L4YAML.CharPredicates

/-! ## Double-quoted -/

/-- Linear twin of `collectDoubleQuotedLoop`: the specification's `content` is
    `kept ++ pending` and its `protectedLen` is `kept.length`. -/
def collectDoubleQuotedLoopFast (s : ScannerState) (kept pending : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    Except ScanError (String × ScannerState) :=
  match fuel with
  | 0 => .error (.unterminatedScalar .doubleQuoted startPos.line)
  | fuel' + 1 =>
    match s.peek? with
    | none => .error (.unterminatedScalar .doubleQuoted startPos.line)
    | some '"' => .ok (kept ++ pending, s.advance)
    | some '\\' =>
      let s_after_backslash := s.advance
      match s_after_backslash.peek? with
      | some c =>
        if isLineBreakBool c then do
          let (folded, s_land) ← foldQuotedNewlines s_after_backslash
          if atDocumentStart s_land || atDocumentEnd s_land then
            throw (.documentMarkerInScalar .doubleQuoted startPos.line)
          if (s_land.col : Int) ≤ currentIndent then
            throw (.underIndentedScalar .doubleQuoted s_land.line)
          if folded == " " then
            collectDoubleQuotedLoopFast s_land kept pending fuel' startPos inFlow currentIndent inputEnd
          else
            collectDoubleQuotedLoopFast s_land (kept ++ pending ++ folded) "" fuel' startPos inFlow currentIndent inputEnd
        else do
          let (ch, s_after_escape) ← processEscape s_after_backslash
          collectDoubleQuotedLoopFast s_after_escape ((kept ++ pending).push ch) "" fuel' startPos inFlow currentIndent inputEnd
      | none => .error (.unterminatedEscape s_after_backslash.line)
    | some c =>
      if isLineBreakBool c then do
        let (folded, s') ← foldQuotedNewlines s
        if atDocumentStart s' || atDocumentEnd s' then
          throw (.documentMarkerInScalar .doubleQuoted startPos.line)
        if (s'.col : Int) ≤ currentIndent then
          throw (.underIndentedScalar .doubleQuoted s'.line)
        if folded == " " then
          collectDoubleQuotedLoopFast s' kept " " fuel' startPos inFlow currentIndent inputEnd
        else
          collectDoubleQuotedLoopFast s' (kept ++ folded) "" fuel' startPos inFlow currentIndent inputEnd
      else if !isNbJsonBool c then
        .error (.invalidControlChar c .doubleQuoted s.line s.col)
      else if c == ' ' || c == '\t' then
        collectDoubleQuotedLoopFast s.advance kept (pending.push c) fuel' startPos inFlow currentIndent inputEnd
      else
        collectDoubleQuotedLoopFast s.advance ((kept ++ pending).push c) "" fuel' startPos inFlow currentIndent inputEnd

/-- `scanDoubleQuoted` over the linear twin. -/
def scanDoubleQuotedFast (s : ScannerState) : Except ScanError ScannerState := do
  let startPos := s.currentPos
  let s_after_open := s.advance
  let fuel := s.inputEnd - s_after_open.offset + 1
  let (content, s_after_close) ← collectDoubleQuotedLoopFast s_after_open "" "" fuel startPos s.inFlow s.currentIndent s.inputEnd
  if !s.inFlow then
    validateTrailingContent s_after_close s.inputEnd
  let s_with_token := s_after_close.emitAt startPos (.scalar content .doubleQuoted)
  .ok { s_with_token with simpleKeyAllowed := false, needIndentCheck := false }

/-! ## Single-quoted -/

/-- Linear twin of `collectSingleQuotedLoop`: the specification's `content` is
    `content ++ pending`, with `pending` the trailing space/tab run that
    `trimTrailingWS` would drop at a fold. -/
def collectSingleQuotedLoopFast (s : ScannerState) (content pending : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    Except ScanError (String × ScannerState) :=
  match fuel with
  | 0 => .error (.unterminatedScalar .singleQuoted startPos.line)
  | fuel' + 1 =>
    match s.peek? with
    | none => .error (.unterminatedScalar .singleQuoted startPos.line)
    | some '\'' =>
      let s_after_quote := s.advance
      match s_after_quote.peek? with
      | some '\'' =>
        collectSingleQuotedLoopFast s_after_quote.advance ((content ++ pending).push '\'') "" fuel' startPos inFlow currentIndent inputEnd
      | _ =>
        .ok (content ++ pending, s_after_quote)
    | some c =>
      if isLineBreakBool c then do
        let (folded, s') ← foldQuotedNewlines s
        if atDocumentStart s' || atDocumentEnd s' then
          throw (.documentMarkerInScalar .singleQuoted startPos.line)
        if (s'.col : Int) ≤ currentIndent then
          throw (.underIndentedScalar .singleQuoted s'.line)
        if folded == " " then
          collectSingleQuotedLoopFast s' content " " fuel' startPos inFlow currentIndent inputEnd
        else
          collectSingleQuotedLoopFast s' (content ++ folded) "" fuel' startPos inFlow currentIndent inputEnd
      else if !isNbJsonBool c then
        .error (.invalidControlChar c .singleQuoted s.line s.col)
      else if c == ' ' || c == '\t' then
        collectSingleQuotedLoopFast s.advance content (pending.push c) fuel' startPos inFlow currentIndent inputEnd
      else
        collectSingleQuotedLoopFast s.advance ((content ++ pending).push c) "" fuel' startPos inFlow currentIndent inputEnd

/-- `scanSingleQuoted` over the linear twin. -/
def scanSingleQuotedFast (s : ScannerState) : Except ScanError ScannerState := do
  let startPos := s.currentPos
  let s_after_open := s.advance
  let fuel := s.inputEnd - s_after_open.offset + 1
  let (content, s_after_close) ← collectSingleQuotedLoopFast s_after_open "" "" fuel startPos s.inFlow s.currentIndent s.inputEnd
  if !s.inFlow then
    validateTrailingContent s_after_close s.inputEnd
  let s_with_token := s_after_close.emitAt startPos (.scalar content .singleQuoted)
  .ok { s_with_token with simpleKeyAllowed := false, needIndentCheck := false }

/-! ## Plain -/

/-- Twin of `collectPlainScalar_handleBlockLineBreak` that hands `content` back
    untouched when the continuation is refused, so the caller need not keep its
    own reference alive across the call. -/
def collectPlainScalar_handleBlockLineBreakFast (s : ScannerState)
    (content : String) (contentIndent : Nat) (inputEnd : Nat) :
    Sum String (String × ScannerState) :=
  let s_after_newline := consumeNewline s
  let bfuel := inputEnd - s_after_newline.offset + 1
  let (emptyCount, s_after_blanks) := skipBlankLinesLoop s_after_newline 0 bfuel inputEnd
  let s_after_spaces := skipSpaces s_after_blanks
  if s_after_spaces.col < contentIndent then
    .inl content
  else if atDocumentBoundary s_after_spaces then
    .inl content
  else
    let s_after_sep := skipWhitespace s_after_spaces
    let content' := if emptyCount > 0 then
      content ++ String.ofList (List.replicate emptyCount '\n')
    else
      content ++ " "
    .inr (content', s_after_sep)

/-- Linear twin of `collectPlainScalarLoop`.  The only difference is the
    no-gain rewind: the specification returns the pre-fold `content`, which
    keeps it alive across the recursive call and makes `content ++ folded`
    copy; the twin keeps just `content.length` and truncates the result, which
    the no-gain test guarantees is exactly `content ++ folded`. -/
def collectPlainScalarLoopFast (s : ScannerState) (content : String) (spaces : String) (fuel : Nat)
    (inFlow : Bool) (contentIndent : Nat) (inputEnd : Nat) :
    Except ScanError PlainScalarResult :=
  match fuel with
  | 0 => .ok { content, spaces, state := s, terminated := false }
  | fuel' + 1 =>
    match s.peek? with
    | none => .ok { content, spaces, state := s, terminated := true }
    | some c =>
      match collectPlainScalar_terminates? c s content spaces inFlow with
      | some result => .ok result
      | none =>
        if isLineBreakBool c then
          if inFlow then do
            let (folded, s_after_fold) ← foldQuotedNewlines s
            match s_after_fold.peek? with
            | some '#' =>
              .ok { content, spaces, state := s, terminated := true }
            | _ => do
              if s_after_fold.currentIndent ≥ 0
                  && (s_after_fold.col : Int) ≤ s_after_fold.currentIndent then
                throw (.underIndentedScalar .plain s_after_fold.line)
              let baseLen := content.length
              let content' := content ++ folded
              let prevLen := content'.length
              match collectPlainScalarLoopFast s_after_fold content' "" fuel' inFlow contentIndent inputEnd with
              | .ok result =>
                if result.content.length ≤ prevLen then
                  .ok { content := String.ofList (result.content.toList.take baseLen), spaces, state := s, terminated := true }
                else .ok result
              | .error e => .error e
          else
            let baseLen := content.length
            match collectPlainScalar_handleBlockLineBreakFast s content contentIndent inputEnd with
            | .inl content =>
              .ok { content, spaces, state := s, terminated := true }
            | .inr (content', s') =>
              match s'.peek? with
              | some '#' =>
                .ok { content := String.ofList (content'.toList.take baseLen), spaces, state := s, terminated := true }
              | _ =>
                let prevLen := content'.length
                match collectPlainScalarLoopFast s' content' "" fuel' inFlow contentIndent inputEnd with
                | .ok result =>
                  if result.content.length ≤ prevLen then
                    .ok { content := String.ofList (result.content.toList.take baseLen), spaces, state := s, terminated := true }
                  else .ok result
                | .error e => .error e
        else if isWhiteSpaceBool c then
          collectPlainScalarLoopFast s.advance content (spaces.push c) fuel' inFlow contentIndent inputEnd
        else
          if !isPlainSafeBool c inFlow then
            .ok { content, spaces, state := s, terminated := true }
          else
            let content' := content ++ spaces ++ (String.singleton c)
            collectPlainScalarLoopFast s.advance content' "" fuel' inFlow contentIndent inputEnd

/-- `scanPlainScalar` over the linear twin. -/
def scanPlainScalarFast (s : ScannerState) : Except ScanError ScannerState := do
  let startPos := s.currentPos
  let inFlow := s.inFlow
  let contentIndent := if inFlow then s.col
    else (max 0 (s.currentIndent + 1)).toNat
  let fuel := (s.inputEnd - s.offset + 1) * 2
  let result ← collectPlainScalarLoopFast s "" "" fuel inFlow contentIndent s.inputEnd
  let content_trimmed := trimTrailingWS result.content
  let s_with_token := result.state.emitAt startPos (.scalar content_trimmed .plain)
  .ok { s_with_token with simpleKeyAllowed := false, needIndentCheck := false }

/-! ## Equivalence with the specification loops -/

namespace ScalarFast

/-- The protected prefix of `kept ++ pending` of length `kept.length` is `kept`. -/
lemma ofList_take_length_append (kept pending : String) :
    String.ofList ((kept ++ pending).toList.take kept.length) = kept := by
  rw [String.toList_append, ← String.length_toList, List.take_left, String.ofList_toList]

lemma append_push (a b : String) (c : Char) : a ++ b.push c = (a ++ b).push c := by
  rw [String.push_eq_append, String.push_eq_append, String.append_assoc]

lemma collectDoubleQuotedLoopFast_eq (fuel : Nat) :
    ∀ (s : ScannerState) (kept pending : String) (startPos : YamlPos) (inFlow : Bool)
      (currentIndent : Int) (inputEnd : Nat),
      collectDoubleQuotedLoopFast s kept pending fuel startPos inFlow currentIndent inputEnd =
      collectDoubleQuotedLoop s (kept ++ pending) fuel startPos inFlow currentIndent inputEnd
        kept.length := by
  induction fuel with
  | zero =>
    intro s kept pending startPos inFlow currentIndent inputEnd
    unfold collectDoubleQuotedLoopFast collectDoubleQuotedLoop
    rfl
  | succ fuel' ih =>
    intro s kept pending startPos inFlow currentIndent inputEnd
    unfold collectDoubleQuotedLoopFast collectDoubleQuotedLoop
    dsimp only
    rw [ofList_take_length_append]
    split
    all_goals (rename_i heq; simp only [heq])
    repeat' (first
      | rfl
      | (split <;> try (rename_i heq; simp only [heq]))
      | simp only [bind, Except.bind])
    all_goals (first
      | (rw [ih]; done)
      | (rw [ih, String.append_empty]; done)
      | (rw [ih, String.append_empty, String.length_append]; done)
      | (rw [ih, append_push]; done)
      | (rename_i h; rw [ih, Nat.add_zero, eq_of_beq h]; done)
      | (trace_state; sorry))

/-! ### Single-quoted -/

/-- Dropping a run of trimmable white from the end of a list leaves nothing. -/
lemma dropWhile_all_eq_nil (l : List Char)
    (hl : l.all (fun c => c == ' ' || c == '\t') = true) :
    l.dropWhile (fun c => c == ' ' || c == '\t') = [] := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hl
    simp [hl.1, ih hl.2]

lemma trimTrailingWS_append_ws (x p : String)
    (hp : p.toList.all (fun c => c == ' ' || c == '\t') = true) :
    trimTrailingWS (x ++ p) = trimTrailingWS x := by
  unfold trimTrailingWS
  rw [String.toList_append, List.reverse_append, List.dropWhile_append,
    dropWhile_all_eq_nil _ (by simpa using hp)]
  simp

lemma trimTrailingWS_push_nonws (x : String) (c : Char)
    (hc : ¬ (c == ' ' || c == '\t') = true) :
    trimTrailingWS (x.push c) = x.push c := by
  apply String.ext
  unfold trimTrailingWS
  rw [String.toList_push, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.dropWhile_cons]
  simp [hc]

lemma trimTrailingWS_append_newlines (x : String) (n : Nat) (hn : n > 0) :
    trimTrailingWS (x ++ String.ofList (List.replicate n '\n')) =
      x ++ String.ofList (List.replicate n '\n') := by
  apply String.ext
  unfold trimTrailingWS
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [String.toList_append, String.toList_ofList, List.replicate_succ']

lemma all_ws_push (p : String) (c : Char)
    (hp : p.toList.all (fun c => c == ' ' || c == '\t') = true)
    (hc : (c == ' ' || c == '\t') = true) :
    (p.push c).toList.all (fun c => c == ' ' || c == '\t') = true := by
  simp [String.toList_push, hp, hc]

lemma foldQuotedNewlines_form (s : ScannerState) (v : String × ScannerState)
    (h : foldQuotedNewlines s = .ok v) :
    (v.fst = " ") ∨ (∃ n, n > 0 ∧ v.fst = String.ofList (List.replicate n '\n')) := by
  unfold foldQuotedNewlines at h
  dsimp only at h
  split at h
  · split at h
    · simp only [pure, Except.pure] at h
      split at h <;> contradiction
    · split at h
      · rename_i hempty
        have := Except.ok.inj h
        subst this
        right; exact ⟨_, hempty, rfl⟩
      · have := Except.ok.inj h
        subst this
        left; rfl
  · split at h
    · rename_i hempty
      have := Except.ok.inj h
      subst this
      right; exact ⟨_, hempty, rfl⟩
    · have := Except.ok.inj h
      subst this
      left; rfl

/-- A fold that is not a single space appends line feeds, which
    `trimTrailingWS` keeps. -/
lemma trimTrailingWS_append_fold (content : String) (s : ScannerState) (v : String × ScannerState)
    (heq : foldQuotedNewlines s = .ok v) (hne : ¬ (v.fst == " ") = true) :
    trimTrailingWS (content ++ v.fst) = content ++ v.fst := by
  rcases foldQuotedNewlines_form s v heq with hsp | ⟨n, hn, hnl⟩
  · exact absurd (by rw [hsp]; rfl) hne
  · rw [hnl]; exact trimTrailingWS_append_newlines content n hn

lemma collectSingleQuotedLoopFast_eq (fuel : Nat) :
    ∀ (s : ScannerState) (content pending : String) (startPos : YamlPos) (inFlow : Bool)
      (currentIndent : Int) (inputEnd : Nat),
      trimTrailingWS content = content →
      pending.toList.all (fun c => c == ' ' || c == '\t') = true →
      collectSingleQuotedLoopFast s content pending fuel startPos inFlow currentIndent inputEnd =
      collectSingleQuotedLoop s (content ++ pending) fuel startPos inFlow currentIndent inputEnd := by
  induction fuel with
  | zero =>
    intro s content pending startPos inFlow currentIndent inputEnd _ _
    unfold collectSingleQuotedLoopFast collectSingleQuotedLoop
    rfl
  | succ fuel' ih =>
    intro s content pending startPos inFlow currentIndent inputEnd hc hp
    have hT : trimTrailingWS (content ++ pending) = content := by
      rw [trimTrailingWS_append_ws _ _ hp, hc]
    unfold collectSingleQuotedLoopFast collectSingleQuotedLoop
    dsimp only
    rw [hT]
    split
    all_goals (rename_i heq; simp only [heq])
    repeat' (first
      | rfl
      | (split <;> try (rename_i heq; simp only [heq]))
      | simp only [bind, Except.bind])
    all_goals (first
      | (rw [ih _ _ _ _ _ _ _ (trimTrailingWS_push_nonws _ _ (by decide)) (by decide),
            String.append_empty]; done)
      | (rename_i h; rw [ih _ _ _ _ _ _ _ hc (by simp), eq_of_beq h]; done)
      | (rename_i h; rw [ih _ _ _ _ _ _ _
            (trimTrailingWS_append_fold _ _ _ ‹foldQuotedNewlines _ = Except.ok _› h)
            (by decide), String.append_empty]; done)
      | (rw [ih _ _ _ _ _ _ _ hc (all_ws_push _ _ hp ‹_›), append_push]; done)
      | (rw [ih _ _ _ _ _ _ _ (trimTrailingWS_push_nonws _ _ ‹_›) (by decide),
            String.append_empty]; done)
      | (trace_state; sorry))

/-! ### Plain -/

lemma terminates_content (c : Char) (s : ScannerState) (content spaces : String) (inFlow : Bool)
    (r : PlainScalarResult)
    (h : collectPlainScalar_terminates? c s content spaces inFlow = some r) :
    r.content = content := by
  unfold collectPlainScalar_terminates? at h
  split at h
  · injection h with h; rw [← h]
  · split at h
    · simp only at h
      split at h <;> (split at h <;> first | (injection h with h; rw [← h]) | contradiction)
    · split at h
      · injection h with h; rw [← h]
      · split at h
        · injection h with h; rw [← h]
        · contradiction

lemma handleBlockLineBreak_form
    (s : ScannerState) (content : String) (contentIndent inputEnd : Nat)
    (content' : String) (s' : ScannerState)
    (h : collectPlainScalar_handleBlockLineBreak s content contentIndent inputEnd = some (content', s')) :
    ∃ t, content' = content ++ t := by
  unfold collectPlainScalar_handleBlockLineBreak at h
  simp only [] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        exact ⟨_, this.1.symm⟩
      · have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        exact ⟨_, this.1.symm⟩

lemma handleBlockLineBreakFast_inl
    (s : ScannerState) (content : String) (contentIndent inputEnd : Nat) (c : String)
    (h : collectPlainScalar_handleBlockLineBreakFast s content contentIndent inputEnd = .inl c) :
    c = content ∧ collectPlainScalar_handleBlockLineBreak s content contentIndent inputEnd = none := by
  unfold collectPlainScalar_handleBlockLineBreakFast at h
  unfold collectPlainScalar_handleBlockLineBreak
  simp only [] at h ⊢
  split at h
  · exact ⟨(Sum.inl.inj h).symm, by rename_i hlt; simp only [hlt, ite_true]⟩
  · split at h
    · exact ⟨(Sum.inl.inj h).symm, by rename_i hlt hdoc; simp only [hlt, hdoc, ite_false, ite_true]⟩
    · contradiction

lemma handleBlockLineBreakFast_inr
    (s : ScannerState) (content : String) (contentIndent inputEnd : Nat) (p : String × ScannerState)
    (h : collectPlainScalar_handleBlockLineBreakFast s content contentIndent inputEnd = .inr p) :
    collectPlainScalar_handleBlockLineBreak s content contentIndent inputEnd = some p := by
  unfold collectPlainScalar_handleBlockLineBreakFast at h
  unfold collectPlainScalar_handleBlockLineBreak
  simp only [] at h ⊢
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i hlt hdoc
      simp only [hlt, hdoc, ite_false]
      exact congrArg some (Sum.inr.inj h)

/-- The specification loop only ever extends its accumulator. -/
lemma collectPlainScalarLoop_prefix (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (inFlow : Bool) (contentIndent inputEnd : Nat)
      (result : PlainScalarResult),
      collectPlainScalarLoop s content spaces fuel inFlow contentIndent inputEnd = .ok result →
      content.toList <+: result.content.toList := by
  induction fuel with
  | zero =>
    intro s content spaces inFlow contentIndent inputEnd result h
    unfold collectPlainScalarLoop at h; injection h with h_eq; cases h_eq; exact List.prefix_rfl
  | succ fuel' ih =>
    intro s content spaces inFlow contentIndent inputEnd result h
    unfold collectPlainScalarLoop at h; split at h
    · injection h with h_eq; cases h_eq; exact List.prefix_rfl
    · rename_i c hpeek; split at h
      · rename_i hterm; injection h with h_eq; cases h_eq
        exact (terminates_content _ _ _ _ _ _ hterm) ▸ List.prefix_rfl
      · rename_i hterm; split at h
        · split at h
          · simp only [bind, Except.bind] at h; split at h <;> try contradiction
            rename_i fold_result heq; cases fold_result with
            | mk folded s_fold =>
              split at h
              · injection h with h_eq; cases h_eq; exact List.prefix_rfl
              · split at h
                · contradiction
                generalize h_loop : collectPlainScalarLoop s_fold (content ++ folded) "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; exact List.prefix_rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    exact List.IsPrefix.trans ⟨folded.toList, String.toList_append.symm⟩
                      (ih s_fold (content ++ folded) "" _ _ _ _ h_loop)
                | error e => simp at h
          · split at h
            · injection h with h_eq; cases h_eq; exact List.prefix_rfl
            · rename_i content' s' hblk; split at h
              · injection h with h_eq; cases h_eq; exact List.prefix_rfl
              · generalize h_loop : collectPlainScalarLoop s' content' "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; exact List.prefix_rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    obtain ⟨t, rfl⟩ := handleBlockLineBreak_form s content contentIndent inputEnd content' s' hblk
                    exact List.IsPrefix.trans ⟨_, String.toList_append.symm⟩ (ih _ _ "" _ _ _ _ h_loop)
                | error e => simp at h
        · split at h
          · exact ih s.advance content (spaces.push c) _ _ _ _ h
          · split at h
            · injection h with h_eq; cases h_eq; exact List.prefix_rfl
            · exact List.IsPrefix.trans
                ⟨(spaces ++ String.singleton c).toList, by
                  simp [String.toList_append, List.append_assoc]⟩
                (ih _ _ "" _ _ _ _ h)

/-- A prefix that is at least as long is the whole string. -/
lemma eq_of_prefix_length_le {a b : String}
    (hpre : a.toList <+: b.toList) (hle : b.length ≤ a.length) : b = a := by
  obtain ⟨t, ht⟩ := hpre
  have hlen := congrArg List.length ht
  rw [List.length_append, String.length_toList, String.length_toList] at hlen
  have ht0 : t = [] := List.length_eq_zero_iff.mp (by omega)
  subst ht0
  rw [List.append_nil] at ht
  exact String.ext ht.symm

/-- The no-gain rewind recovers the pre-fold content from the result. -/
lemma nogain_restore (content t : String) (result : PlainScalarResult)
    (hpre : (content ++ t).toList <+: result.content.toList)
    (hle : result.content.length ≤ (content ++ t).length) :
    String.ofList (result.content.toList.take content.length) = content := by
  rw [eq_of_prefix_length_le hpre hle, ofList_take_length_append]

lemma collectPlainScalarLoopFast_eq (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (inFlow : Bool) (contentIndent inputEnd : Nat),
      collectPlainScalarLoopFast s content spaces fuel inFlow contentIndent inputEnd =
      collectPlainScalarLoop s content spaces fuel inFlow contentIndent inputEnd := by
  induction fuel with
  | zero =>
    intro s content spaces inFlow contentIndent inputEnd
    unfold collectPlainScalarLoopFast collectPlainScalarLoop
    rfl
  | succ fuel' ih =>
    intro s content spaces inFlow contentIndent inputEnd
    unfold collectPlainScalarLoopFast collectPlainScalarLoop
    simp only [ih]
    split
    all_goals (rename_i heq; simp only [heq])
    repeat' (first
      | rfl
      | (obtain ⟨rfl, h2⟩ := handleBlockLineBreakFast_inl _ _ _ _ _
            ‹collectPlainScalar_handleBlockLineBreakFast _ _ _ _ = Sum.inl _›
         simp only [h2])
      | (have h2 := handleBlockLineBreakFast_inr _ _ _ _ _
            ‹collectPlainScalar_handleBlockLineBreakFast _ _ _ _ = Sum.inr _›
         simp only [h2])
      | (split <;> try (rename_i heq; simp only [heq]))
      | simp only [bind, Except.bind])
    all_goals (first
      | (rw [nogain_restore _ _ _
            (collectPlainScalarLoop_prefix _ _ _ _ _ _ _ _
              ‹collectPlainScalarLoop _ _ _ _ _ _ _ = Except.ok _›) ‹_›]; done)
      | (obtain ⟨t, rfl⟩ := handleBlockLineBreak_form _ _ _ _ _ _
            ‹collectPlainScalar_handleBlockLineBreak _ _ _ _ = some _›
         first
          | (rw [ofList_take_length_append]; done)
          | (rw [nogain_restore _ _ _
              (collectPlainScalarLoop_prefix _ _ _ _ _ _ _ _
                ‹collectPlainScalarLoop _ _ _ _ _ _ _ = Except.ok _›) ‹_›]; done))
      | (trace_state; sorry))

end ScalarFast

/-! ## Compiled code runs the twins -/

@[csimp] lemma scanDoubleQuoted_eq_fast : @scanDoubleQuoted = @scanDoubleQuotedFast := by
  funext s
  unfold scanDoubleQuoted scanDoubleQuotedFast
  simp only [ScalarFast.collectDoubleQuotedLoopFast_eq, String.append_empty, String.length_empty]

@[csimp] lemma scanSingleQuoted_eq_fast : @scanSingleQuoted = @scanSingleQuotedFast := by
  funext s
  unfold scanSingleQuoted scanSingleQuotedFast
  simp only [ScalarFast.collectSingleQuotedLoopFast_eq _ _ "" "" _ _ _ _ (by decide) (by decide),
    String.append_empty]

@[csimp] lemma scanPlainScalar_eq_fast : @scanPlainScalar = @scanPlainScalarFast := by
  funext s
  unfold scanPlainScalar scanPlainScalarFast
  simp only [ScalarFast.collectPlainScalarLoopFast_eq]

end L4YAML.Scanner
