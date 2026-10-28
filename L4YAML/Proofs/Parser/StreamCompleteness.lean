module

public import L4YAML.Proofs.Parser.TokenGrammar
-- `go`/`tokenEvent` are sealed by their producer; `import all` unseals their bodies for
-- `perTokenTrace_eq_tokenEvents` (precedent: Proofs/Output/*Scannability).
import all L4YAML.Proofs.Serialization.TokenEvents
public import L4YAML.Proofs.Parser.ParserWellBehaved

/-! Module-private by default: only `parseStream_accepts` is exported; the per-token
scaffolding below and every lemma over it stay internal (EVENTSOF-CONCEPT §9, S5 slice 2). -/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Stream completeness — `TokenGrammar ∧ TokenStateOk → parseStream = .ok`

The parser half of the grammar-completeness converse: a token array of the
right shape (`TG`) under the right per-document state (`TokenStateOk`) is
accepted by `parseStream`.  The proof is one induction on the `TG`
derivation, carrying `Inv` (parser state ⊇ the event environment at the
current position) and a span-proportional fuel bound. -/

namespace L4YAML.Proofs.TokenGrammar

open L4YAML
open L4YAML.TokenParser
open L4YAML.Proofs.ParserWellBehaved
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents

/-! ## Environments along the token array -/

/-- The environment update `WellFormedFrom` performs per event. -/
def stepEnv (env : Env) : Event → Env
  | .beginDocument => {}
  | .endDocument => {}
  | .defineAnchor n => { env with anchors := n :: env.anchors }
  | .useAlias _ => env
  | .declareTag h => { env with tagHandles := h :: env.tagHandles }
  | .useTag _ => env

def envAfter (env : Env) (evs : List Event) : Env := evs.foldl stepEnv env

lemma envAfter_append (env : Env) (a b : List Event) :
    envAfter env (a ++ b) = envAfter (envAfter env a) b :=
  List.foldl_append ..

lemma wf_append {env : Env} {a b : List Event} (h : WellFormedFrom env (a ++ b)) :
    WellFormedFrom (envAfter env a) b := by
  induction a generalizing env with
  | nil => simpa [envAfter] using h
  | cons e rest ih =>
    cases e <;> simp only [List.cons_append, WellFormedFrom, Env.reset] at h <;>
      simp only [envAfter, List.foldl_cons, stepEnv] <;>
      first | exact ih h | exact ih h.2

/-! ## Proof-internal per-token trace (scaffolding, not a model)

`TokenStateOk` is stated over `TokenEvents.tokenEvents`, which keeps a document's
`%TAG` handles pending until its `---`.  The environment bookkeeping below needs a
trace that is compositional token by token, so it uses a PRIVATE per-token twin
(`perTokenEvents`/`perTokenTrace`): a document begins at its first directive (or at
a `---` not preceded by directives), a `%TAG` declares its handle on the spot.  The
two traces are EQUAL on every `TokenGrammar` stream (`perTokenTrace_eq_tokenEvents`,
via spec [209]'s `---` after a non-empty directive run), which is the one bridge
`perTokenOk_of_tokenStateOk` from the public premise to this scaffolding; nothing
outside this file sees it (EVENTSOF-CONCEPT §9, S5 slice 2; 7.7 `parse_iff_grammar`). -/

/-- Is the token before `p` a directive?  (Proof-internal, with `perTokenEvents`.) -/
def prevDirAt (ts : Toks) : Nat → Bool
  | 0 => false
  | k + 1 => isDirective (tok ts k)

/-- Events denoted by token `p` (see the section header; proof-internal). -/
def perTokenEvents (ts : Toks) (p : Nat) : List Event :=
  let prevDir : Bool := prevDirAt ts p
  let begin : List Event := if prevDir then [] else [.beginDocument]
  match tok ts p with
  | some (.versionDirective ..) => begin
  | some (.tagDirective h _) => if isNamedHandle h then begin ++ [.declareTag h] else begin
  | some .documentStart => begin
  | some .documentEnd => [.endDocument]
  | some (.anchor n) => [.defineAnchor n]
  | some (.alias n) => [.useAlias n]
  | some (.tag h _) => if h = "" then [] else [.useTag h]
  | _ => []

/-- The whole per-token trace (proof-internal). -/
def perTokenTrace (ts : Toks) : List Event :=
  (List.range ts.size).flatMap (perTokenEvents ts)

/-- `TokenStateOk` read through the per-token trace (proof-internal). -/
def PerTokenOk (ts : Toks) : Prop :=
  SerializationWellFormed (perTokenTrace ts)

/-- Environment after the events of tokens `[0, i)`. -/
def envAt (ts : Toks) (i : Nat) : Env :=
  envAfter {} ((List.range i).flatMap (perTokenEvents ts))

lemma envAt_succ (ts : Toks) (i : Nat) :
    envAt ts (i + 1) = envAfter (envAt ts i) (perTokenEvents ts i) := by
  simp [envAt, List.range_succ, List.flatMap_append, envAfter_append]

lemma envAt_zero (ts : Toks) : envAt ts 0 = {} := rfl

lemma flatMap_range_split (f : Nat → List Event) {p n : Nat} (h : p < n) :
    ∃ rest, (List.range n).flatMap f = (List.range p).flatMap f ++ (f p ++ rest) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · obtain ⟨rest, hr⟩ := ih h'
      exact ⟨rest ++ f n, by rw [List.range_succ, List.flatMap_append, hr]; simp⟩
    · subst h'
      exact ⟨[], by rw [List.range_succ, List.flatMap_append]; simp⟩

lemma tok_some_lt {ts : Toks} {p : Nat} {t : YamlToken} (h : tok ts p = some t) :
    p < ts.size :=
  Nat.lt_of_not_le fun hc => by simp [tok, Array.getElem?_eq_none hc] at h

lemma tok_none_of_ge {ts : Toks} {p : Nat} (h : ts.size ≤ p) : tok ts p = none := by
  simp [tok, Array.getElem?_eq_none h]

lemma stateOk_at {ts : Toks} (h : PerTokenOk ts) {p : Nat} (hp : p < ts.size) :
    ∃ rest, WellFormedFrom (envAt ts p) (perTokenEvents ts p ++ rest) := by
  obtain ⟨rest, hr⟩ := flatMap_range_split (perTokenEvents ts) hp
  refine ⟨rest, ?_⟩
  unfold PerTokenOk perTokenTrace SerializationWellFormed at h
  rw [hr] at h
  exact wf_append h

lemma alias_ok {ts : Toks} (h : PerTokenOk ts) {p : Nat} {n : String}
    (ht : tok ts p = some (.alias n)) : n ∈ (envAt ts p).anchors := by
  obtain ⟨rest, hw⟩ := stateOk_at h (tok_some_lt ht)
  have he : perTokenEvents ts p = [.useAlias n] := by simp [perTokenEvents, prevDirAt, ht]
  rw [he] at hw
  exact hw.1

lemma tag_ok {ts : Toks} (h : PerTokenOk ts) {p : Nat} {hd s : String}
    (ht : tok ts p = some (.tag hd s)) : TagHandleAllowed (envAt ts p) hd := by
  by_cases h0 : hd = ""
  · exact Or.inl (Or.inl h0)
  obtain ⟨rest, hw⟩ := stateOk_at h (tok_some_lt ht)
  have he : perTokenEvents ts p = [.useTag hd] := by simp [perTokenEvents, prevDirAt, ht, h0]
  rw [he] at hw
  exact hw.1

/-- Content tokens other than `&` leave the environment unchanged. -/
lemma envAt_succ_content {ts : Toks} {p : Nat} (h : isDirective (tok ts p) = false)
    (h1 : tok ts p ≠ some .documentStart) (h2 : tok ts p ≠ some .documentEnd)
    (h3 : isAnchor (tok ts p) = false) : envAt ts (p + 1) = envAt ts p := by
  rw [envAt_succ]
  unfold perTokenEvents prevDirAt
  cases ho : tok ts p with
  | none => rfl
  | some t =>
    cases t <;> simp_all [isDirective, isAnchor, envAfter, stepEnv] <;> split <;> simp [stepEnv]

/-! ## The parser-state invariant -/

/-- Parser state at position `i`: tokens, position, and declared anchors /
    tag handles covering the environment at `i`. -/
structure Inv (ts : Toks) (ps : ParseState) (i : Nat) : Prop where
  tokens : ps.tokens = ts
  pos : ps.pos = i
  bound : i ≤ ts.size
  anchors : ∀ n, n ∈ (envAt ts i).anchors → n ∈ ps.declaredAnchors
  tags : ∀ h, h ∈ (envAt ts i).tagHandles → ps.tagHandles.any (·.1 == h) = true

lemma get_val {ts : Toks} {k : Nat} (hk : k < ts.size) : some (ts[k]'hk).val = tok ts k := by
  simp [tok, Array.getElem?_eq_getElem hk]

lemma get_pos {ts : Toks} {k : Nat} (hk : k < ts.size) : (ts[k]'hk).pos = posAt ts k := by
  simp [posAt, Array.getElem?_eq_getElem hk]

lemma getBang_val {ts : Toks} {k : Nat} (hk : k < ts.size) : some ts[k]!.val = tok ts k := by
  rw [getElem!_pos ts k hk]; exact get_val hk

lemma getBang_pos {ts : Toks} {k : Nat} (hk : k < ts.size) : ts[k]!.pos = posAt ts k := by
  rw [getElem!_pos ts k hk]; exact get_pos hk

lemma peek_tok {ts : Toks} {ps : ParseState} (h : ps.tokens = ts) :
    ps.peek? = tok ts ps.pos := by
  unfold ParseState.peek?
  rw [h]
  by_cases hi : ps.pos < ts.size
  · simp [hi, get_val hi]
  · simp [hi, tok_none_of_ge (Nat.not_lt.1 hi)]

lemma peekNext_tok {ts : Toks} {ps : ParseState} (h : ps.tokens = ts) :
    ps.peekNext? = tok ts (ps.pos + 1) := by
  unfold ParseState.peekNext?
  rw [h]
  by_cases hi : ps.pos + 1 < ts.size
  · simp [hi, get_val hi]
  · simp [hi, tok_none_of_ge (Nat.not_lt.1 hi)]

lemma peekPos_getD {ts : Toks} {ps : ParseState} (h : ps.tokens = ts) :
    ps.peekPos?.getD { offset := 0, line := 0, col := 0 } = posAt ts ps.pos := by
  unfold ParseState.peekPos?
  rw [h]
  by_cases hi : ps.pos < ts.size
  · simp [hi, get_pos hi]
  · simp [hi, posAt, Array.getElem?_eq_none (Nat.not_lt.1 hi)]

lemma Inv.peek {ts ps i} (h : Inv ts ps i) : ps.peek? = tok ts i := by
  rw [peek_tok h.tokens, h.pos]

lemma Inv.advance {ts ps i} (h : Inv ts ps i) (hi : i < ts.size)
    (he : envAt ts (i + 1) = envAt ts i) : Inv ts ps.advance (i + 1) where
  tokens := h.tokens
  pos := by simp [ParseState.advance, h.pos]
  bound := hi
  anchors := by rw [he]; exact h.anchors
  tags := by rw [he]; exact h.tags

lemma Inv.same {ts ps i} (h : Inv ts ps i) {ps' : ParseState} (ht : ps'.tokens = ps.tokens)
    (hp : ps'.pos = ps.pos) (ha : ps'.declaredAnchors = ps.declaredAnchors)
    (hg : ps'.tagHandles = ps.tagHandles) : Inv ts ps' i where
  tokens := ht.trans h.tokens
  pos := hp.trans h.pos
  bound := h.bound
  anchors := by rw [ha]; exact h.anchors
  tags := by rw [hg]; exact h.tags

lemma envAt_succ_anchor {ts : Toks} {p : Nat} {n : String} (h : tok ts p = some (.anchor n)) :
    envAt ts (p + 1) = { envAt ts p with anchors := n :: (envAt ts p).anchors } := by
  rw [envAt_succ]; simp [perTokenEvents, prevDirAt, h, envAfter, stepEnv]

lemma Inv.declare {ts ps i} (h : Inv ts ps i) {ps' : ParseState} {j : Nat} (n : String)
    (ht : ps'.tokens = ts) (hp : ps'.pos = j) (hb : j ≤ ts.size)
    (ha : ps'.declaredAnchors = ps.declaredAnchors.push n) (hg : ps'.tagHandles = ps.tagHandles)
    (he : envAt ts j = { envAt ts i with anchors := n :: (envAt ts i).anchors }) :
    Inv ts ps' j where
  tokens := ht
  pos := hp
  bound := hb
  anchors := by
    intro m hm
    rw [he] at hm
    rw [ha, Array.mem_push]
    rcases List.mem_cons.1 hm with hm | hm
    · exact Or.inr hm
    · exact Or.inl (h.anchors m hm)
  tags := by rw [he, hg]; exact h.tags

/-- The `%TAG` guard inside `parseNodeProperties` passes under `TokenStateOk`. -/
lemma tag_guard {env : Env} {hd : String} {arr : Array (String × String)}
    (hall : TagHandleAllowed env hd)
    (hcov : ∀ h, h ∈ env.tagHandles → arr.any (·.1 == h) = true) :
    (hd != "" && hd != "!" && hd != "!!") = true → arr.any (fun x => x.fst == hd) = true := by
  intro hc
  rcases hall with hb | hm
  · exfalso
    rcases hb with rfl | rfl | rfl <;> simp at hc
  · exact hcov hd hm

set_option maxHeartbeats 3200000 in
/-- `parseNodeProperties` on a `props` span: succeeds, no duplicate anchor, lands at `j`. -/
lemma props_ok {ts : Toks} {ps : ParseState} {i j : Nat} (hS : PerTokenOk ts)
    (hp : TG ts .props i j) (hinv : Inv ts ps i) :
    ∃ props ps', parseNodeProperties ps = .ok (props, ps') ∧ Inv ts ps' j ∧
      props.hadDuplicateAnchor = false := by
  have hp2 : ps.advance.pos = i + 1 := by simp [ParseState.advance, hinv.pos]
  have hp3 : ps.advance.advance.pos = i + 2 := by simp [ParseState.advance, hinv.pos]
  have hpk2 : ps.advance.peek? = tok ts (i + 1) := by
    rw [peek_tok (ps := ps.advance) hinv.tokens, hp2]
  cases hp with
  | props_none hn =>
    refine ⟨{}, ps, parseNodeProperties_skip ps ?_, hinv, rfl⟩
    rw [hinv.peek]
    cases ho : tok ts i with
    | none => trivial
    | some t => cases t <;> simp_all [isProp]
  | props_anchor hn hnext =>
    rename_i n
    unfold parseNodeProperties
    dsimp only []
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',
               Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
               show List.range' 0 2 1 = [0, 1] from by decide,
               List.forIn_cons, List.forIn_nil, bind, Except.bind, pure, Except.pure]
    rw [hinv.peek, hn]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hpk2]
    cases ho : tok ts (i + 1) with
    | none =>
      simp only []
      refine ⟨_, _, rfl, ?_, rfl⟩
      exact hinv.declare n hinv.tokens (by simp [hp2]) (tok_some_lt hn) rfl rfl (envAt_succ_anchor hn)
    | some t =>
      cases t <;> simp [isProp, ho] at hnext <;> simp only [] <;>
        exact ⟨_, _, rfl, hinv.declare n hinv.tokens (by simp [hp2]) (tok_some_lt hn) rfl rfl (envAt_succ_anchor hn), rfl⟩
  | props_tag hn hnext =>
    rename_i hd sfx
    have hg := tag_guard (tag_ok hS hn) hinv.tags
    unfold parseNodeProperties
    dsimp only []
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',
               Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
               show List.range' 0 2 1 = [0, 1] from by decide,
               List.forIn_cons, List.forIn_nil, bind, Except.bind, pure, Except.pure]
    rw [hinv.peek, hn]
    have hinv' : Inv ts ps.advance (i + 1) :=
      hinv.advance (tok_some_lt hn) (envAt_succ_content (by simp [hn, isDirective])
        (by simp [hn]) (by simp [hn]) (by simp [hn, isAnchor]))
    by_cases hc : (hd != "" && hd != "!" && hd != "!!") = true
    · simp only [hc, hg hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpk2]
      cases ho : tok ts (i + 1) with
      | none => simp only []; exact ⟨_, _, rfl, hinv', rfl⟩
      | some t =>
        cases t <;> simp [isProp, ho] at hnext <;> simp only [] <;> exact ⟨_, _, rfl, hinv', rfl⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, hpk2]
      cases ho : tok ts (i + 1) with
      | none => simp only []; exact ⟨_, _, rfl, hinv', rfl⟩
      | some t =>
        cases t <;> simp [isProp, ho] at hnext <;> simp only [] <;> exact ⟨_, _, rfl, hinv', rfl⟩
  | props_anchorTag hn ht =>
    rename_i n hd sfx
    have hall : TagHandleAllowed (envAt ts i) hd := by
      have := tag_ok hS ht
      rwa [envAt_succ_anchor hn] at this
    have hg := tag_guard hall hinv.tags
    have hinv2 : Inv ts (ps.advance.advance.declareAnchor n) (i + 2) :=
      hinv.declare n hinv.tokens (by simp [hp3]) (tok_some_lt ht) rfl rfl
        (by rw [envAt_succ_content (p := i + 1) (by simp [ht, isDirective]) (by simp [ht])
              (by simp [ht]) (by simp [ht, isAnchor]), envAt_succ_anchor hn])
    unfold parseNodeProperties
    dsimp only []
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',
               Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
               show List.range' 0 2 1 = [0, 1] from by decide,
               List.forIn_cons, List.forIn_nil, bind, Except.bind, pure, Except.pure]
    rw [hinv.peek, hn]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hpk2, ht]
    by_cases hc : (hd != "" && hd != "!" && hd != "!!") = true
    · simp only [hc, show ps.advance.tagHandles = ps.tagHandles from rfl, hg hc, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, _, rfl, hinv2, rfl⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, _, rfl, hinv2, rfl⟩
  | props_tagAnchor ht hn =>
    rename_i hd sfx n
    have hg := tag_guard (tag_ok hS ht) hinv.tags
    have he1 : envAt ts (i + 1) = envAt ts i :=
      envAt_succ_content (by simp [ht, isDirective]) (by simp [ht]) (by simp [ht]) (by simp [ht, isAnchor])
    have hinv2 : Inv ts (ps.advance.advance.declareAnchor n) (i + 2) :=
      hinv.declare n hinv.tokens (by simp [hp3]) (tok_some_lt hn) rfl rfl
        (by rw [envAt_succ_anchor hn, he1])
    unfold parseNodeProperties
    dsimp only []
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',
               Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
               show List.range' 0 2 1 = [0, 1] from by decide,
               List.forIn_cons, List.forIn_nil, bind, Except.bind, pure, Except.pure]
    rw [hinv.peek, ht]
    by_cases hc : (hd != "" && hd != "!" && hd != "!!") = true
    · simp only [hc, hg hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpk2, hn,
        Option.isSome_none]
      exact ⟨_, _, rfl, hinv2, rfl⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, hpk2, hn, Option.isSome_none]
      exact ⟨_, _, rfl, hinv2, rfl⟩

/-! ## Span facts about derivations -/

lemma tg_le {ts : Toks} {s : Sym} {i j : Nat} (h : TG ts s i j) : i ≤ j := by
  induction h <;> try omega
  all_goals first
    | (obtain hd := ‹DocStart _ _ _ _›; unfold DocStart at hd
       rcases hd with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> omega)
    | (obtain hd := ‹FlowSep _ _ _ _›; unfold FlowSep at hd
       rcases hd with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> omega)
    | (rcases ‹(_ ∧ _) ∨ (_ ∧ _)› with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega)

/-- Tokens that start a non-empty node. -/
def startsNode : Option YamlToken → Bool
  | some (.alias _) | some (.anchor _) | some (.tag ..) | some (.scalar ..)
  | some .blockSequenceStart | some .blockMappingStart | some .blockEntry
  | some .flowSequenceStart | some .flowMappingStart => true
  | _ => false

lemma content_empty_of {ts : Toks} {se : Bool} {i m : Nat} (hc : TG ts (.content se) i m)
    (hs : startsNode (tok ts i) = false) : m = i := by
  cases hc with
  | content_scalar h' => simp [h', startsNode] at hs
  | content_blockSeq hb => cases hb with | blockSeq h' _ _ => simp [h', startsNode] at hs
  | content_blockMap hb => cases hb with | blockMap h' _ _ => simp [h', startsNode] at hs
  | content_seqEntryEmpty _ => rfl
  | content_implicitSeq h' _ => simp [h', startsNode] at hs
  | content_flowSeq hb => cases hb with | flowSeq h' _ _ => simp [h', startsNode] at hs
  | content_flowMap hb => cases hb with | flowMap h' _ _ => simp [h', startsNode] at hs
  | content_empty _ => rfl

/-- A node derivation at a token that cannot start a node is the empty node. -/
lemma node_empty_of {ts : Toks} {i m : Nat} (h : TG ts .node i m)
    (hs : startsNode (tok ts i) = false) : m = i := by
  cases h with
  | node_alias ha => simp [ha, startsNode] at hs
  | node hp hl hc =>
    rename_i m'
    have hm' : m' = i := by
      cases hp with
      | props_none _ => rfl
      | props_anchor ha _ => simp [ha, startsNode] at hs
      | props_tag ha _ => simp [ha, startsNode] at hs
      | props_anchorTag ha _ => simp [ha, startsNode] at hs
      | props_tagAnchor ha _ => simp [ha, startsNode] at hs
    subst hm'
    exact content_empty_of hc hs

lemma startsNode_false_of_emptyFollower {o : Option YamlToken} (h : emptyFollower o = true) :
    startsNode o = false := by
  cases o with
  | none => rfl
  | some t => cases t <;> simp_all [emptyFollower, startsNode]

/-- `D ts n`: the token before `n` is not a directive. -/
def NotDirBefore (ts : Toks) (n : Nat) : Prop := isDirective (tok ts (n - 1)) = false

lemma chain {ts : Toks} {a b c : Nat} (hab : a < b → NotDirBefore ts b)
    (hbc : b < c → NotDirBefore ts c) (hle : b ≤ c) (h : a < c) : NotDirBefore ts c := by
  rcases Nat.lt_or_eq_of_le hle with h' | h'
  · exact hbc h'
  · subst h'; exact hab h

lemma notDirBefore_of {ts : Toks} {k : Nat} {t : YamlToken} (h : tok ts k = some t)
    (ht : isDirective (some t) = false) : NotDirBefore ts (k + 1) := by
  unfold NotDirBefore; simp [h, ht]

/-- The last token of a non-empty node-level span is never a directive. -/
lemma last_not_directive {ts : Toks} {s : Sym} {i j : Nat} (h : TG ts s i j) :
    (match s with
      | .stream _ | .document | .directives => True
      | _ => i < j → NotDirBefore ts j) := by
  induction h with
  | stream_end _ => trivial
  | stream_docEnd _ _ => trivial
  | stream_doc _ _ _ _ _ _ _ _ => trivial
  | stream_docTerminated _ _ _ _ _ _ _ => trivial
  | document _ _ _ => trivial
  | directives_nil _ => trivial
  | directives_cons _ _ => trivial
  | node_alias ha => intro _; exact notDirBefore_of ha rfl
  | node hp _ hc ihp ihc => exact fun hlt => chain ihp ihc (tg_le hc) hlt
  | props_none _ => intro h; omega
  | props_anchor ha _ => intro _; exact notDirBefore_of ha rfl
  | props_tag ha _ => intro _; exact notDirBefore_of ha rfl
  | props_anchorTag _ ht => intro _; exact notDirBefore_of ht rfl
  | props_tagAnchor _ ha => intro _; exact notDirBefore_of ha rfl
  | content_scalar hs => intro _; exact notDirBefore_of hs rfl
  | content_blockSeq _ ih => exact ih
  | content_blockMap _ ih => exact ih
  | content_seqEntryEmpty _ => intro h; omega
  | content_implicitSeq _ _ ih => exact ih
  | content_flowSeq _ ih => exact ih
  | content_flowMap _ ih => exact ih
  | content_empty _ => intro h; omega
  | blockSeq _ _ he => intro _; exact notDirBefore_of he rfl
  | seqEntries_nil _ => intro h; omega
  | seqEntries_cons hb hn hr ihn ihr =>
    exact fun hlt => chain (fun h1 => chain (fun _ => notDirBefore_of hb rfl) ihn (tg_le hn) h1)
      ihr (tg_le hr) hlt
  | blockMap _ _ he => intro _; exact notDirBefore_of he rfl
  | mapEntries_nil _ _ => intro h; omega
  | mapEntries_key hk hke hr ihk ihr => exact fun hlt => chain ihk ihr (tg_le hr) hlt
  | mapEntries_value hv hn hr ihn ihr =>
    exact fun hlt => chain (fun h1 => chain (fun _ => notDirBefore_of hv rfl) ihn (tg_le hn) h1)
      ihr (tg_le hr) hlt
  | keyEntry hk hn hv ihn ihv =>
    exact fun hlt => chain (fun h1 => chain (fun _ => notDirBefore_of hk rfl) ihn (tg_le hn) h1)
      ihv (tg_le hv) hlt
  | entryValue_value hv _ _ hn ih =>
    exact fun hlt => chain (fun _ => notDirBefore_of hv rfl) ih (tg_le hn) hlt
  | entryValue_retro _ hv hn ih =>
    exact fun hlt => chain (fun _ => notDirBefore_of hv rfl) ih (tg_le hn) hlt
  | entryValue_none _ _ => intro h; omega
  | flowSeq _ _ he => intro _; exact notDirBefore_of he rfl
  | flowSeqItems_end _ => intro h; omega
  | flowSeqItems_trailing hf _ => intro _; exact notDirBefore_of hf rfl
  | flowSeqItems_pair _ hsep _ hp hr ihp ihr =>
    intro hlt
    refine chain (fun h1 => chain ?_ ihp (tg_le hp) h1) ihr (tg_le hr) hlt
    intro hiq
    rcases hsep with ⟨_, hq⟩ | ⟨_, hf, hq⟩
    · omega
    · subst hq; exact notDirBefore_of hf rfl
  | flowSeqItems_node _ hsep _ _ hn hr ihn ihr =>
    intro hlt
    refine chain (fun h1 => chain ?_ ihn (tg_le hn) h1) ihr (tg_le hr) hlt
    intro hiq
    rcases hsep with ⟨_, hq⟩ | ⟨_, hf, hq⟩
    · omega
    · subst hq; exact notDirBefore_of hf rfl
  | singlePair_value _ _ hv hn2 _ ihv =>
    exact fun hlt => chain (fun _ => notDirBefore_of hv rfl) ihv (tg_le hn2) hlt
  | singlePair_noValue hk hn _ ihn =>
    exact fun hlt => chain (fun _ => notDirBefore_of hk rfl) ihn (tg_le hn) hlt
  | flowMap _ _ he => intro _; exact notDirBefore_of he rfl
  | flowMapEntries_end _ => intro h; omega
  | flowMapEntries_trailing hf _ => intro _; exact notDirBefore_of hf rfl
  | flowMapEntries_explicit _ _ hk hn hv hr ihn ihv ihr =>
    exact fun hlt => chain (fun h1 => chain (fun h2 => chain (fun _ => notDirBefore_of hk rfl)
      ihn (tg_le hn) h2) ihv (tg_le hv) h1) ihr (tg_le hr) hlt
  | flowMapEntries_implicit _ hsep _ _ hn hv hr ihn ihv ihr =>
    intro hlt
    refine chain (fun h1 => chain (fun h2 => chain ?_ ihn (tg_le hn) h2) ihv (tg_le hv) h1) ihr
      (tg_le hr) hlt
    intro hiq
    rcases hsep with ⟨_, hq⟩ | ⟨_, hf, hq⟩
    · omega
    · subst hq; exact notDirBefore_of hf rfl
  | flowMapValue_value _ hv hn ih =>
    exact fun hlt => chain (fun _ => notDirBefore_of hv rfl) ih (tg_le hn) hlt
  | flowMapValue_none hr' _ =>
    intro hlt
    rcases hr' with ⟨hk, hq⟩ | ⟨_, hq⟩
    · subst hq; exact notDirBefore_of hk rfl
    · omega

/-! ## Fuel budgets and the per-nonterminal acceptance statement -/

/-- Fuel each nonterminal needs for a span of `L` tokens (slack for the parser's
    one-decrement-per-call structure). -/
def fuelReq : Sym → Nat → Nat
  | .node, L => 4 * L + 1
  | .content _, L => 4 * L
  | .blockSeq, L => 4 * L
  | .blockMap, L => 4 * L
  | .flowSeq, L => 4 * L
  | .flowMap, L => 4 * L
  | .seqEntries, L => 4 * L - 1
  | .mapEntries, L => 4 * L + 3
  | .keyEntry, L => 4 * L + 2
  | .entryValue .., L => 4 * L + 2
  | .singlePair, L => 4 * L + 2
  | .flowMapValue, L => 4 * L + 2
  | .flowSeqItems first, L => 4 * L + 3 + (if first then 1 else 0)
  | .flowMapEntries first, L => 4 * L + 3 + (if first then 1 else 0)
  | _, _ => 0

/-- What the parser function for each nonterminal does on a derived span. -/
def ParseOk (ts : Toks) : Sym → Nat → Nat → Prop
  | .node, i, j => ∀ ps fuel, Inv ts ps i → fuelReq .node (j - i) ≤ fuel →
      ∃ v ps', parseNode ps fuel = .ok (v, ps') ∧ Inv ts ps' j
  | .content se, i, j => ∀ ps fuel props, Inv ts ps i → fuelReq (.content se) (j - i) ≤ fuel →
      ∃ v ps', parseNodeContent ps fuel props se = .ok (v, ps') ∧ Inv ts ps' j
  | .blockSeq, i, j => ∀ ps fuel, Inv ts ps i → fuelReq .blockSeq (j - i) ≤ fuel →
      ∃ v ps', parseBlockSequence ps fuel = .ok (v, ps') ∧ Inv ts ps' j
  | .seqEntries, i, j => ∀ ps fuel items, Inv ts ps i → fuelReq .seqEntries (j - i) ≤ fuel →
      (∃ items' ps', parseBlockSequenceLoop ps fuel items = .ok (items', ps') ∧ Inv ts ps' j) ∧
      (∃ items' ps', parseImplicitBlockSequenceLoop ps fuel items = .ok (items', ps') ∧
        Inv ts ps' j)
  | .blockMap, i, j => ∀ ps fuel, Inv ts ps i → fuelReq .blockMap (j - i) ≤ fuel →
      ∃ v ps', parseBlockMapping ps fuel = .ok (v, ps') ∧ Inv ts ps' j
  | .mapEntries, i, j => ∀ ps fuel pairs, Inv ts ps i → fuelReq .mapEntries (j - i) ≤ fuel →
      ∃ pairs' ps', parseBlockMappingLoop ps fuel pairs = .ok (pairs', ps') ∧ Inv ts ps' j
  | .keyEntry, i, j => ∀ ps fuel idx, Inv ts ps i → fuelReq .keyEntry (j - i) ≤ fuel →
      ∃ k v ps', handleBlockMappingKeyEntry ps fuel idx = .ok (k, v, ps') ∧ Inv ts ps' j
  | .entryValue khc kl kc, i, j => ∀ ps fuel, Inv ts ps i →
      fuelReq (.entryValue khc kl kc) (j - i) ≤ fuel →
      ∃ v ps', parseBlockMappingEntryValue ps fuel khc kl kc = .ok (v, ps') ∧ Inv ts ps' j
  | .flowSeq, i, j => ∀ ps fuel, Inv ts ps i → fuelReq .flowSeq (j - i) ≤ fuel →
      ∃ v ps', parseFlowSequence ps fuel = .ok (v, ps') ∧ Inv ts ps' j
  | .flowSeqItems first, i, j => ∀ ps fuel items, Inv ts ps i →
      fuelReq (.flowSeqItems first) (j - i) ≤ fuel → (first = true ↔ items.size = 0) →
      ∃ items' ps', parseFlowSequenceLoop ps fuel items = .ok (items', ps') ∧ Inv ts ps' j
  | .singlePair, i, j => ∀ ps fuel, Inv ts ps i → fuelReq .singlePair (j - i) ≤ fuel →
      ∃ v ps', parseSinglePairMapping ps fuel = .ok (v, ps') ∧ Inv ts ps' j
  | .flowMap, i, j => ∀ ps fuel, Inv ts ps i → fuelReq .flowMap (j - i) ≤ fuel →
      ∃ v ps', parseFlowMapping ps fuel = .ok (v, ps') ∧ Inv ts ps' j
  | .flowMapEntries first, i, j => ∀ ps fuel pairs, Inv ts ps i →
      fuelReq (.flowMapEntries first) (j - i) ≤ fuel → (first = true ↔ pairs.size = 0) →
      ∃ pairs' ps', parseFlowMappingLoop ps fuel pairs = .ok (pairs', ps') ∧ Inv ts ps' j
  | .flowMapValue, i, j => ∀ ps fuel path kc, Inv ts ps i →
      fuelReq .flowMapValue (j - i) ≤ fuel →
      ∃ v ps', parseFlowMappingValue ps fuel path kc = .ok (v, ps') ∧ Inv ts ps' j
  | _, _, _ => True

/-- Tokens whose event leaves the environment unchanged. -/
def contentTok : YamlToken → Bool
  | .versionDirective .. | .tagDirective .. | .documentStart | .documentEnd | .anchor _ => false
  | _ => true

lemma envAt_succ_content' {ts : Toks} {p : Nat} {t : YamlToken} (h : tok ts p = some t)
    (hc : contentTok t = true) : envAt ts (p + 1) = envAt ts p := by
  rw [envAt_succ]
  unfold perTokenEvents prevDirAt
  rw [h]
  cases t <;> simp_all [contentTok, envAfter, stepEnv] <;> split <;> simp [stepEnv]

lemma Inv.step {ts ps i} (h : Inv ts ps i) {t : YamlToken} (ht : tok ts i = some t)
    (hc : contentTok t = true) : Inv ts ps.advance (i + 1) :=
  h.advance (tok_some_lt ht) (envAt_succ_content' ht hc)

lemma Inv.advance_pos {ts ps i} (h : Inv ts ps i) : ps.advance.pos = i + 1 := by
  simp [ParseState.advance, h.pos]

lemma Inv.peek_advance {ts ps i} (h : Inv ts ps i) : ps.advance.peek? = tok ts (i + 1) := by
  rw [peek_tok (ps := ps.advance) h.tokens, h.advance_pos]

lemma applyNodeFinalization_declared (val : YamlValue) (ps : ParseState) (props : NodeProperties)
    (p : YamlPos) : (applyNodeFinalization val ps props p).2.declaredAnchors = ps.declaredAnchors := by
  simp only [applyNodeFinalization]
  split <;> (try split) <;> simp_all [ParseState.addAnchor]

lemma applyNodeFinalization_tagHandles (val : YamlValue) (ps : ParseState)
    (props : NodeProperties) (p : YamlPos) :
    (applyNodeFinalization val ps props p).2.tagHandles = ps.tagHandles := by
  simp only [applyNodeFinalization]
  split <;> (try split) <;> simp_all [ParseState.addAnchor]

lemma Inv.finalize {ts ps i} (h : Inv ts ps i) (val : YamlValue) (props : NodeProperties)
    (p : YamlPos) : Inv ts (applyNodeFinalization val ps props p).2 i :=
  h.same (applyNodeFinalization_tokens ..) (applyNodeFinalization_pos ..)
    (applyNodeFinalization_declared ..) (applyNodeFinalization_tagHandles ..)

/-- `parseNode`'s inline `isSeqEntry` is `isSeqEntryAt`. -/
lemma isSeqEntry_eq {ts ps i} (h : Inv ts ps i) :
    (if i > 0 then
        match ps.tokens[i - 1]!.val with
        | .blockEntry => true
        | _ => false
      else false) = isSeqEntryAt ts i := by
  rw [h.tokens]
  cases i with
  | zero => rfl
  | succ k =>
    have hk : k < ts.size := by have := h.bound; omega
    simp only [Nat.zero_lt_succ, ↓reduceIte, Nat.add_sub_cancel, isSeqEntryAt]
    rw [← getBang_val hk]
    cases ts[k]!.val <;> rfl

lemma content_not_alias {ts : Toks} {se : Bool} {i j : Nat} (hc : TG ts (.content se) i j)
    {n : String} (ha : tok ts i = some (.alias n)) : False := by
  cases hc with
  | content_scalar h' => simp [ha] at h'
  | content_blockSeq hb => cases hb with | blockSeq h' _ _ => simp [ha] at h'
  | content_blockMap hb => cases hb with | blockMap h' _ _ => simp [ha] at h'
  | content_seqEntryEmpty h' => simp [ha] at h'
  | content_implicitSeq h' _ => simp [ha] at h'
  | content_flowSeq hb => cases hb with | flowSeq h' _ _ => simp [ha] at h'
  | content_flowMap hb => cases hb with | flowMap h' _ _ => simp [ha] at h'
  | content_empty h' => simp [ha, emptyFollower] at h'

/-- `validateNodeProps` passes on a derived node (no duplicate anchor, line check). -/
lemma validate_ok {ts : Toks} {i m : Nat} {ps : ParseState} {props : NodeProperties}
    (hinv : Inv ts ps m) (hl : PropsLineOk ts i m) (hdup : props.hadDuplicateAnchor = false) :
    validateNodeProps ps i props = .ok () := by
  unfold validateNodeProps
  simp only [bind, Except.bind, pure, Except.pure, hdup, Bool.false_eq_true, ↓reduceIte]
  rw [hinv.peek, hinv.pos]
  have key : ∀ hb : isBlockStart (tok ts m) = true,
      (if i < m then
          if (ps.tokens[m - 1]!.pos.line ==
              (ps.peekPos?.getD { offset := 0, line := 0, col := 0 }).line) = true then
            (throw (.trailingContent (ps.peekPos?.getD { offset := 0, line := 0, col := 0 }).line
              (ps.peekPos?.getD { offset := 0, line := 0, col := 0 }).col) : Except ScanError Unit)
          else pure ()
        else pure ()) = .ok () := by
    intro hb
    by_cases hlt : i < m
    · have hm : m < ts.size := by
        cases ho : tok ts m with
        | none => simp [ho, isBlockStart] at hb
        | some t => exact tok_some_lt ho
      have hm1 : m - 1 < ts.size := by omega
      have hne := hl hlt hb
      rw [hinv.tokens, getBang_pos hm1, peekPos_getD hinv.tokens, hinv.pos]
      simp only [hlt, ↓reduceIte]
      have : ((posAt ts (m - 1)).line == (posAt ts m).line) = false := by
        simpa [lineAt] using hne
      simp [this, pure, Except.pure]
    · simp [hlt, pure, Except.pure]
  split
  · exact key (by simp_all [isBlockStart])
  · exact key (by simp_all [isBlockStart])
  · rfl

lemma seqEntries_lt {ts : Toks} {i j : Nat} (h : TG ts .seqEntries i j)
    (hb : tok ts i = some .blockEntry) : i < j := by
  cases h with
  | seqEntries_nil hne => exact absurd hb hne
  | seqEntries_cons _ hn hr => have := tg_le hn; have := tg_le hr; omega

/-- After `-`, a node that the loop would shortcut is empty. -/
lemma node_after_entry_empty {ts : Toks} {i m : Nat} (hb : tok ts i = some .blockEntry)
    (hn : TG ts .node (i + 1) m)
    (hne : startsNode (tok ts (i + 1)) = false ∨ tok ts (i + 1) = some .blockEntry) :
    m = i + 1 := by
  rcases hne with hne | hne
  · exact node_empty_of hn hne
  · cases hn with
    | node_alias ha => simp [hne] at ha
    | node hp hl hc =>
      rename_i m'
      have hm' : m' = i + 1 := by
        cases hp with
        | props_none _ => rfl
        | props_anchor ha _ => simp [hne] at ha
        | props_tag ha _ => simp [hne] at ha
        | props_anchorTag ha _ => simp [hne] at ha
        | props_tagAnchor ha _ => simp [hne] at ha
      subst hm'
      have hse : isSeqEntryAt ts (i + 1) = true := by simp [isSeqEntryAt, hb]
      rw [hse] at hc
      cases hc with
      | content_scalar h' => simp [hne] at h'
      | content_blockSeq hb' => cases hb' with | blockSeq h' _ _ => simp [hne] at h'
      | content_blockMap hb' => cases hb' with | blockMap h' _ _ => simp [hne] at h'
      | content_seqEntryEmpty _ => rfl
      | content_flowSeq hb' => cases hb' with | flowSeq h' _ _ => simp [hne] at h'
      | content_flowMap hb' => cases hb' with | flowMap h' _ _ => simp [hne] at h'
      | content_empty h' => simp [hne, emptyFollower] at h'

/-- The parser's inline key path segment. -/
def keyName (v : YamlValue) (idx : Nat) : String :=
  match v with | .scalar s => s.content | _ => s!"{idx}"

lemma keyEntry_lt {ts : Toks} {i m : Nat} (h : TG ts .keyEntry i m) : i < m := by
  cases h with
  | keyEntry _ hn hv => have := tg_le hn; have := tg_le hv; omega

lemma tryConsume_hit {ts ps i} (hinv : Inv ts ps i) {t : YamlToken} (h : tok ts i = some t)
    (hrefl : (t == t) = true) : ps.tryConsume t = (true, ps.advance) := by
  unfold ParseState.tryConsume
  rw [hinv.peek, h]
  simp [hrefl]

lemma tryConsume_value_miss {ts ps i} (hinv : Inv ts ps i) (h : tok ts i ≠ some .value) :
    ps.tryConsume .value = (false, ps) := by
  unfold ParseState.tryConsume
  rw [hinv.peek]
  cases ho : tok ts i with
  | none => rfl
  | some t => cases t <;> first | rfl | exact absurd ho h

lemma tryConsume_key_miss {ts ps i} (hinv : Inv ts ps i) (h : tok ts i ≠ some .key) :
    ps.tryConsume .key = (false, ps) := by
  unfold ParseState.tryConsume
  rw [hinv.peek]
  cases ho : tok ts i with
  | none => rfl
  | some t => cases t <;> first | rfl | exact absurd ho h

lemma tryConsume_docEnd_miss {ts ps i} (hinv : Inv ts ps i) (h : tok ts i ≠ some .documentEnd) :
    ps.tryConsume .documentEnd = (false, ps) := by
  unfold ParseState.tryConsume
  rw [hinv.peek]
  cases ho : tok ts i with
  | none => rfl
  | some t => cases t <;> first | rfl | exact absurd ho h

lemma tryConsume_docStart_miss {ts ps i} (hinv : Inv ts ps i)
    (h : tok ts i ≠ some .documentStart) : ps.tryConsume .documentStart = (false, ps) := by
  unfold ParseState.tryConsume
  rw [hinv.peek]
  cases ho : tok ts i with
  | none => rfl
  | some t => cases t <;> first | rfl | exact absurd ho h

/-- The property-indentation loop of `parseBlockMappingEntryValue` passes under `ValuePropsOk`. -/
lemma valueProps_loop_ok {ts ps m kc} (hinv : Inv ts ps (m + 1)) (hvp : ValuePropsOk ts m kc)
    (hm : m < ts.size) :
    (forIn [ps.pos : min (ps.pos + 2) ps.tokens.size] () (fun k (_ : Unit) =>
        match ps.tokens[k]!.val with
        | .anchor _ | .tag _ _ =>
          let propPos := ps.tokens[k]!.pos
          if propPos.line != ps.tokens[ps.pos - 1]!.pos.line && propPos.col <= kc then
            (throw (.trailingContent propPos.line propPos.col) : Except ScanError (ForInStep Unit))
          else pure (ForInStep.yield ())
        | _ => pure (ForInStep.done ())) : Except ScanError Unit) = .ok () := by
  have hp := hinv.pos
  have htk := hinv.tokens
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.div_one, Nat.add_sub_cancel]
  have cond : ∀ k, ValuePropOk ts m kc k →
      ((posAt ts k).line != (posAt ts m).line && decide ((posAt ts k).col ≤ kc)) = false := by
    intro k hok
    unfold ValuePropOk lineAt colAt at hok
    rcases hok with h | h
    · simp [h]
    · simp [Nat.not_le.2 h]
  have hn : min (ps.pos + 2) ps.tokens.size - ps.pos = 0 ∨
      min (ps.pos + 2) ps.tokens.size - ps.pos = 1 ∨
      min (ps.pos + 2) ps.tokens.size - ps.pos = 2 := by omega
  rcases hn with hn | hn | hn <;> rw [hn]
  · rfl
  · have h1 : m + 1 < ts.size := by rw [htk, hp] at hn; omega
    simp only [List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil, hp, htk,
      Nat.add_sub_cancel]
    rw [getBang_pos h1, getBang_pos hm]
    cases ho : ts[m + 1]!.val
    all_goals first
      | (have hpr : isProp (tok ts (m + 1)) = true := by rw [← getBang_val h1, ho]; rfl
         simp only [cond _ (hvp.1 hpr), Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
           bind, Except.bind])
      | simp only [pure, Except.pure, bind, Except.bind]
  · have h1 : m + 1 < ts.size := by rw [htk, hp] at hn; omega
    have h2 : m + 2 < ts.size := by rw [htk, hp] at hn; omega
    simp only [List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil, hp, htk,
      Nat.add_sub_cancel]
    rw [getBang_pos h1, getBang_pos h2, getBang_pos hm]
    cases ho : ts[m + 1]!.val
    all_goals first
      | (have hpr : isProp (tok ts (m + 1)) = true := by rw [← getBang_val h1, ho]; rfl
         simp only [cond _ (hvp.1 hpr), Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
           bind, Except.bind]
         cases ho2 : ts[m + 2]!.val
         all_goals first
           | (have hpr2 : isProp (tok ts (m + 2)) = true := by rw [← getBang_val h2, ho2]; rfl
              simp only [cond _ (hvp.2 hpr hpr2), Bool.false_eq_true, ↓reduceIte, pure,
                Except.pure, bind, Except.bind])
           | simp only [pure, Except.pure, bind, Except.bind])
      | simp only [pure, Except.pure, bind, Except.bind]

set_option maxHeartbeats 2000000 in
lemma tg_parse {ts : Toks} (hS : PerTokenOk ts) {s : Sym} {i j : Nat} (h : TG ts s i j) :
    ParseOk ts s i j := by
  induction h with
  | stream_end _ => trivial
  | stream_docEnd _ _ => trivial
  | stream_doc _ _ _ _ _ _ _ _ => trivial
  | stream_docTerminated _ _ _ _ _ _ _ => trivial
  | document _ _ _ => trivial
  | directives_nil _ => trivial
  | directives_cons _ _ => trivial
  | props_none _ => trivial
  | props_anchor _ _ => trivial
  | props_tag _ _ => trivial
  | props_anchorTag _ _ => trivial
  | props_tagAnchor _ _ => trivial
  | node_alias ha =>
    intro ps fuel hinv hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    have hpk := hinv.peek
    rw [ha] at hpk
    have hdecl : ps.declaredIndex.contains _ = true :=
      (DeclaredIndex.contains_iff _ _).2 (hinv.anchors _ (alias_ok hS ha))
    have hinv' := hinv.step ha rfl
    unfold parseNode
    simp only [hpk, hdecl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind,
      pure, Except.pure]
    split
    · exact ⟨_, _, rfl, hinv'.same rfl rfl rfl rfl⟩
    · exact ⟨_, _, rfl, hinv'⟩
  | node hp hl hc _ ihc =>
    intro ps fuel hinv hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    obtain ⟨props, ps1, hprops, hinv1, hdup⟩ := props_ok hS hp hinv
    have hle := tg_le hp
    have hle2 := tg_le hc
    unfold parseNode
    simp only [bind, Except.bind, pure, Except.pure]
    rw [hinv.peek]
    split
    · exfalso
      rename_i n ha
      cases hp with
      | props_none _ => exact content_not_alias hc ha
      | props_anchor h' _ => simp [ha] at h'
      | props_tag h' _ => simp [ha] at h'
      | props_anchorTag h' _ => simp [ha] at h'
      | props_tagAnchor h' _ => simp [ha] at h'
    · rw [hprops]
      simp only []
      rw [hinv.pos, validate_ok hinv1 hl hdup]
      simp only []
      obtain ⟨v, ps2, hcont, hinv2⟩ := ihc ps1 f props hinv1 (by simp [fuelReq] at hf ⊢; omega)
      rw [← isSeqEntry_eq hinv] at hcont
      erw [hcont]
      exact ⟨_, _, rfl, hinv2.finalize _ _ _⟩
  | content_scalar hs =>
    intro ps fuel props hinv _
    unfold parseNodeContent
    rw [hinv.peek, hs]
    exact ⟨_, _, rfl, hinv.step hs rfl⟩
  | content_blockSeq hb ih =>
    intro ps fuel props hinv hf
    unfold parseNodeContent
    rw [hinv.peek]
    cases hb with
    | blockSeq hs _ _ =>
      rw [hs]
      exact ih ps fuel hinv (by simpa [fuelReq] using hf)
  | content_blockMap hb ih =>
    intro ps fuel props hinv hf
    unfold parseNodeContent
    rw [hinv.peek]
    cases hb with
    | blockMap hs _ _ =>
      rw [hs]
      exact ih ps fuel hinv (by simpa [fuelReq] using hf)
  | content_seqEntryEmpty hb =>
    intro ps fuel props hinv _
    unfold parseNodeContent
    rw [hinv.peek, hb]
    exact ⟨_, _, rfl, hinv⟩
  | content_implicitSeq hb hent ih =>
    intro ps fuel props hinv hf
    have hlt := seqEntries_lt hent hb
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    unfold parseNodeContent
    rw [hinv.peek, hb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold parseImplicitBlockSequence
    simp only [bind, Except.bind, pure, Except.pure]
    obtain ⟨_, items', ps', hloop, hinv'⟩ := ih ps f #[] hinv (by simp [fuelReq] at hf ⊢; omega)
    rw [hloop]
    exact ⟨_, _, rfl, hinv'⟩
  | content_flowSeq hb ih =>
    intro ps fuel props hinv hf
    unfold parseNodeContent
    rw [hinv.peek]
    cases hb with
    | flowSeq hs _ _ =>
      rw [hs]
      exact ih ps fuel hinv (by simpa [fuelReq] using hf)
  | content_flowMap hb ih =>
    intro ps fuel props hinv hf
    unfold parseNodeContent
    rw [hinv.peek]
    cases hb with
    | flowMap hs _ _ =>
      rw [hs]
      exact ih ps fuel hinv (by simpa [fuelReq] using hf)
  | content_empty he =>
    intro ps fuel props hinv _
    unfold parseNodeContent
    rw [hinv.peek]
    cases ho : tok ts _ with
    | none => exact ⟨_, _, rfl, hinv⟩
    | some t => cases t <;> simp [emptyFollower, ho] at he <;> exact ⟨_, _, rfl, hinv⟩
  | blockSeq hs hent hend ih =>
    intro ps fuel hinv hf
    have hle := tg_le hent
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    unfold parseBlockSequence
    simp only [bind, Except.bind, pure, Except.pure]
    obtain ⟨⟨items', ps', hloop, hinv'⟩, _⟩ :=
      ih ps.advance f #[] (hinv.step hs rfl) (by simp [fuelReq] at hf ⊢; omega)
    rw [hloop]
    simp only []
    rw [hinv'.peek, hend]
    exact ⟨_, _, rfl, hinv'.step hend rfl⟩
  | seqEntries_nil hne =>
    intro ps fuel items hinv _
    cases fuel with
    | zero =>
      exact ⟨⟨items, ps, by unfold parseBlockSequenceLoop; rfl, hinv⟩,
        ⟨items, ps, by unfold parseImplicitBlockSequenceLoop; rfl, hinv⟩⟩
    | succ f =>
      refine ⟨⟨items, ps, ?_, hinv⟩, ⟨items, ps, ?_, hinv⟩⟩
      · unfold parseBlockSequenceLoop
        rw [hinv.peek]
        split
        · exact absurd ‹_› hne
        · rfl
      · unfold parseImplicitBlockSequenceLoop
        rw [hinv.peek]
        split
        · exact absurd ‹_› hne
        · rfl
  | seqEntries_cons hb hn hr ihn ihr =>
    intro ps fuel items hinv hf
    have hle1 := tg_le hn
    have hle2 := tg_le hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    have hinv1 := hinv.step hb rfl
    constructor
    · unfold parseBlockSequenceLoop
      rw [hinv.peek, hb]
      simp only [bind, Except.bind, pure, Except.pure]
      rw [hinv.peek_advance]
      split
      all_goals first
        | (have hm := node_after_entry_empty hb hn (by rename_i hnext; simp [hnext, startsNode])
           subst hm
           exact (ihr ps.advance f _ hinv1 (by simp [fuelReq] at hf ⊢; omega)).1)
        | (obtain ⟨v, ps2, hnode, hinv2⟩ :=
             ihn { ps.advance with currentPath := ps.advance.currentPath.push (.index items.size) } f
               (hinv1.same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega)
           rw [hnode]
           exact (ihr { ps2 with currentPath := ps.advance.currentPath } f _
             (hinv2.same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega)).1)
    · unfold parseImplicitBlockSequenceLoop
      rw [hinv.peek, hb]
      simp only [bind, Except.bind, pure, Except.pure]
      rw [hinv.peek_advance]
      split
      all_goals first
        | (have hm := node_after_entry_empty hb hn (by rename_i hnext; simp [hnext, startsNode])
           subst hm
           exact (ihr ps.advance f _ hinv1 (by simp [fuelReq] at hf ⊢; omega)).2)
        | (obtain ⟨v, ps2, hnode, hinv2⟩ :=
             ihn { ps.advance with currentPath := ps.advance.currentPath.push (.index items.size) } f
               (hinv1.same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega)
           rw [hnode]
           exact (ihr { ps2 with currentPath := ps.advance.currentPath } f _
             (hinv2.same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega)).2)
  | blockMap hs hent hend ih =>
    intro ps fuel hinv hf
    have hle := tg_le hent
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    unfold parseBlockMapping
    simp only [bind, Except.bind, pure, Except.pure]
    obtain ⟨pairs', ps', hloop, hinv'⟩ :=
      ih ps.advance f #[] (hinv.step hs rfl) (by simp [fuelReq] at hf ⊢; omega)
    rw [hloop]
    simp only []
    rw [hinv'.peek, hend]
    exact ⟨_, _, rfl, hinv'.step hend rfl⟩
  | mapEntries_nil hk hv =>
    intro ps fuel pairs hinv _
    cases fuel with
    | zero => exact ⟨pairs, ps, by unfold parseBlockMappingLoop; rfl, hinv⟩
    | succ f =>
      refine ⟨pairs, ps, ?_, hinv⟩
      unfold parseBlockMappingLoop
      rw [hinv.peek]
      split
      · exact absurd ‹_› hk
      · exact absurd ‹_› hv
      · rfl
  | mapEntries_key hk hke hr ihk ihr =>
    intro ps fuel pairs hinv hf
    have hlt := keyEntry_lt hke
    have hle := tg_le hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    unfold parseBlockMappingLoop
    rw [hinv.peek, hk]
    simp only [bind, Except.bind, pure, Except.pure]
    obtain ⟨k, v, ps2, hent, hinv2⟩ := ihk ps f pairs.size hinv (by simp [fuelReq] at hf ⊢; omega)
    rw [hent]
    exact ihr ps2 f _ hinv2 (by simp [fuelReq] at hf ⊢; omega)
  | mapEntries_value hv hn hr ihn ihr =>
    rename_i i0 m0 j0
    intro ps fuel pairs hinv hf
    have hle1 := tg_le hn
    have hle2 := tg_le hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    have hinv1 := hinv.step hv rfl
    unfold parseBlockMappingLoop
    rw [hinv.peek, hv]
    simp only [bind, Except.bind, pure, Except.pure]
    unfold handleBlockMappingValueEntry
    simp only [bind, Except.bind, pure, Except.pure]
    have hpk : ({ ps.advance with currentPath := ps.advance.currentPath.push (.key s!"{pairs.size}") }
        : ParseState).peek? = tok ts (i0 + 1) := by
      rw [show ({ ps.advance with currentPath := ps.advance.currentPath.push (.key s!"{pairs.size}") }
        : ParseState).peek? = ps.advance.peek? from rfl, hinv.peek_advance]
    erw [hpk]
    rcases ho : tok ts (i0 + 1) with _ | t <;> (try cases t)
    all_goals first
      | (have hm := node_empty_of hn (by first | simp [ho, startsNode] | (rw [ho]; rfl))
         subst hm
         exact ihr { ps.advance with currentPath := ps.advance.currentPath } f
           (pairs.push (emptyNode, emptyNode)) (hinv1.same rfl rfl rfl rfl)
           (by simp [fuelReq] at hf ⊢; omega))
      | (obtain ⟨v, ps2, hnode, hinv2⟩ :=
           ihn { ps.advance with currentPath := ps.advance.currentPath.push (.key s!"{pairs.size}") } f
             (hinv1.same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega)
         obtain ⟨p', ps', hloop, hinv'⟩ :=
           ihr { ps2 with currentPath := ps.advance.currentPath } f (pairs.push (emptyNode, v))
             (hinv2.same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega)
         refine ⟨p', ps', ?_, hinv'⟩
         simp only [hnode]
         exact hloop)
  | keyEntry hk hn hv ihn ihv =>
    rename_i i0 m0 j0
    intro ps fuel idx hinv hf
    have hle1 := tg_le hn
    have hle2 := tg_le hv
    have hinv1 := hinv.step hk rfl
    unfold handleBlockMappingKeyEntry
    simp only [bind, Except.bind, pure, Except.pure]
    rw [peekPos_getD hinv.tokens, hinv.pos, hinv.peek_advance]
    rcases ho : tok ts (i0 + 1) with _ | t <;> (try cases t)
    all_goals first
      | (have hm := node_empty_of hn (by rw [ho]; rfl)
         subst hm
         obtain ⟨v2, ps3, hval, hinv3⟩ := ihv
           { ps.advance with currentPath := (ps.advance.currentPath.push (.key (keyName emptyNode idx))) } fuel
           (hinv1.same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega)
         simp only [keyHasContentAt, ho] at hval
         simp only [Bool.false_eq_true, ↓reduceIte]
         erw [hval]
         exact ⟨_, _, _, rfl, hinv3.same rfl rfl rfl rfl⟩)
      | (simp only [↓reduceIte]
         obtain ⟨v, ps2, hnode, hinv2⟩ := ihn ps.advance fuel hinv1 (by simp [fuelReq] at hf ⊢; omega)
         simp only [hnode]
         obtain ⟨v2, ps3, hval, hinv3⟩ := ihv
           { ps2 with currentPath := (ps2.currentPath.push (.key (keyName v idx))) } fuel
           (hinv2.same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega)
         simp only [keyHasContentAt, ho] at hval
         erw [hval]
         exact ⟨_, _, _, rfl, hinv3.same rfl rfl rfl rfl⟩)
  | entryValue_value hv hvp hkl hn ih =>
    intro ps fuel hinv hf
    have hle := tg_le hn
    have hm := tok_some_lt hv
    have hinv1 := hinv.step hv rfl
    unfold parseBlockMappingEntryValue
    rw [tryConsume_hit hinv hv rfl]
    simp only [bind, Except.bind, pure, Except.pure, ↓reduceIte]
    erw [valueProps_loop_ok hinv1 hvp hm]
    simp only []
    rw [hinv1.peek]
    split
    all_goals first
      | (have hj := node_empty_of hn (by rename_i hnext; simp [hnext, startsNode])
         subst hj
         exact ⟨_, _, rfl, hinv1⟩)
      | (rename_i hnext
         rw [peekPos_getD hinv1.tokens, hinv1.pos]
         split
         · rename_i hc
           exfalso
           rw [Bool.and_eq_true, beq_iff_eq] at hc
           exact hkl (by simp [hnext, isBlockStart]) hc.1 hc.2
         · exact ih ps.advance fuel hinv1 (by simp [fuelReq] at hf ⊢; omega))
      | exact ih ps.advance fuel hinv1 (by simp [fuelReq] at hf ⊢; omega)
  | entryValue_retro hk hv hn ih =>
    intro ps fuel hinv hf
    have hle := tg_le hn
    have hinv1 := hinv.step hk rfl
    have hinv2 := hinv1.step hv rfl
    unfold parseBlockMappingEntryValue
    rw [tryConsume_value_miss hinv (by simp [hk])]
    simp only [bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
    rw [hinv.peek, peekNext_tok hinv.tokens, hinv.pos, hk, hv]
    simp only []
    rw [tryConsume_hit hinv hk rfl, tryConsume_hit hinv1 hv rfl]
    simp only []
    rw [hinv2.peek]
    split
    all_goals first
      | (have hj := node_empty_of hn (by rename_i hnext; simp [hnext, startsNode])
         subst hj
         exact ⟨_, _, rfl, hinv2⟩)
      | exact ih _ fuel hinv2 (by simp [fuelReq] at hf ⊢; omega)
  | entryValue_none hnv hnkv =>
    intro ps fuel hinv _
    unfold parseBlockMappingEntryValue
    rw [tryConsume_value_miss hinv hnv]
    simp only [bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
    rw [hinv.peek, peekNext_tok hinv.tokens, hinv.pos]
    split
    · exact absurd ⟨‹_›, ‹_›⟩ hnkv
    · exact ⟨_, _, rfl, hinv⟩
  | flowSeq hs hit hend ih =>
    intro ps fuel hinv hf
    have hle := tg_le hit
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    unfold parseFlowSequence
    simp only [bind, Except.bind, pure, Except.pure]
    obtain ⟨items', ps', hloop, hinv'⟩ := ih ps.advance f #[] (hinv.step hs rfl)
      (by simp [fuelReq] at hf ⊢; omega) (by simp)
    rw [hloop]
    simp only []
    rw [hinv'.peek, hend]
    exact ⟨_, _, rfl, hinv'.step hend rfl⟩
  | flowSeqItems_end he =>
    intro ps fuel items hinv _ _
    cases fuel with
    | zero => exact ⟨items, ps, by unfold parseFlowSequenceLoop; rfl, hinv⟩
    | succ f =>
      refine ⟨items, ps, ?_, hinv⟩
      unfold parseFlowSequenceLoop
      rw [hinv.peek, he]
  | flowSeqItems_trailing hfe he =>
    intro ps fuel items hinv hf hfirst
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    have hsz : items.size > 0 := by
      have := hfirst.2; by_cases h0 : items.size = 0
      · exact absurd (this h0) Bool.false_ne_true
      · omega
    unfold parseFlowSequenceLoop
    rw [hinv.peek, hfe]
    simp only [hsz, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    rw [hinv.peek_advance, he]
    exact ⟨_, _, rfl, hinv.step hfe rfl⟩
  | flowMap hs hit hend ih =>
    intro ps fuel hinv hf
    have hle := tg_le hit
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    unfold parseFlowMapping
    simp only [bind, Except.bind, pure, Except.pure]
    obtain ⟨pairs', ps', hloop, hinv'⟩ := ih ps.advance f #[] (hinv.step hs rfl)
      (by simp [fuelReq] at hf ⊢; omega) (by simp)
    rw [hloop]
    simp only []
    rw [hinv'.peek, hend]
    exact ⟨_, _, rfl, hinv'.step hend rfl⟩
  | flowMapEntries_end he =>
    intro ps fuel pairs hinv _ _
    cases fuel with
    | zero => exact ⟨pairs, ps, by unfold parseFlowMappingLoop; rfl, hinv⟩
    | succ f =>
      refine ⟨pairs, ps, ?_, hinv⟩
      unfold parseFlowMappingLoop
      rw [hinv.peek, he]
  | flowMapEntries_trailing hfe he =>
    intro ps fuel pairs hinv hf hfirst
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    have hsz : pairs.size > 0 := by
      have := hfirst.2; by_cases h0 : pairs.size = 0
      · exact absurd (this h0) Bool.false_ne_true
      · omega
    unfold parseFlowMappingLoop
    rw [hinv.peek, hfe]
    simp only [hsz, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    rw [hinv.peek_advance, he]
    exact ⟨_, _, rfl, hinv.step hfe rfl⟩
  | flowMapValue_value hr' hv hn ih =>
    rename_i r0 r0' j0
    intro ps fuel path kc hinv hf
    have hle := tg_le hn
    unfold parseFlowMappingValue
    simp only [bind, Except.bind, pure, Except.pure]
    have hinv0 : Inv ts ({ ps with currentPath := path.push (.key kc) } : ParseState) r0 :=
      hinv.same rfl rfl rfl rfl
    -- after the optional `?`, we sit at r0'
    have step1 : ∃ (b : Bool) (ps1 : ParseState), ({ ps with currentPath := path.push (.key kc) }
        : ParseState).tryConsume .key = (b, ps1) ∧ Inv ts ps1 r0' := by
      rcases hr' with ⟨hk, hq⟩ | ⟨hk, hq⟩
      · subst hq; exact ⟨_, _, tryConsume_hit hinv0 hk rfl, hinv0.step hk rfl⟩
      · subst hq; exact ⟨_, _, tryConsume_key_miss hinv0 hk, hinv0⟩
    obtain ⟨b, ps1, h1, hinv1⟩ := step1
    rw [h1]
    simp only []
    rw [tryConsume_hit hinv1 hv rfl]
    simp only [↓reduceIte]
    have hinv2 := hinv1.step hv rfl
    rw [hinv2.peek]
    rcases ho : tok ts (r0' + 1) with _ | t <;> (try cases t)
    all_goals first
      | (have hj := node_empty_of hn (by rw [ho]; rfl)
         subst hj
         exact ⟨_, _, rfl, hinv2.same rfl rfl rfl rfl⟩)
      | (obtain ⟨v, ps3, hnode, hinv3⟩ := ih ps1.advance fuel hinv2 (by simp [fuelReq] at hf ⊢; omega)
         simp only [hnode]
         exact ⟨_, _, rfl, hinv3.same rfl rfl rfl rfl⟩)
  | flowMapValue_none hr' hnv =>
    rename_i r0 r0'
    intro ps fuel path kc hinv _
    unfold parseFlowMappingValue
    simp only [bind, Except.bind, pure, Except.pure]
    have hinv0 : Inv ts ({ ps with currentPath := path.push (.key kc) } : ParseState) r0 :=
      hinv.same rfl rfl rfl rfl
    have step1 : ∃ (b : Bool) (ps1 : ParseState), ({ ps with currentPath := path.push (.key kc) }
        : ParseState).tryConsume .key = (b, ps1) ∧ Inv ts ps1 r0' := by
      rcases hr' with ⟨hk, hq⟩ | ⟨hk, hq⟩
      · subst hq; exact ⟨_, _, tryConsume_hit hinv0 hk rfl, hinv0.step hk rfl⟩
      · subst hq; exact ⟨_, _, tryConsume_key_miss hinv0 hk, hinv0⟩
    obtain ⟨b, ps1, h1, hinv1⟩ := step1
    rw [h1]
    simp only []
    rw [tryConsume_value_miss hinv1 hnv]
    exact ⟨_, _, rfl, hinv1.same rfl rfl rfl rfl⟩
  | flowSeqItems_pair hne hsep hk hsp hr ihsp ihr =>
    rename_i i0 q0 m0 j0
    intro ps fuel items hinv hf hfirst
    have hle1 := tg_le hsp
    have hle2 := tg_le hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    unfold parseFlowSequenceLoop
    rw [hinv.peek]
    split
    · rename_i h; exact absurd h hne
    rcases hsep with ⟨hfirst', rfl⟩ | ⟨hfirst', hfe, rfl⟩
    · subst hfirst'
      have hsz : ¬ items.size > 0 := by have := hfirst.1 rfl; omega
      simp only [hsz, ↓reduceIte, bind, Except.bind, pure, Except.pure]
      rw [hinv.peek, hk]
      simp only [bind, Except.bind, pure, Except.pure]
      obtain ⟨v, ps2, hsp, hinv2⟩ := ihsp
        { ps with currentPath := (ps.currentPath.push (.index items.size)) } f
        (hinv.same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega)
      simp only [hsp]
      exact ihr { ps2 with currentPath := ps.currentPath } f (items.push v)
        (hinv2.same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega) (by simp)
    · subst hfirst'
      have hsz : items.size > 0 := by
        by_cases h0 : items.size = 0
        · exact absurd (hfirst.2 h0) Bool.false_ne_true
        · omega
      simp only [hsz, ↓reduceIte, hfe, bind, Except.bind, pure, Except.pure]
      rw [hinv.peek_advance, hk]
      simp only [bind, Except.bind, pure, Except.pure]
      obtain ⟨v, ps2, hsp, hinv2⟩ := ihsp
        { ps.advance with currentPath := (ps.advance.currentPath.push (.index items.size)) } f
        ((hinv.step hfe rfl).same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega)
      simp only [hsp]
      exact ihr { ps2 with currentPath := ps.advance.currentPath } f (items.push v)
        (hinv2.same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega) (by simp)
  | flowSeqItems_node hne hsep hnk hnend hn hr ihn ihr =>
    rename_i i0 q0 m0 j0
    intro ps fuel items hinv hf hfirst
    have hle1 := tg_le hn
    have hle2 := tg_le hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    unfold parseFlowSequenceLoop
    rw [hinv.peek]
    split
    · rename_i h; exact absurd h hne
    rcases hsep with ⟨hfirst', rfl⟩ | ⟨hfirst', hfe, rfl⟩
    · subst hfirst'
      have hsz : ¬ items.size > 0 := by have := hfirst.1 rfl; omega
      simp only [hsz, ↓reduceIte, bind, Except.bind, pure, Except.pure]
      rw [hinv.peek]
      simp only [bind, Except.bind, pure, Except.pure]
      rcases ho : tok ts q0 with _ | t <;> (try cases t)
      all_goals first
        | exact absurd ho hnk
        | exact absurd ho hnend
        | (obtain ⟨v, ps2, hnode, hinv2⟩ := ihn
             { ps with currentPath := (ps.currentPath.push (.index items.size)) } f
             (hinv.same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega)
           simp only [hnode]
           exact ihr { ps2 with currentPath := ps.currentPath } f (items.push v)
             (hinv2.same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega) (by simp))
    · subst hfirst'
      have hsz : items.size > 0 := by
        by_cases h0 : items.size = 0
        · exact absurd (hfirst.2 h0) Bool.false_ne_true
        · omega
      simp only [hsz, ↓reduceIte, hfe, bind, Except.bind, pure, Except.pure]
      rw [hinv.peek_advance]
      simp only [bind, Except.bind, pure, Except.pure]
      rcases ho : tok ts (i0 + 1) with _ | t <;> (try cases t)
      all_goals first
        | exact absurd ho hnk
        | exact absurd ho hnend
        | (obtain ⟨v, ps2, hnode, hinv2⟩ := ihn
             { ps.advance with currentPath := (ps.advance.currentPath.push (.index items.size)) } f
             ((hinv.step hfe rfl).same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega)
           simp only [hnode]
           exact ihr { ps2 with currentPath := ps.advance.currentPath } f (items.push v)
             (hinv2.same rfl rfl rfl rfl) (by simp [fuelReq] at hf ⊢; omega) (by simp))
  | singlePair_value hk hn hv hn2 ihn ihv =>
    rename_i i0 r0 j0
    intro ps fuel hinv hf
    have hle1 := tg_le hn
    have hle2 := tg_le hn2
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    have hinv1 := hinv.step hk rfl
    unfold parseSinglePairMapping
    simp only []
    rw [hinv1.peek]
    rcases ho : tok ts (i0 + 1) with _ | t <;> (try cases t)
    all_goals first
      | (have hr := node_empty_of hn (by rw [ho]; rfl)
         subst hr
         simp only [bind, Except.bind, pure, Except.pure]
         have hinv2' : Inv ts ({ ps.advance with currentPath := ps.advance.currentPath.push (.key (keyPathSegment emptyNode)) }
           : ParseState) _ := hinv1.same rfl rfl rfl rfl
         rw [tryConsume_hit hinv2' hv rfl]
         simp only [↓reduceIte]
         have hinv3 := hinv2'.step hv rfl
         rw [hinv3.peek]
         rcases ho2 : tok ts (i0 + 1 + 1) with _ | t2 <;> (try cases t2)
         all_goals first
           | (have hj := node_empty_of hn2 (by rw [ho2]; rfl)
              subst hj
              exact ⟨_, _, rfl, hinv3.same rfl rfl rfl rfl⟩)
           | (obtain ⟨v, ps4, hnode2, hinv4⟩ := ihv _ f hinv3 (by simp [fuelReq] at hf ⊢; omega)
              simp only [hnode2]
              exact ⟨_, _, rfl, hinv4.same rfl rfl rfl rfl⟩))
      | (have hr := node_empty_of hn (by rw [ho]; rfl)
         subst hr
         exact absurd (ho.symm.trans hv) nofun)
      | (obtain ⟨key, ps2, hnode, hinv2⟩ := ihn ps.advance f hinv1 (by simp [fuelReq] at hf ⊢; omega)
         simp only [bind, Except.bind, pure, Except.pure, hnode]
         have hinv2' : Inv ts ({ ps2 with currentPath := ps2.currentPath.push (.key (keyPathSegment key)) }
           : ParseState) _ := hinv2.same rfl rfl rfl rfl
         rw [tryConsume_hit hinv2' hv rfl]
         simp only [↓reduceIte]
         have hinv3 := hinv2'.step hv rfl
         rw [hinv3.peek]
         rcases ho2 : tok ts (r0 + 1) with _ | t2 <;> (try cases t2)
         all_goals first
           | (have hj := node_empty_of hn2 (by rw [ho2]; rfl)
              subst hj
              exact ⟨_, _, rfl, hinv3.same rfl rfl rfl rfl⟩)
           | (obtain ⟨v, ps4, hnode2, hinv4⟩ := ihv _ f hinv3 (by simp [fuelReq] at hf ⊢; omega)
              simp only [hnode2]
              exact ⟨_, _, rfl, hinv4.same rfl rfl rfl rfl⟩))
  | singlePair_noValue hk hn hnv ihn =>
    rename_i i0 r0
    intro ps fuel hinv hf
    have hle1 := tg_le hn
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    have hinv1 := hinv.step hk rfl
    unfold parseSinglePairMapping
    simp only []
    rw [hinv1.peek]
    rcases ho : tok ts (i0 + 1) with _ | t <;> (try cases t)
    all_goals first
      | (have hr := node_empty_of hn (by rw [ho]; rfl)
         subst hr
         simp only [bind, Except.bind, pure, Except.pure]
         have hinv2' : Inv ts ({ ps.advance with currentPath := ps.advance.currentPath.push (.key (keyPathSegment emptyNode)) }
           : ParseState) _ := hinv1.same rfl rfl rfl rfl
         rw [tryConsume_value_miss hinv2' hnv]
         exact ⟨_, _, rfl, hinv2'.same rfl rfl rfl rfl⟩)
      | (obtain ⟨key, ps2, hnode, hinv2⟩ := ihn ps.advance f hinv1 (by simp [fuelReq] at hf ⊢; omega)
         simp only [bind, Except.bind, pure, Except.pure, hnode]
         have hinv2' : Inv ts ({ ps2 with currentPath := ps2.currentPath.push (.key (keyPathSegment key)) }
           : ParseState) _ := hinv2.same rfl rfl rfl rfl
         rw [tryConsume_value_miss hinv2' hnv]
         exact ⟨_, _, rfl, hinv2'.same rfl rfl rfl rfl⟩)
  | flowMapEntries_explicit hne hsep hk hn hv hr ihn ihv ihr =>
    rename_i i0 q0 r0 m0 j0
    intro ps fuel pairs hinv hf hfirst
    have hle1 := tg_le hn
    have hle2 := tg_le hv
    have hle3 := tg_le hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    unfold parseFlowMappingLoop
    rw [hinv.peek]
    split
    · rename_i h; exact absurd h hne
    rcases hsep with ⟨hfirst', rfl⟩ | ⟨hfirst', hfe, rfl⟩
    · subst hfirst'
      have hsz : ¬ pairs.size > 0 := by have := hfirst.1 rfl; omega
      simp only [hsz, ↓reduceIte, bind, Except.bind, pure, Except.pure]
      rw [hinv.peek, hk]
      simp only [bind, Except.bind, pure, Except.pure]
      unfold parseExplicitKey
      rw [(hinv.step hk rfl).peek]
      rcases ho : tok ts (q0 + 1) with _ | t <;> (try cases t)
      all_goals first
        | (have hr := node_empty_of hn (by rw [ho]; rfl)
           subst hr
           simp only []
           obtain ⟨v, ps3, hval, hinv3⟩ := ihv ps.advance f ps.advance.currentPath (keyName emptyNode pairs.size) (hinv.step hk rfl)
             (by simp [fuelReq] at hf ⊢; omega)
           erw [hval]
           exact ihr ps3 f (pairs.push (emptyNode, v)) hinv3 (by simp [fuelReq] at hf ⊢; omega) (by simp))
        | (obtain ⟨key, ps2, hnode, hinv2⟩ := ihn ps.advance f (hinv.step hk rfl) (by simp [fuelReq] at hf ⊢; omega)
           simp only [hnode]
           obtain ⟨v, ps3, hval, hinv3⟩ := ihv ps2 f ps2.currentPath (keyName key pairs.size) hinv2
             (by simp [fuelReq] at hf ⊢; omega)
           erw [hval]
           exact ihr ps3 f (pairs.push (key, v)) hinv3 (by simp [fuelReq] at hf ⊢; omega) (by simp))
    · subst hfirst'
      have hsz : pairs.size > 0 := by
        by_cases h0 : pairs.size = 0
        · exact absurd (hfirst.2 h0) Bool.false_ne_true
        · omega
      simp only [hsz, ↓reduceIte, hfe, bind, Except.bind, pure, Except.pure]
      rw [hinv.peek_advance, hk]
      simp only [bind, Except.bind, pure, Except.pure]
      unfold parseExplicitKey
      rw [((hinv.step hfe rfl).step hk rfl).peek]
      rcases ho : tok ts ((i0 + 1) + 1) with _ | t <;> (try cases t)
      all_goals first
        | (have hr := node_empty_of hn (by rw [ho]; rfl)
           subst hr
           simp only []
           obtain ⟨v, ps3, hval, hinv3⟩ := ihv ps.advance.advance f ps.advance.advance.currentPath (keyName emptyNode pairs.size) ((hinv.step hfe rfl).step hk rfl)
             (by simp [fuelReq] at hf ⊢; omega)
           erw [hval]
           exact ihr ps3 f (pairs.push (emptyNode, v)) hinv3 (by simp [fuelReq] at hf ⊢; omega) (by simp))
        | (obtain ⟨key, ps2, hnode, hinv2⟩ := ihn ps.advance.advance f ((hinv.step hfe rfl).step hk rfl) (by simp [fuelReq] at hf ⊢; omega)
           simp only [hnode]
           obtain ⟨v, ps3, hval, hinv3⟩ := ihv ps2 f ps2.currentPath (keyName key pairs.size) hinv2
             (by simp [fuelReq] at hf ⊢; omega)
           erw [hval]
           exact ihr ps3 f (pairs.push (key, v)) hinv3 (by simp [fuelReq] at hf ⊢; omega) (by simp))
  | flowMapEntries_implicit hne hsep hnk hnend hn hv hr ihn ihv ihr =>
    rename_i i0 q0 r0 m0 j0
    intro ps fuel pairs hinv hf hfirst
    have hle1 := tg_le hn
    have hle2 := tg_le hv
    have hle3 := tg_le hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [fuelReq] at hf; omega⟩
    unfold parseFlowMappingLoop
    rw [hinv.peek]
    split
    · rename_i h; exact absurd h hne
    rcases hsep with ⟨hfirst', rfl⟩ | ⟨hfirst', hfe, rfl⟩
    · subst hfirst'
      have hsz : ¬ pairs.size > 0 := by have := hfirst.1 rfl; omega
      simp only [hsz, ↓reduceIte, bind, Except.bind, pure, Except.pure]
      rw [hinv.peek]
      simp only [bind, Except.bind, pure, Except.pure]
      rcases ho : tok ts q0 with _ | t <;> (try cases t)
      all_goals first
        | exact absurd ho hnend
        | exact absurd ho hnk
        | (obtain ⟨key, ps2, hnode, hinv2⟩ := ihn ps f hinv (by simp [fuelReq] at hf ⊢; omega)
           simp only [hnode]
           obtain ⟨v, ps3, hval, hinv3⟩ := ihv ps2 f ps2.currentPath (keyName key pairs.size) hinv2
             (by simp [fuelReq] at hf ⊢; omega)
           erw [hval]
           exact ihr ps3 f (pairs.push (key, v)) hinv3 (by simp [fuelReq] at hf ⊢; omega) (by simp))
    · subst hfirst'
      have hsz : pairs.size > 0 := by
        by_cases h0 : pairs.size = 0
        · exact absurd (hfirst.2 h0) Bool.false_ne_true
        · omega
      simp only [hsz, ↓reduceIte, hfe, bind, Except.bind, pure, Except.pure]
      rw [hinv.peek_advance]
      simp only [bind, Except.bind, pure, Except.pure]
      rcases ho : tok ts (i0 + 1) with _ | t <;> (try cases t)
      all_goals first
        | exact absurd ho hnend
        | exact absurd ho hnk
        | (obtain ⟨key, ps2, hnode, hinv2⟩ := ihn ps.advance f (hinv.step hfe rfl) (by simp [fuelReq] at hf ⊢; omega)
           simp only [hnode]
           obtain ⟨v, ps3, hval, hinv3⟩ := ihv ps2 f ps2.currentPath (keyName key pairs.size) hinv2
             (by simp [fuelReq] at hf ⊢; omega)
           erw [hval]
           exact ihr ps3 f (pairs.push (key, v)) hinv3 (by simp [fuelReq] at hf ⊢; omega) (by simp))



/-! ## Document level: directives, `---`, and the per-document environment -/

/-- The environment is clean: no anchors, no `%TAG` handles. -/
def EnvReset (ts : Toks) (i : Nat) : Prop :=
  (envAt ts i).anchors = [] ∧ (envAt ts i).tagHandles = []

/-- `h` is declared by a `%TAG` directive in `[lo, hi)`. -/
def DeclaredIn (ts : Toks) (lo hi : Nat) (h : String) : Prop :=
  ∃ p pre, lo ≤ p ∧ p < hi ∧ tok ts p = some (.tagDirective h pre)

/-- After the directives of a document starting at `lo`: no anchors, only declared handles. -/
def DirEnvOk (ts : Toks) (lo i : Nat) : Prop :=
  (envAt ts i).anchors = [] ∧ ∀ h, h ∈ (envAt ts i).tagHandles → DeclaredIn ts lo i h

/-- The `declareTag` event of a directive-like token. -/
def decl : YamlToken → List Event
  | .tagDirective h _ => if isNamedHandle h then [.declareTag h] else []
  | _ => []

lemma envAt_succ_begin_reset {ts : Toks} {i : Nat} {t : YamlToken} (hi : 0 < i)
    (hnd : NotDirBefore ts i) (ho : tok ts i = some t)
    (hb : t = .documentStart ∨ isDirective (some t) = true) :
    envAt ts (i + 1) = envAfter {} (decl t) := by
  rw [envAt_succ]
  unfold perTokenEvents prevDirAt
  rw [ho]
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  unfold NotDirBefore at hnd
  simp only [Nat.add_sub_cancel] at hnd
  rcases hb with rfl | hd
  · simp [hnd, envAfter, stepEnv, decl]
  · cases t with
    | tagDirective h _ =>
      by_cases hb : isNamedHandle h = true <;> simp [hnd, hb, envAfter, stepEnv, decl]
    | _ => simp [isDirective] at hd <;> simp [hnd, envAfter, stepEnv, decl]

lemma envAt_succ_begin_keep {ts : Toks} {i : Nat} {t : YamlToken} (hi : 0 < i)
    (hpd : isDirective (tok ts (i - 1)) = true) (ho : tok ts i = some t)
    (hb : t = .documentStart ∨ isDirective (some t) = true) :
    envAt ts (i + 1) = envAfter (envAt ts i) (decl t) := by
  rw [envAt_succ]
  unfold perTokenEvents prevDirAt
  rw [ho]
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hpd
  rcases hb with rfl | hd
  · simp [hpd, envAfter, stepEnv, decl]
  · cases t with
    | tagDirective h _ =>
      by_cases hb : BuiltinTagHandle h <;> simp [hpd, hb, envAfter, stepEnv, decl]
    | _ => simp [isDirective] at hd <;> simp [hpd, envAfter, stepEnv, decl]

lemma dirEnvOk_of_decl {ts : Toks} {lo i : Nat} {t : YamlToken} {env : Env}
    (hlo : lo ≤ i) (ho : tok ts i = some t) (henv : envAt ts (i + 1) = envAfter env (decl t))
    (ha : env.anchors = []) (hg : ∀ h, h ∈ env.tagHandles → DeclaredIn ts lo i h) :
    DirEnvOk ts lo (i + 1) := by
  unfold DirEnvOk
  rw [henv]
  have mono : ∀ h, DeclaredIn ts lo i h → DeclaredIn ts lo (i + 1) h := by
    rintro h ⟨p, pre, h1, h2, h3⟩; exact ⟨p, pre, h1, by omega, h3⟩
  cases t with
  | tagDirective h pre =>
    by_cases hb : isNamedHandle h = true
    · refine ⟨by simp [envAfter, stepEnv, decl, hb, ha], ?_⟩
      intro h' hm
      simp only [envAfter, decl, hb, ↓reduceIte, List.foldl, stepEnv, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ⟨i, pre, hlo, by omega, ho⟩
      · exact mono _ (hg _ hm)
    · exact ⟨by simp [envAfter, decl, hb, ha], fun h' hm => mono _ (hg _ (by simpa [envAfter, decl, hb] using hm))⟩
  | _ => exact ⟨by simp [envAfter, decl, ha], fun h hm => mono _ (hg _ (by simpa [envAfter, decl] using hm))⟩

lemma dirEnvOk_reset {ts : Toks} {lo i : Nat} {t : YamlToken} (hi : 0 < i) (hlo : lo ≤ i)
    (hnd : NotDirBefore ts i) (ho : tok ts i = some t)
    (hb : t = .documentStart ∨ isDirective (some t) = true) : DirEnvOk ts lo (i + 1) :=
  dirEnvOk_of_decl hlo ho (envAt_succ_begin_reset hi hnd ho hb) rfl (fun _ hm => by cases hm)

lemma dirEnvOk_keep {ts : Toks} {lo i : Nat} {t : YamlToken} (hi : 0 < i) (hlo : lo ≤ i)
    (hpd : isDirective (tok ts (i - 1)) = true) (ho : tok ts i = some t)
    (hb : t = .documentStart ∨ isDirective (some t) = true) (hok : DirEnvOk ts lo i) :
    DirEnvOk ts lo (i + 1) :=
  dirEnvOk_of_decl hlo ho (envAt_succ_begin_keep hi hpd ho hb) hok.1 hok.2

lemma dirEnvOk_step {ts : Toks} {lo i : Nat} (hi : 0 < i) (hlo : lo ≤ i)
    (hd : isDirective (tok ts i) = true) (hok : DirEnvOk ts lo i) : DirEnvOk ts lo (i + 1) := by
  obtain ⟨t, ho⟩ : ∃ t, tok ts i = some t := by
    cases h : tok ts i with
    | none => simp [h, isDirective] at hd
    | some t => exact ⟨t, rfl⟩
  rw [ho] at hd
  by_cases hnd : NotDirBefore ts i
  · exact dirEnvOk_reset hi hlo hnd ho (Or.inr hd)
  · have hpd : isDirective (tok ts (i - 1)) = true := by
      unfold NotDirBefore at hnd
      cases h : isDirective (tok ts (i - 1)) <;> simp_all
    exact dirEnvOk_keep hi hlo hpd ho (Or.inr hd) hok

lemma dirs_facts {ts : Toks} {s : Sym} {i d : Nat} (h : TG ts s i d) :
    (match s with
      | .directives => isDirective (tok ts d) = false ∧ (i ≤ ts.size → d ≤ ts.size) ∧
          (i < d → isDirective (tok ts (d - 1)) = true) ∧
          (∀ lo, 0 < lo → lo ≤ i → DirEnvOk ts lo i → DirEnvOk ts lo d)
      | _ => True) := by
  induction h with
  | directives_nil hn => exact ⟨hn, fun h => h, fun h => absurd h (Nat.lt_irrefl _), fun _ _ _ h => h⟩
  | directives_cons hd hr ih =>
    rename_i i0 d0
    obtain ⟨t, ho⟩ : ∃ t, tok ts i0 = some t := by
      cases h : tok ts i0 with
      | none => simp [h, isDirective] at hd
      | some t => exact ⟨t, rfl⟩
    have hlt := tok_some_lt ho
    have hle := tg_le hr
    refine ⟨ih.1, fun _ => ih.2.1 (by omega), fun _ => ?_, fun lo hlo0 hlo hok => ?_⟩
    · by_cases heq : i0 + 1 = d0
      · subst heq; simpa using hd
      · exact ih.2.2.1 (by omega)
    · exact ih.2.2.2 lo hlo0 (by omega) (dirEnvOk_step (by omega) hlo hd hok)
  | _ => trivial

lemma directives_last {ts : Toks} {i d : Nat} (h : TG ts .directives i d) :
    isDirective (tok ts d) = false := (dirs_facts h).1

lemma directives_bound {ts : Toks} {i d : Nat} (h : TG ts .directives i d) (hi : i ≤ ts.size) :
    d ≤ ts.size := (dirs_facts h).2.1 hi

/-- The environment at the root node of a document: reset by the first
`%`/`---` token (or already clean), then extended only by this document's `%TAG`s. -/
lemma doc_env {ts : Toks} {i d e : Nat} (hi : 0 < i) (hd : TG ts .directives i d)
    (hds : DocStart ts i d e) (hnd : i < e → NotDirBefore ts i) (hre : i = e → EnvReset ts i) :
    DirEnvOk ts i e := by
  have hle := tg_le hd
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · -- at least one directive: the first resets, the rest extend
    obtain ⟨t, ho⟩ : ∃ t, tok ts i = some t := by
      cases h : tok ts i with
      | none =>
        cases hd with
        | directives_nil hn => omega
        | directives_cons hd' _ => simp [h, isDirective] at hd'
      | some t => exact ⟨t, rfl⟩
    have hd1 : isDirective (tok ts i) = true := by
      cases hd with
      | directives_nil hn => omega
      | directives_cons hd' _ => exact hd'
    have hnd' : NotDirBefore ts i := hnd (by
      rcases hds with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> omega)
    have h1 : DirEnvOk ts i (i + 1) := dirEnvOk_reset hi (Nat.le_refl _) hnd' ho (Or.inr (ho ▸ hd1))
    have hrest : TG ts .directives (i + 1) d := by
      cases hd with
      | directives_nil hn => omega
      | directives_cons _ hr => exact hr
    have h2 : DirEnvOk ts i d := (dirs_facts hrest).2.2.2 i hi (by omega) h1
    rcases hds with ⟨hds, rfl, _⟩ | ⟨_, rfl, _⟩
    · exact dirEnvOk_keep (by omega) (by omega) ((dirs_facts hd).2.2.1 hlt) hds (Or.inl rfl) h2
    · exact h2
  · subst heq
    rcases hds with ⟨hds, rfl, _⟩ | ⟨_, rfl, _⟩
    · exact dirEnvOk_reset hi (Nat.le_refl _) (hnd (by omega)) hds (Or.inl rfl)
    · obtain ⟨ha, hg⟩ := hre rfl
      exact ⟨ha, fun h hm => by rw [hg] at hm; cases hm⟩

/-- `parseDirectives`'s loop body, abstracted: the loop consumes exactly the
directive run and records every `%TAG`. -/
lemma dirLoop {ts : Toks} {s : Sym} {i d : Nat} (h : TG ts s i d) :
    (match s with
      | .directives =>
        ∀ (f : Nat → ParseState × Array Directive → Id (ForInStep (ParseState × Array Directive)))
          (_ : ∀ k ps dirs a b, ps.peek? = some (.versionDirective a b) →
            f k (ps, dirs) = .yield (ps.advance,
              dirs.push (.yaml (toString a ++ toString "." ++ toString b))))
          (_ : ∀ k ps dirs h pre, ps.peek? = some (.tagDirective h pre) →
            f k (ps, dirs) = .yield (ps.advance, dirs.push (.tag h pre)))
          (_ : ∀ k ps dirs, isDirective ps.peek? = false → f k (ps, dirs) = .done (ps, dirs))
          (ps : ParseState) (dirs : Array Directive) (n k : Nat),
          ps.tokens = ts → ps.pos = i → d - i ≤ n →
          ∃ dirs', forIn (List.range' k n) (ps, dirs) f = (({ ps with pos := d } : ParseState), dirs') ∧
            (∀ x, x ∈ dirs → x ∈ dirs') ∧
            ∀ p h pre, i ≤ p → p < d → tok ts p = some (.tagDirective h pre) →
              Directive.tag h pre ∈ dirs'
      | _ => True) := by
  induction h with
  | directives_nil hn =>
    rename_i i0
    intro f _ _ hother ps dirs n k htk hp _
    have hpk : ps.peek? = tok ts i0 := by rw [peek_tok htk, hp]
    refine ⟨dirs, ?_, fun x hx => hx, fun p h pre h1 h2 _ => absurd h2 (by omega)⟩
    subst hp
    cases n with
    | zero => rfl
    | succ n =>
      rw [List.range'_succ, List.forIn_cons, hother k ps dirs (by rw [hpk]; exact hn)]
      rfl
  | directives_cons hd hr ih =>
    rename_i i0 d0
    intro f hver htag hother ps dirs n k htk hp hn
    have hle := tg_le hr
    have hpk : ps.peek? = tok ts i0 := by rw [peek_tok htk, hp]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [List.range'_succ, List.forIn_cons]
    have hadv : ps.advance.pos = i0 + 1 := by simp [ParseState.advance, hp]
    rcases ho : tok ts i0 with _ | t <;> (try cases t) <;> simp [ho, isDirective] at hd
    · -- %YAML
      rename_i a b
      obtain ⟨dirs', hrec, hsub, hmem⟩ := ih f hver htag hother ps.advance
        (dirs.push (.yaml (toString a ++ toString "." ++ toString b))) n' (k + 1) htk hadv (by omega)
      rw [hver k ps dirs a b (hpk.trans ho)]
      refine ⟨dirs', hrec, fun x hx => hsub x (Array.mem_push.2 (Or.inl hx)), ?_⟩
      intro p h pre h1 h2 h3
      rcases Nat.lt_or_eq_of_le h1 with h1 | h1
      · exact hmem p h pre h1 h2 h3
      · subst h1; rw [ho] at h3; cases h3
    · -- %TAG
      rename_i h0 pre0
      obtain ⟨dirs', hrec, hsub, hmem⟩ := ih f hver htag hother ps.advance
        (dirs.push (.tag h0 pre0)) n' (k + 1) htk hadv (by omega)
      rw [htag k ps dirs h0 pre0 (hpk.trans ho)]
      refine ⟨dirs', hrec, fun x hx => hsub x (Array.mem_push.2 (Or.inl hx)), ?_⟩
      intro p h pre h1 h2 h3
      rcases Nat.lt_or_eq_of_le h1 with h1 | h1
      · exact hmem p h pre h1 h2 h3
      · subst h1; rw [ho] at h3; cases h3; exact hsub _ (Array.mem_push.2 (Or.inr rfl))
  | _ => trivial

lemma parseDirectives_ok {ts : Toks} {ps : ParseState} {i d : Nat} (hd : TG ts .directives i d)
    (htk : ps.tokens = ts) (hp : ps.pos = i) (hb : d ≤ ts.size) :
    ∃ dirs : Array Directive, parseDirectives ps = (dirs, ({ ps with pos := d } : ParseState)) ∧
      ∀ p h pre, i ≤ p → p < d → tok ts p = some (.tagDirective h pre) →
        Directive.tag h pre ∈ dirs := by
  have key := dirLoop hd
  simp only [] at key
  obtain ⟨dirs', hloop, _, hmem⟩ := key
    (fun _ (s : ParseState × Array Directive) => match s.1.peek? with
      | some (.versionDirective major minor) =>
        ForInStep.yield (s.1.advance,
          s.2.push (.yaml (toString major ++ toString "." ++ toString minor)))
      | some (.tagDirective handle tagPrefix) =>
        ForInStep.yield (s.1.advance, s.2.push (.tag handle tagPrefix))
      | _ => ForInStep.done (s.1, s.2))
    (by intro k ps dirs a b hpk; simp only [hpk])
    (by intro k ps dirs h pre hpk; simp only [hpk])
    (by
      intro k ps dirs hnd
      rcases ho : ps.peek? with _ | t <;> (try cases t) <;> simp [isDirective, ho] at hnd ⊢)
    ps #[] (ps.tokens.size - ps.pos) 0 htk hp (by rw [htk, hp]; omega)
  refine ⟨dirs', ?_, hmem⟩
  unfold parseDirectives
  simp only [Id.run, bind, pure]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.div_one, Nat.add_sub_cancel, Nat.sub_zero]
  erw [hloop]

/-! ## `prepareDocumentState`, `parseDocument` -/

lemma beq_docStart_false {o : Option YamlToken} (h : o ≠ some .documentStart) :
    (o == some .documentStart) = false := by
  rcases o with _ | t <;> (try cases t) <;> first | rfl | exact absurd rfl h

lemma peekPos_some {ts : Toks} {ps : ParseState} (h : ps.tokens = ts) (hlt : ps.pos < ts.size) :
    ps.peekPos? = some (posAt ts ps.pos) := by
  unfold ParseState.peekPos?
  rw [h]
  simp only [hlt, ↓reduceIte, getBang_pos hlt]

lemma tryConsume_docStart_miss' {ts : Toks} {m : Nat} {ps : ParseState} (htk : ps.tokens = ts)
    (hp : ps.pos = m) (h : tok ts m ≠ some .documentStart) :
    ps.tryConsume .documentStart = (false, ps) := by
  unfold ParseState.tryConsume
  rw [peek_tok htk, hp]
  rcases ho : tok ts m with _ | t <;> (try cases t) <;> first | rfl | exact absurd ho h

lemma tryConsume_docStart_hit' {ts : Toks} {m : Nat} {ps : ParseState} (htk : ps.tokens = ts)
    (hp : ps.pos = m) (h : tok ts m = some .documentStart) :
    ps.tryConsume .documentStart = (true, ps.advance) := by
  unfold ParseState.tryConsume
  rw [peek_tok htk, hp, h]
  rfl

lemma prepare_ok {ts : Toks} {ps : ParseState} {i d e : Nat} (hd : TG ts .directives i d)
    (hds : DocStart ts i d e) (htk : ps.tokens = ts) (hp : ps.pos = i) (hb : d ≤ ts.size)
    (henv : DirEnvOk ts i e) :
    ∃ dirs ps', prepareDocumentState ps = .ok (dirs, ps') ∧ Inv ts ps' e := by
  obtain ⟨dirs, hdirs, hmem⟩ := parseDirectives_ok hd htk hp hb
  have hde : e ≤ d + 1 := by rcases hds with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> omega
  unfold prepareDocumentState
  rw [hdirs]
  simp only [bind, Except.bind, pure, Except.pure]
  generalize hT : Array.filterMap _ dirs = T
  have htags : ∀ h, h ∈ (envAt ts e).tagHandles → T.any (·.1 == h) = true := by
    intro h hm
    obtain ⟨p, pre, h1, h2, h3⟩ := henv.2 h hm
    have h2' : p < d := by
      rcases Nat.lt_or_eq_of_le (show p ≤ d by omega) with h' | h'
      · exact h'
      · subst h'; have := directives_last hd; rw [h3] at this; cases this
    have hin := hmem p h pre h1 h2' h3
    rw [← hT]
    exact Array.any_eq_true'.2 ⟨(h, pre), Array.mem_filterMap.2 ⟨Directive.tag h pre, hin, rfl⟩, by simp⟩
  have hanc : ∀ n, n ∈ (envAt ts e).anchors → False := fun n hn => by
    rw [henv.1] at hn; cases hn
  rcases hds with ⟨hds, rfl, hline⟩ | ⟨hne, rfl, _⟩
  · have hlt : d < ts.size := tok_some_lt hds
    have hpkR : ({ ps with pos := d, tagHandles := T } : ParseState).peek? = tok ts d := by rw [peek_tok (ps := ({ ps with pos := d, tagHandles := T } : ParseState)) htk]
    have hpp : ({ ps with pos := d, tagHandles := T } : ParseState).peekPos? = some (posAt ts d) := peekPos_some htk hlt
    have htc : ({ ps with pos := d, tagHandles := T } : ParseState).tryConsume .documentStart = (true, ({ ps with pos := d, tagHandles := T } : ParseState).advance) :=
      tryConsume_docStart_hit' htk rfl hds
    have hpk2 : ({ ps with pos := d, tagHandles := T } : ParseState).advance.peek? = tok ts (d + 1) := by
      rw [peek_tok (ps := ({ ps with pos := d, tagHandles := T } : ParseState).advance) htk]
      rfl
    have hgd : ({ ps with pos := d, tagHandles := T } : ParseState).advance.peekPos?.getD { offset := 0, line := 0, col := 0 } = posAt ts (d + 1) := by
      rw [peekPos_getD (ps := ({ ps with pos := d, tagHandles := T } : ParseState).advance) htk]
      rfl
    have hinv' : Inv ts ({ ps with pos := d, tagHandles := T } : ParseState).advance (d + 1) :=
      { tokens := htk, pos := rfl, bound := hlt, anchors := fun n hn => (hanc n hn).elim,
        tags := htags }
    rw [hpkR, hds]
    simp only [show (some YamlToken.documentStart == some YamlToken.documentStart) = true from rfl,
      ↓reduceIte, hpp, Option.map, htc, hpk2, hgd]
    rcases ho : tok ts (d + 1) with _ | t <;> (try cases t)
    all_goals first
      | (have hl := hline (by rw [ho]; rfl)
         unfold lineAt at hl
         simp only [beq_eq_false_iff_ne.2 hl, Bool.false_eq_true, ↓reduceIte]
         exact ⟨dirs, _, rfl, hinv'⟩)
      | exact ⟨dirs, _, rfl, hinv'⟩
  · have hR : Inv ts ({ ps with pos := e, tagHandles := T } : ParseState) e :=
      { tokens := htk, pos := rfl, bound := hb, anchors := fun n hn => (hanc n hn).elim,
        tags := htags }
    rw [hR.peek, beq_docStart_false hne, tryConsume_docStart_miss' hR.tokens hR.pos hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨dirs, _, rfl, hR⟩

/-- Document-start precondition: the previous token is not a directive, and either the
environment is clean or this document announces itself with `%`/`---`. -/
def DocPre (ts : Toks) (i : Nat) : Prop :=
  NotDirBefore ts i ∧
    (EnvReset ts i ∨ tok ts i = some .documentStart ∨ isDirective (tok ts i) = true)

lemma parseDocument_ok {ts : Toks} {ps : ParseState} {i m : Nat} (hS : PerTokenOk ts)
    (hdoc : TG ts .document i m) (htk : ps.tokens = ts) (hp : ps.pos = i) (hm : m ≤ ts.size)
    (hi : 0 < i) (hpre : DocPre ts i) :
    ∃ doc ps', parseDocument ps = .ok (doc, ps') ∧ ps'.tokens = ts ∧ ps'.pos = m := by
  cases hdoc with
  | document hd hds hn =>
    rename_i d e
    have hid := tg_le hd
    have hem := tg_le hn
    have hde : d ≤ e := by rcases hds with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> omega
    have hb : d ≤ ts.size := by omega
    have henv : DirEnvOk ts i e := doc_env hi hd hds (fun _ => hpre.1) (fun hie => by
      rcases hpre.2 with h | h | h
      · exact h
      · exfalso
        rcases hds with ⟨_, he, _⟩ | ⟨hne, he⟩
        · omega
        · exact hne (by rw [show d = i by omega]; exact h)
      · exfalso
        cases hd with
        | directives_nil hn' => rw [hn'] at h; cases h
        | directives_cons _ hr => have := tg_le hr; omega)
    obtain ⟨dirs, ps1, hprep, hinv1⟩ := prepare_ok hd hds htk hp hb henv
    unfold parseDocument
    simp only [hprep, bind, Except.bind, pure, Except.pure]
    rw [hinv1.peek]
    rcases ho : tok ts e with _ | t <;> (try cases t)
    all_goals first
      | (have hme := node_empty_of hn (by rw [ho]; rfl)
         subst hme
         exact ⟨_, _, rfl, hinv1.tokens, hinv1.pos⟩)
      | (obtain ⟨v, ps2, hnode, hinv2⟩ := tg_parse hS hn ps1 (4 * ps1.tokens.size + 4) hinv1
           (by simp only [fuelReq]; rw [hinv1.tokens]; omega)
         simp only [hnode]
         exact ⟨_, _, rfl, hinv2.tokens, hinv2.pos⟩)

/-! ## Stream level -/

/-- Loop invariant of `parseStreamLoop` at token `i` in stream state `st`. -/
def SInv (ts : Toks) (ps : ParseState) (i : Nat) (st : StreamState) : Prop :=
  ps.tokens = ts ∧ ps.pos = i ∧ i ≤ ts.size ∧ 0 < i ∧
    match st with
    | .afterDocument =>
      NotDirBefore ts i ∨ (isDirective (tok ts i) = false ∧ tok ts i ≠ some .documentStart)
    | _ => NotDirBefore ts i ∧ EnvReset ts i

lemma envReset_after_docEnd {ts : Toks} {m : Nat} (h : tok ts m = some .documentEnd) :
    EnvReset ts (m + 1) := by
  unfold EnvReset
  rw [envAt_succ]
  unfold perTokenEvents prevDirAt
  rw [h]
  simp [envAfter, stepEnv]

lemma envReset_one {ts : Toks} (h : tok ts 0 = some .streamStart) : EnvReset ts 1 := by
  unfold EnvReset
  rw [envAt_succ, envAt_zero]
  unfold perTokenEvents prevDirAt
  rw [h]
  simp [envAfter]

/-- `parseStreamLoop`'s per-document reset of the anchor and position state. -/
abbrev resetDoc (ps : ParseState) : ParseState :=
  { ps with anchors := #[], anchorIndex := .empty, declaredAnchors := #[],
            declaredIndex := .empty, nodePositions := #[], currentPath := #[] }

lemma tryConsume_docEnd_miss' {ts : Toks} {m : Nat} {ps : ParseState} (htk : ps.tokens = ts)
    (hp : ps.pos = m) (h : tok ts m ≠ some .documentEnd) :
    ps.tryConsume .documentEnd = (false, ps) := by
  unfold ParseState.tryConsume
  rw [peek_tok htk, hp]
  rcases ho : tok ts m with _ | t <;> (try cases t) <;> first | rfl | exact absurd ho h

lemma tryConsume_docEnd_hit' {ts : Toks} {m : Nat} {ps : ParseState} (htk : ps.tokens = ts)
    (hp : ps.pos = m) (h : tok ts m = some .documentEnd) :
    ps.tryConsume .documentEnd = (true, ps.advance) := by
  unfold ParseState.tryConsume
  rw [peek_tok htk, hp, h]
  rfl

lemma afterDoc_valid {t : YamlToken} (h : StreamState.afterDocument.validNextToken t = true) :
    t = .documentStart ∨ isDirective (some t) = true ∨
      (startsNode (some t) = false ∧ isDirective (some t) = false ∧ t ≠ .documentStart) := by
  cases t <;> simp_all [StreamState.validNextToken, isDirective, startsNode]

lemma doc_empty_of {ts : Toks} {i m : Nat} (hdoc : TG ts .document i m)
    (hnd : isDirective (tok ts i) = false) (hns : tok ts i ≠ some .documentStart)
    (hsn : startsNode (tok ts i) = false) : m = i := by
  cases hdoc with
  | document hd hds hn =>
    rename_i d e
    have hdi : d = i := by
      cases hd with
      | directives_nil _ => rfl
      | directives_cons h _ => rw [hnd] at h; cases h
    subst hdi
    rcases hds with ⟨h, _, _⟩ | ⟨_, rfl, _⟩
    · exact absurd h hns
    · exact node_empty_of hn hsn

lemma docPre_of {ts : Toks} {ps : ParseState} {i m : Nat} {st : StreamState} {t : YamlToken}
    (hinv : SInv ts ps i st) (hv : st.validNextToken t = true) (ht : tok ts i = some t)
    (hdoc : TG ts .document i m)
    (hprog : i < m ∨ (tok ts m = some .documentEnd ∧ t ≠ .documentEnd)) : DocPre ts i := by
  obtain ⟨_, _, _, hi, hst⟩ := hinv
  cases st with
  | afterDocument =>
    simp only [] at hst
    rcases afterDoc_valid hv with h | h | ⟨h1, h2, h3⟩
    · subst h
      refine ⟨?_, Or.inr (Or.inl ht)⟩
      rcases hst with hnd | ⟨_, hne⟩
      · exact hnd
      · exact absurd ht hne
    · refine ⟨?_, Or.inr (Or.inr (by rw [ht]; exact h))⟩
      rcases hst with hnd | ⟨hnd, _⟩
      · exact hnd
      · rw [ht, h] at hnd; cases hnd
    · exfalso
      have hm := doc_empty_of hdoc (by rw [ht]; exact h2)
        (by rw [ht]; exact fun e => h3 (Option.some.inj e)) (by rw [ht]; exact h1)
      rcases hprog with hlt | ⟨hend, hne⟩
      · omega
      · subst hm; rw [ht] at hend; exact hne (Option.some.inj hend)
  | initial => exact ⟨hst.1, Or.inl hst.2⟩
  | afterDocumentEnd => exact ⟨hst.1, Or.inl hst.2⟩

lemma doc_after {ts : Toks} {i m : Nat} (hdoc : TG ts .document i m) (hlt : i < m) :
    NotDirBefore ts m ∨ (isDirective (tok ts m) = false ∧ tok ts m ≠ some .documentStart) := by
  cases hdoc with
  | document hd hds hn =>
    rename_i d e
    have hem := tg_le hn
    rcases Nat.lt_or_eq_of_le hem with hlt' | heq
    · exact Or.inl (last_not_directive hn hlt')
    · subst heq
      rcases hds with ⟨hds, rfl, _⟩ | ⟨hne, rfl, _⟩
      · exact Or.inl (notDirBefore_of hds rfl)
      · exact Or.inr ⟨directives_last hd, hne⟩

lemma stream_ok {ts : Toks} {s : Sym} {i j : Nat} (hS : PerTokenOk ts) (h : TG ts s i j) :
    (match s with
      | .stream st => ∀ ps docs fuel, SInv ts ps i st → j - i ≤ fuel → j ≤ ts.size →
          ∃ docs', parseStreamLoop ps docs st fuel = .ok docs'
      | _ => True) := by
  induction h with
  | stream_end he =>
    intro ps docs fuel hinv _ _
    cases fuel with
    | zero => exact ⟨docs, rfl⟩
    | succ f =>
      unfold parseStreamLoop
      rw [peek_tok hinv.1, hinv.2.1]
      rcases he with he | he <;> rw [he] <;> exact ⟨docs, rfl⟩
  | stream_docEnd he hr ih =>
    rename_i st i0 j0
    intro ps docs fuel hinv hf hj
    have hle := tg_le hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    unfold parseStreamLoop
    rw [peek_tok hinv.1, hinv.2.1, he]
    simp only [tryConsume_docEnd_hit' hinv.1 hinv.2.1 he]
    have hlt := tok_some_lt he
    exact ih ps.advance docs f
      ⟨by simp [ParseState.advance, hinv.1], by simp [ParseState.advance, hinv.2.1], by omega,
       by omega, notDirBefore_of he rfl, envReset_after_docEnd he⟩ (by omega) hj
  | stream_doc ht hne1 hne2 hvalid hdoc hlt hnde hr _ ihr =>
    rename_i i0 m0 j0 t st
    intro ps docs fuel hinv hf hj
    have hle := tg_le hr
    have hdm := tg_le hdoc
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hpre : DocPre ts i0 := docPre_of hinv hvalid ht hdoc (Or.inl hlt)
    obtain ⟨doc, ps', hpd, htk', hp'⟩ :=
      parseDocument_ok hS hdoc hinv.1 hinv.2.1 (by omega) hinv.2.2.2.1 hpre
    have hafter := doc_after hdoc hlt
    unfold parseStreamLoop
    rw [peek_tok hinv.1, hinv.2.1, ht]
    cases t
    all_goals first
      | exact absurd rfl hne1
      | exact absurd rfl hne2
      | (simp only [hvalid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpd]
         rw [tryConsume_docEnd_miss' (ps := resetDoc ps') htk' hp' hnde]
         simp only [Bool.false_eq_true, ↓reduceIte]
         split
         · exact ⟨_, rfl⟩
         · refine ihr _ (docs.push doc) f ?_ (by omega) hj
           exact ⟨htk', hp', by omega, by omega, hafter⟩)
  | stream_docTerminated ht hne1 hne2 hvalid hdoc hend hr _ ihr =>
    rename_i i0 m0 j0 t st
    intro ps docs fuel hinv hf hj
    have hle := tg_le hr
    have hdm := tg_le hdoc
    have hlt := tok_some_lt hend
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hpre : DocPre ts i0 := docPre_of hinv hvalid ht hdoc (Or.inr ⟨hend, hne1⟩)
    obtain ⟨doc, ps', hpd, htk', hp'⟩ :=
      parseDocument_ok hS hdoc hinv.1 hinv.2.1 (by omega) hinv.2.2.2.1 hpre
    unfold parseStreamLoop
    rw [peek_tok hinv.1, hinv.2.1, ht]
    cases t
    all_goals first
      | exact absurd rfl hne1
      | exact absurd rfl hne2
      | (simp only [hvalid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpd]
         rw [tryConsume_docEnd_hit' (ps := resetDoc ps') htk' hp' hend]
         simp only [↓reduceIte]
         split
         · exact ⟨_, rfl⟩
         · refine ihr _ (docs.push doc) f ?_ (by omega) hj
           exact ⟨htk', by simp [ParseState.advance, hp'], by omega, by omega,
             notDirBefore_of hend rfl, envReset_after_docEnd hend⟩)
  | _ => trivial

/-! ## The bridge: `TokenStateOk` → `PerTokenOk` on `TokenGrammar` streams -/

/-- Every directive is followed by a directive or `---` (spec [209]); the hypothesis under
which the per-token trace equals `tokenEvents` (7.7 `parse_iff_grammar`, via S5 slice 2). -/
def DirRunsClosed (ts : Toks) : Prop :=
  ∀ q, isDirective (tok ts q) = true →
    isDirective (tok ts (q + 1)) = true ∨ tok ts (q + 1) = some .documentStart

/-- `tok` at an in-range index (7.7 `parse_iff_grammar`, via S5 slice 2). -/
lemma tok_of_lt {ts : Toks} {p : Nat} (hp : p < ts.size) : tok ts p = some ts[p].val := by
  simp [tok, hp]

/-- `TokenEvents.go` from token `p` on, against the per-token trace: with a directive just
before `p`, `go` owes a `beginDocument` and the pending handles; otherwise the traces agree.
7.7 `parse_iff_grammar`, via S5 slice 2 (proof-internal scaffolding). -/
lemma go_drop (ts : Toks) (hC : DirRunsClosed ts) :
    ∀ n p pending, p + n = ts.size →
      (prevDirAt ts p = true →
        go (ts.toList.drop p) pending =
          .beginDocument :: (pending.reverse.map .declareTag ++
            (List.range' p n).flatMap (perTokenEvents ts))) ∧
      (prevDirAt ts p = false → pending = [] →
        go (ts.toList.drop p) pending = (List.range' p n).flatMap (perTokenEvents ts)) := by
  intro n
  induction n with
  | zero =>
    intro p pending hp
    have hd : ts.toList.drop p = [] := List.drop_of_length_le (by simp; omega)
    refine ⟨fun hpd => ?_, fun _ hpend => ?_⟩
    · exfalso
      cases p with
      | zero => simp [prevDirAt] at hpd
      | succ k =>
        have hnone : tok ts (k + 1) = none := tok_none_of_ge (by omega)
        rcases hC k (by simpa [prevDirAt] using hpd) with h | h <;> simp [hnone, isDirective] at h
    · subst hpend; simp [hd, go]
  | succ n ih =>
    intro p pending hp
    have hlt : p < ts.size := by omega
    have hdrop : ts.toList.drop p = ts[p] :: ts.toList.drop (p + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]; simp
    have htok : tok ts p = some ts[p].val := tok_of_lt hlt
    have hprev : prevDirAt ts (p + 1) = isDirective (tok ts p) := rfl
    have hpe : perTokenEvents ts p =
        (let begin : List Event := if prevDirAt ts p then [] else [.beginDocument]
         match some ts[p].val with
         | some (.versionDirective ..) => begin
         | some (.tagDirective h _) => if isNamedHandle h then begin ++ [.declareTag h] else begin
         | some .documentStart => begin
         | some .documentEnd => [.endDocument]
         | some (.anchor n) => [.defineAnchor n]
         | some (.alias n) => [.useAlias n]
         | some (.tag h _) => if h = "" then [] else [.useTag h]
         | _ => []) := by
      unfold perTokenEvents; rw [htok]
    rw [hdrop, List.range'_succ, List.flatMap_cons, hpe]
    have ih' : ∀ pend, _ := fun pend => ih (p + 1) pend (by omega)
    simp only [go]
    generalize hv : ts[p].val = v at htok hpe ⊢
    refine ⟨fun hpd => ?_, fun hpd hpend => ?_⟩
    · -- previous token is a directive: this one is a directive or `---`
      obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by cases p <;> simp [prevDirAt] at hpd ⊢⟩
      have hcl := hC k (by simpa [prevDirAt] using hpd)
      rw [htok] at hcl
      simp only [hpd, ↓reduceIte]
      cases v <;> simp [isDirective] at hcl
      all_goals dsimp only
      case documentStart =>
        have h2 := (ih' []).2
        simp only [prevDirAt, htok, isDirective, true_implies] at h2
        simp [h2]
      case versionDirective =>
        have h1 := (ih' pending).1
        simp only [prevDirAt, htok, isDirective, true_implies] at h1
        simp [tokenEvent, h1]
      case tagDirective h pre =>
        have h1 := (ih' (h :: pending)).1
        have h1' := (ih' pending).1
        simp only [prevDirAt, htok, isDirective, true_implies] at h1 h1'
        by_cases hn : isNamedHandle h = true
        · simp [hn, h1]
        · simp only [Bool.not_eq_true] at hn
          simp [hn, h1']
    · subst hpend
      simp only [hpd, Bool.false_eq_true, ↓reduceIte]
      cases v <;> dsimp only <;> try simp only [tokenEvent]
      case tagDirective h pre =>
        have h1 := (ih' [h]).1
        have h1' := (ih' []).1
        simp only [prevDirAt, htok, isDirective, true_implies] at h1 h1'
        by_cases hn : isNamedHandle h = true
        · simp [hn, h1]
        · simp only [Bool.not_eq_true] at hn
          simp [hn, h1']
      case versionDirective =>
        have h1 := (ih' []).1
        simp only [prevDirAt, htok, isDirective, true_implies] at h1
        simp [h1]
      case tag h sfx =>
        have h2 := (ih' []).2
        simp only [prevDirAt, htok, isDirective, true_implies] at h2
        by_cases he : h = ""
        · subst he; simp [h2]
        · simp [he, String.isEmpty_iff, h2]
      all_goals
        have h2 := (ih' []).2
        simp only [prevDirAt, htok, isDirective, true_implies] at h2
        simp [h2]

/-- The per-token trace IS `tokenEvents` once every directive run is `---`-closed
(7.7 `parse_iff_grammar`, via S5 slice 2). -/
lemma perTokenTrace_eq_tokenEvents (ts : Toks) (hC : DirRunsClosed ts) :
    perTokenTrace ts = tokenEvents ts := by
  unfold perTokenTrace tokenEvents
  have := (go_drop ts hC ts.size 0 [] (by simp)).2 (by simp [prevDirAt]) rfl
  simpa [List.range_eq_range'] using this.symm

/-- No directive and no `---` inside `[i, j)` (7.7 `parse_iff_grammar`, via S5 slice 2). -/
def NoDir (ts : Toks) (i j : Nat) : Prop :=
  ∀ q, i ≤ q → q < j → isDirective (tok ts q) = false ∧ tok ts q ≠ some .documentStart

/-- Every directive inside `[i, j)` is followed by a directive or `---`
(7.7 `parse_iff_grammar`, via S5 slice 2). -/
def Closed (ts : Toks) (i j : Nat) : Prop :=
  ∀ q, i ≤ q → q < j → isDirective (tok ts q) = true →
    isDirective (tok ts (q + 1)) = true ∨ tok ts (q + 1) = some .documentStart

/-- A known non-directive, non-`---` token closes a `NoDir` position
(7.7 `parse_iff_grammar`, via S5 slice 2). -/
lemma nd_of_tok {ts : Toks} {q : Nat} {t : YamlToken} (h : tok ts q = some t)
    (hd : isDirective (some t) = false) (hs : t ≠ .documentStart) :
    isDirective (tok ts q) = false ∧ tok ts q ≠ some .documentStart := by
  rw [h]; exact ⟨hd, by intro e; exact hs (Option.some.inj e)⟩

/-- Close a `NoDir` goal at a position whose token is known (`tok ts _ = some _` in context). -/
macro "ndt" : tactic => `(tactic| (first
  | exact nd_of_tok ‹tok _ _ = some (.scalar _ _)› (by simp [isDirective]) (by simp)
  | exact nd_of_tok ‹tok _ _ = some (.alias _)› (by simp [isDirective]) (by simp)
  | exact nd_of_tok ‹tok _ _ = some (.anchor _)› (by simp [isDirective]) (by simp)
  | exact nd_of_tok ‹tok _ _ = some (.tag _ _)› (by simp [isDirective]) (by simp)
  | exact nd_of_tok ‹tok _ _ = some .blockEntry› (by simp [isDirective]) (by simp)
  | exact nd_of_tok ‹tok _ _ = some .blockSequenceStart› (by simp [isDirective]) (by simp)
  | exact nd_of_tok ‹tok _ _ = some .blockMappingStart› (by simp [isDirective]) (by simp)
  | exact nd_of_tok ‹tok _ _ = some .blockEnd› (by simp [isDirective]) (by simp)
  | exact nd_of_tok ‹tok _ _ = some .key› (by simp [isDirective]) (by simp)
  | exact nd_of_tok ‹tok _ _ = some .value› (by simp [isDirective]) (by simp)
  | exact nd_of_tok ‹tok _ _ = some .flowEntry› (by simp [isDirective]) (by simp)
  | exact nd_of_tok ‹tok _ _ = some .flowSequenceStart› (by simp [isDirective]) (by simp)
  | exact nd_of_tok ‹tok _ _ = some .flowSequenceEnd› (by simp [isDirective]) (by simp)
  | exact nd_of_tok ‹tok _ _ = some .flowMappingStart› (by simp [isDirective]) (by simp)
  | exact nd_of_tok ‹tok _ _ = some .flowMappingEnd› (by simp [isDirective]) (by simp)))

/-- Directive tokens live only in `.directives` spans, each closed by `---` (spec [209];
7.7 `parse_iff_grammar`, via S5 slice 2). -/
lemma tg_closed {ts : Toks} {s : Sym} {i j : Nat} (h : TG ts s i j) :
    (match s with
      | .directives => ∀ q, i ≤ q → q < j → isDirective (tok ts q) = true
      | .document | .stream _ => Closed ts i j
      | _ => NoDir ts i j) := by
  induction h with
  | stream_end _ => intro q h1 h2; omega
  | stream_docEnd hd _ ih =>
    intro q h1 h2 hq
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · simp [hd, isDirective] at hq
    · exact ih q h1' h2 hq
  | stream_doc _ _ _ _ _ _ _ _ ih1 ih2 =>
    intro q h1 h2 hq
    exact (Nat.lt_or_ge q _).elim (fun h => ih1 q h1 h hq) (fun h => ih2 q h h2 hq)
  | stream_docTerminated _ _ _ _ _ hm _ ih1 ih2 =>
    intro q h1 h2 hq
    rcases Nat.lt_or_ge q _ with h | h
    · exact ih1 q h1 h hq
    · rcases Nat.eq_or_lt_of_le h with rfl | h'
      · simp [hm, isDirective] at hq
      · exact ih2 q h' h2 hq
  | document hd hds hn ihd ihn =>
    rename_i i d e m
    intro q h1 h2 hq
    rcases hds with ⟨hds, rfl, _⟩ | ⟨hne, rfl, rfl⟩
    · -- directives `[i, d)`, `---` at `d`, node after
      rcases Nat.lt_or_ge q d with h | h
      · rcases Nat.lt_or_ge (q + 1) d with h' | h'
        · exact Or.inl (ihd (q + 1) (by omega) h')
        · exact Or.inr (by simpa [show q + 1 = d by omega] using hds)
      · rcases Nat.eq_or_lt_of_le h with h' | h'
        · rw [h'] at hds; simp [hds, isDirective] at hq
        · exact absurd hq (by simpa using (ihn q h' h2).1)
    · -- no directives (`i = d`), node from `i`
      exact absurd hq (by simpa using (ihn q h1 h2).1)
  | directives_nil _ => intro q h1 h2; omega
  | directives_cons hd _ ih =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · exact hd
    · exact ih q h1' h2
  | node_alias ht => intro q h1 h2; rcases Nat.eq_or_lt_of_le h1 with rfl | h <;> first | ndt | omega
  | node _ _ _ ihp ihc =>
    intro q h1 h2
    exact (Nat.lt_or_ge q _).elim (fun h => ihp q h1 h) (fun h => ihc q h h2)
  | props_none _ => intro q h1 h2; omega
  | props_anchor ht _ => intro q h1 h2; rcases Nat.eq_or_lt_of_le h1 with rfl | h <;> first | ndt | omega
  | props_tag ht _ => intro q h1 h2; rcases Nat.eq_or_lt_of_le h1 with rfl | h <;> first | ndt | omega
  | props_anchorTag ht ht' =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · ndt
    · rcases Nat.eq_or_lt_of_le h with rfl | h' <;> first | ndt | omega
  | props_tagAnchor ht ht' =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · ndt
    · rcases Nat.eq_or_lt_of_le h with rfl | h' <;> first | ndt | omega
  | content_scalar ht => intro q h1 h2; rcases Nat.eq_or_lt_of_le h1 with rfl | h <;> first | ndt | omega
  | content_blockSeq _ ih => exact ih
  | content_blockMap _ ih => exact ih
  | content_seqEntryEmpty _ => intro q h1 h2; omega
  | content_implicitSeq _ _ ih => exact ih
  | content_flowSeq _ ih => exact ih
  | content_flowMap _ ih => exact ih
  | content_empty _ => intro q h1 h2; omega
  | blockSeq ht _ hk ih =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · ndt
    · rcases Nat.lt_or_ge q _ with h' | h'
      · exact ih q h h'
      · rcases Nat.eq_or_lt_of_le h' with rfl | h'' <;> first | ndt | omega
  | seqEntries_nil _ => intro q h1 h2; omega
  | seqEntries_cons ht _ _ ih1 ih2 =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · ndt
    · exact (Nat.lt_or_ge q _).elim (fun h' => ih1 q h h') (fun h' => ih2 q h' h2)
  | blockMap ht _ hk ih =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · ndt
    · rcases Nat.lt_or_ge q _ with h' | h'
      · exact ih q h h'
      · rcases Nat.eq_or_lt_of_le h' with rfl | h'' <;> first | ndt | omega
  | mapEntries_nil _ _ => intro q h1 h2; omega
  | mapEntries_key ht _ _ ih1 ih2 =>
    intro q h1 h2
    exact (Nat.lt_or_ge q _).elim (fun h => ih1 q h1 h) (fun h => ih2 q h h2)
  | mapEntries_value ht _ _ ih1 ih2 =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · ndt
    · exact (Nat.lt_or_ge q _).elim (fun h' => ih1 q h h') (fun h' => ih2 q h' h2)
  | keyEntry ht _ _ ih1 ih2 =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · ndt
    · exact (Nat.lt_or_ge q _).elim (fun h' => ih1 q h h') (fun h' => ih2 q h' h2)
  | entryValue_value ht _ _ _ ih =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · ndt
    · exact ih q h h2
  | entryValue_retro ht ht' _ ih =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · ndt
    · rcases Nat.eq_or_lt_of_le h with h' | h'
      · rw [← h']; ndt
      · exact ih q h' h2
  | entryValue_none _ _ => intro q h1 h2; omega
  | flowSeq ht _ hk ih =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · ndt
    · rcases Nat.lt_or_ge q _ with h' | h'
      · exact ih q h h'
      · rcases Nat.eq_or_lt_of_le h' with rfl | h'' <;> first | ndt | omega
  | flowSeqItems_end _ => intro q h1 h2; omega
  | flowSeqItems_trailing ht ht' =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · ndt
    · omega
  | flowSeqItems_pair _ hsep hq _ _ ih1 ih2 =>
    intro q h1 h2
    rcases hsep with ⟨rfl, rfl⟩ | ⟨rfl, hfe, rfl⟩
    · exact (Nat.lt_or_ge q _).elim (fun h => ih1 q h1 h) (fun h => ih2 q h h2)
    · rcases Nat.eq_or_lt_of_le h1 with rfl | h
      · ndt
      · exact (Nat.lt_or_ge q _).elim (fun h' => ih1 q h h') (fun h' => ih2 q h' h2)
  | flowSeqItems_node _ hsep _ _ _ _ ih1 ih2 =>
    intro q h1 h2
    rcases hsep with ⟨rfl, rfl⟩ | ⟨rfl, hfe, rfl⟩
    · exact (Nat.lt_or_ge q _).elim (fun h => ih1 q h1 h) (fun h => ih2 q h h2)
    · rcases Nat.eq_or_lt_of_le h1 with rfl | h
      · ndt
      · exact (Nat.lt_or_ge q _).elim (fun h' => ih1 q h h') (fun h' => ih2 q h' h2)
  | singlePair_value ht _ hv _ ih1 ih2 =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · ndt
    · rcases Nat.lt_or_ge q _ with h' | h'
      · exact ih1 q h h'
      · rcases Nat.eq_or_lt_of_le h' with h'' | h''
        · rw [← h'']; ndt
        · exact ih2 q h'' h2
  | singlePair_noValue ht _ _ ih =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · ndt
    · exact ih q h h2
  | flowMap ht _ hk ih =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · ndt
    · rcases Nat.lt_or_ge q _ with h' | h'
      · exact ih q h h'
      · rcases Nat.eq_or_lt_of_le h' with rfl | h'' <;> first | ndt | omega
  | flowMapEntries_end _ => intro q h1 h2; omega
  | flowMapEntries_trailing ht ht' =>
    intro q h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · ndt
    · omega
  | flowMapEntries_explicit _ hsep hq _ _ _ ih1 ih2 ih3 =>
    intro q h1 h2
    rcases hsep with ⟨rfl, rfl⟩ | ⟨rfl, hfe, rfl⟩
    · rcases Nat.eq_or_lt_of_le h1 with rfl | h
      · ndt
      · rcases Nat.lt_or_ge q _ with h' | h'
        · exact ih1 q h h'
        · exact (Nat.lt_or_ge q _).elim (fun h'' => ih2 q h' h'') (fun h'' => ih3 q h'' h2)
    · rcases Nat.eq_or_lt_of_le h1 with rfl | h
      · ndt
      · rcases Nat.eq_or_lt_of_le h with h' | h'
        · rw [← h']; ndt
        · rcases Nat.lt_or_ge q _ with h'' | h''
          · exact ih1 q h' h''
          · exact (Nat.lt_or_ge q _).elim (fun h3 => ih2 q h'' h3) (fun h3 => ih3 q h3 h2)
  | flowMapEntries_implicit _ hsep _ _ _ _ _ ih1 ih2 ih3 =>
    intro q h1 h2
    rcases hsep with ⟨rfl, rfl⟩ | ⟨rfl, hfe, rfl⟩
    · rcases Nat.lt_or_ge q _ with h | h
      · exact ih1 q h1 h
      · exact (Nat.lt_or_ge q _).elim (fun h' => ih2 q h h') (fun h' => ih3 q h' h2)
    · rcases Nat.eq_or_lt_of_le h1 with rfl | h
      · ndt
      · rcases Nat.lt_or_ge q _ with h' | h'
        · exact ih1 q h h'
        · exact (Nat.lt_or_ge q _).elim (fun h'' => ih2 q h' h'') (fun h'' => ih3 q h'' h2)
  | flowMapValue_value hk hv _ ih =>
    intro q h1 h2
    rcases hk with ⟨hk, rfl⟩ | ⟨hk, rfl⟩
    · rcases Nat.eq_or_lt_of_le h1 with rfl | h
      · ndt
      · rcases Nat.eq_or_lt_of_le h with h' | h'
        · rw [← h']; ndt
        · exact ih q h' h2
    · rcases Nat.eq_or_lt_of_le h1 with rfl | h
      · ndt
      · exact ih q h h2
  | flowMapValue_none hk _ =>
    intro q h1 h2
    rcases hk with ⟨hk, rfl⟩ | ⟨hk, rfl⟩
    · rcases Nat.eq_or_lt_of_le h1 with rfl | h <;> first | ndt | omega
    · omega

/-- A `.stream` span ends on a non-directive token (`streamEnd` or past the end;
7.7 `parse_iff_grammar`, via S5 slice 2). -/
lemma tg_stream_last {ts : Toks} {s : Sym} {i j : Nat} (h : TG ts s i j) :
    (match s with | .stream _ => isDirective (tok ts j) = false | _ => True) := by
  induction h with
  | stream_end h => rcases h with h | h <;> simp [h, isDirective]
  | stream_docEnd _ _ ih => exact ih
  | stream_doc _ _ _ _ _ _ _ _ _ ih => exact ih
  | stream_docTerminated _ _ _ _ _ _ _ _ ih => exact ih
  | _ => trivial

/-- `TokenGrammar` streams close every directive run with `---` (spec [209];
7.7 `parse_iff_grammar`, via S5 slice 2). -/
lemma tokenGrammar_directivesClosed {ts : Toks} (hG : TokenGrammar ts) : DirRunsClosed ts := by
  obtain ⟨h0, j, hs, hj⟩ := hG
  intro q hq
  have hc : Closed ts 1 j := tg_closed hs
  have hl : isDirective (tok ts j) = false := tg_stream_last hs
  cases q with
  | zero => simp [h0, isDirective] at hq
  | succ k =>
    rcases Nat.lt_or_ge (k + 1) j with h | h
    · exact hc (k + 1) (by omega) h hq
    · rcases Nat.eq_or_lt_of_le h with h' | h'
      · rw [h'] at hl; simp [hl] at hq
      · rw [tok_none_of_ge (by omega)] at hq; simp [isDirective] at hq

/-- THE bridge from the public state premise to the proof-internal one: on a `TokenGrammar`
stream the per-token trace is `tokenEvents`, so `TokenStateOk` is `PerTokenOk`
(EVENTSOF-CONCEPT §9 S5 slice 2; 7.7 `parse_iff_grammar`). -/
lemma perTokenOk_of_tokenStateOk {ts : Toks} (hG : TokenGrammar ts) (h : TokenStateOk ts) :
    PerTokenOk ts := by
  unfold PerTokenOk
  rw [perTokenTrace_eq_tokenEvents ts (tokenGrammar_directivesClosed hG)]
  exact h

/-- **Stream D, parser half of the converse**: a token array of the right shape
(`TokenGrammar`) under the right per-document state (`TokenStateOk`) is accepted by
`parseStream`. -/
public lemma parseStream_accepts (ts : Array (Positioned YamlToken))
    (h_shape : TokenGrammar ts) (h_state : TokenStateOk ts) :
    ∃ docs, parseStream ts = .ok docs := by
  have h_state := perTokenOk_of_tokenStateOk h_shape h_state
  obtain ⟨h0, j, hstream, hj⟩ := h_shape
  unfold parseStream
  simp only [bind, Except.bind, pure, Except.pure]
  unfold ParseState.expect
  rw [peek_tok (ts := ts) rfl]
  simp only []
  rw [h0]
  simp only [show (BEq.beq YamlToken.streamStart YamlToken.streamStart) = true from rfl,
    ↓reduceIte]
  have hnd : NotDirBefore ts 1 := by unfold NotDirBefore; simp [h0, isDirective]
  exact stream_ok h_state hstream _ #[] ts.size
    ⟨rfl, rfl, by omega, by omega, hnd, envReset_one h0⟩ (by omega) (by omega)

end L4YAML.Proofs.TokenGrammar
