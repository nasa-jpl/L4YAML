/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Serialization.SerializationWellFormed
public import L4YAML.Proofs.Serialization.TokenEvents
import all Init.Data.Range.Basic
import all L4YAML.Proofs.Serialization.TokenEvents

/-!
# S5(→): the parser's anchor/tag guards compose to `checkFrom`

Capstone chain: 7.7 `parse_iff_grammar`, serialization half, via S5 of
`EVENTSOF-CONCEPT.md` §9.  The single-guard bridges
(`parser_alias_guard_exact`, `parser_tag_guard_exact`) say what ONE guard
checks at ONE token; this module composes them over a whole `parseStream` run.

The checker is first restated as a state machine over tokens (`stepTok`,
`runToks`), shown equal to `checkFrom env (TokenEvents.go l pending)`.  The
parser-side invariant `Rel` is an ORDER, not an equivalence: the parser
declares only the surviving anchor of a node (`declareAnchorOpt props.anchor`)
and registers every `%TAG` handle, so its tables sit below (anchors) and above
(handles) the `Env` the checker folds — which is exactly what the forward
direction needs.

Two token-shape facts the scanner guarantees but the parser does not re-check
are premises here (both have token-level counterexamples, pinned in
`Tests/AdversarialInstantiation.lean`, Priority 50): `TagUsesShaped` (a used
handle is builtin or `!word!`) and `DirectivesClosed` (a directive run ends in
`---`).  The run may also stop before the last token — at `...`-less
`streamEnd` or where `parseDocument` consumes nothing — so the conclusion is
stated on the consumed prefix.
-/

@[expose] public section Blanket

namespace L4YAML.Proofs.Serialization.ParseCheckFrom

open L4YAML L4YAML.TokenParser
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents

abbrev Toks := Array (Positioned YamlToken)

/-- The token at index `i`, as `TokenGrammar.tok` reads it. -/
def tok (ts : Toks) (i : Nat) : Option YamlToken := (ts[i]?).map Positioned.val

/-! ## The checker as a state machine over tokens -/

/-- Checker state: the `Env` folded so far and the named `%TAG` handles pending
until the next `---` (`TokenEvents.go`'s accumulator). -/
abbrev CS := Env × List String

def declareAll (env : Env) : List String → Env
  | [] => env
  | h :: hs => declareAll { env with tagHandles := h :: env.tagHandles } hs

/-- One token's effect on the checker state; `none` is a failed guard. -/
def stepTok (s : CS) : YamlToken → Option CS
  | .tagDirective h _ => some (if isNamedHandle h then (s.1, h :: s.2) else s)
  | .documentStart => some (declareAll s.1.reset s.2.reverse, [])
  | .documentEnd => some (s.1.reset, s.2)
  | .anchor n => some ({ s.1 with anchors := n :: s.1.anchors }, s.2)
  | .alias n => if AliasAllowed s.1 n then some s else none
  | .tag h _ => if h = "" then some s else if TagHandleAllowed s.1 h then some s else none
  | _ => some s

def runToks : List (Positioned YamlToken) → CS → Option CS
  | [], s => some s
  | t :: ts, s => (stepTok s t.val).bind (runToks ts)

lemma runToks_append (l₁ l₂ : List (Positioned YamlToken)) (s : CS) :
    runToks (l₁ ++ l₂) s = (runToks l₁ s).bind (runToks l₂) := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons t l ih =>
    simp only [List.cons_append, runToks]
    cases stepTok s t.val <;> simp [ih]

lemma checkFrom_declareTags (env : Env) (hs : List String) (rest : List Event) :
    checkFrom env (hs.map .declareTag ++ rest) = checkFrom (declareAll env hs) rest := by
  induction hs generalizing env with
  | nil => rfl
  | cons h hs ih => simp only [List.map_cons, List.cons_append, checkFrom, declareAll, ih]

/-- `checkFrom` over the token trace IS the state machine: capstone 7.7 via S5. -/
lemma checkFrom_go_iff (l : List (Positioned YamlToken)) (env : Env) (pending : List String) :
    checkFrom env (go l pending) = true ↔ (runToks l (env, pending)).isSome = true := by
  induction l generalizing env pending with
  | nil =>
    simp only [go, runToks, Option.isSome_some, iff_true]
    rw [← List.append_nil (pending.reverse.map _), checkFrom_declareTags]; rfl
  | cons t l ih =>
    obtain ⟨_, v, _⟩ := t
    cases v
    case tagDirective h p =>
      simp only [go, runToks, stepTok]
      split <;> simp [ih]
    case documentStart =>
      simp only [go, runToks, stepTok, checkFrom, checkFrom_declareTags, Option.bind_some]
      exact ih _ _
    case documentEnd => simpa [go, tokenEvent, runToks, stepTok, checkFrom] using ih env.reset pending
    case anchor n => simpa [go, tokenEvent, runToks, stepTok, checkFrom] using ih _ pending
    case alias n =>
      simp only [go, tokenEvent, runToks, stepTok, checkFrom]
      split <;> simp [ih]
    case tag h suf =>
      simp only [go, tokenEvent, runToks, stepTok]
      by_cases hh : h = ""
      · subst hh; simp [ih]
      · simp only [hh, String.isEmpty_iff, ↓reduceIte, checkFrom]
        split <;> simp [ih]
    all_goals simpa [go, tokenEvent, runToks, stepTok] using ih env pending

/-! ## Token segments -/

/-- The tokens the parser consumed between positions `i` and `j`. -/
def seg (ts : Toks) (i j : Nat) : List (Positioned YamlToken) := (ts.toList.drop i).take (j - i)

@[simp] lemma seg_self (ts : Toks) (i : Nat) : seg ts i i = [] := by simp [seg]

lemma seg_append (ts : Toks) {i j k : Nat} (h₁ : i ≤ j) (h₂ : j ≤ k) :
    seg ts i k = seg ts i j ++ seg ts j k := by
  unfold seg
  rw [show k - i = (j - i) + (k - j) by omega, List.take_add, List.drop_drop,
    show i + (j - i) = j by omega]

lemma seg_one (ts : Toks) {i : Nat} {p : Positioned YamlToken} (h : ts[i]? = some p) :
    seg ts i (i + 1) = [p] := by
  unfold seg
  have hi : i < ts.toList.length := by
    rw [Array.length_toList]; exact (Array.getElem?_eq_some_iff.mp h).1
  rw [List.drop_eq_getElem_cons hi, Nat.add_sub_cancel_left, List.take_succ_cons, List.take_zero]
  simp only [List.cons.injEq, and_true]
  have := Array.getElem?_eq_some_iff.mp h
  obtain ⟨hlt, rfl⟩ := this
  simp

lemma seg_zero_eq (ts : Toks) (k : Nat) : seg ts 0 k = (ts.extract 0 k).toList := by
  simp [seg]

lemma peek_eq_tok (ps : ParseState) : ps.peek? = tok ps.tokens ps.pos := by
  unfold ParseState.peek? tok
  split
  · rename_i h; simp [Array.getElem?_eq_getElem h, getElem!_pos ps.tokens ps.pos h]
  · rename_i h
    have hn : ps.tokens[ps.pos]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt h)
    simp [hn]

lemma peek_some {ps : ParseState} {t : YamlToken} (h : ps.peek? = some t) :
    ∃ p, ps.tokens[ps.pos]? = some p ∧ p.val = t := by
  rw [peek_eq_tok] at h
  unfold tok at h
  cases hp : ps.tokens[ps.pos]? with
  | none => simp [hp] at h
  | some p => simp only [hp, Option.map_some, Option.some.injEq] at h; exact ⟨p, rfl, h⟩

lemma pos_lt_of_peek {ps : ParseState} {t : YamlToken} (h : ps.peek? = some t) :
    ps.pos < ps.tokens.size := by
  obtain ⟨p, hp, -⟩ := peek_some h
  exact (Array.getElem?_eq_some_iff.mp hp).1

lemma mem_of_getElem? {ts : Toks} {i : Nat} {p : Positioned YamlToken} (h : ts[i]? = some p) :
    p ∈ ts := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp h
  exact Array.getElem_mem hlt


/-! ## The parser-side order -/

/-- Scanner fact A, as a token predicate: a used handle is builtin or `!word!`
(`Scanner/NodeProperties.lean`'s `scanTag` emits nothing else). -/
def TagUsesShaped (ts : Toks) : Prop :=
  ∀ p ∈ ts, ∀ h suf, p.val = .tag h suf → BuiltinTagHandle h ∨ isNamedHandle h = true

def isDirectiveTok : Option YamlToken → Bool
  | some (.versionDirective ..) | some (.tagDirective ..) => true
  | _ => false

/-- Scanner fact D, as a token predicate: a directive run ends in `---`
(the scanner's `directiveWithoutDocument`). -/
def DirectivesClosed (ts : Toks) : Prop :=
  ∀ i, isDirectiveTok (tok ts i) = true →
    isDirectiveTok (tok ts (i + 1)) = true ∨ tok ts (i + 1) = some .documentStart

/-- The parser's tables sit below the checker's `Env`: every declared anchor is
in `env.anchors`, every NAMED registered handle is in `env.tagHandles`. -/
def Rel (ps : ParseState) (s : CS) : Prop :=
  (∀ n, n ∈ ps.declaredAnchors → n ∈ s.1.anchors) ∧
  (∀ h, isNamedHandle h = true → (∃ p ∈ ps.tagHandles, p.1 = h) → h ∈ s.1.tagHandles)

lemma Rel.of_eq {ps ps' : ParseState} {s : CS} (h : Rel ps s)
    (hd : ps'.declaredAnchors = ps.declaredAnchors) (ht : ps'.tagHandles = ps.tagHandles) :
    Rel ps' s :=
  ⟨fun n hn => h.1 n (hd ▸ hn), fun hh hn hp => h.2 hh hn (ht ▸ hp)⟩

lemma Rel.mono {ps : ParseState} {s s' : CS} (h : Rel ps s)
    (ha : ∀ n, n ∈ s.1.anchors → n ∈ s'.1.anchors)
    (ht : ∀ n, n ∈ s.1.tagHandles → n ∈ s'.1.tagHandles) : Rel ps s' :=
  ⟨fun n hn => ha n (h.1 n hn), fun hh hn hp => ht hh (h.2 hh hn hp)⟩

/-- `CF ps ps'`: the segment a call consumed passes the checker from any state
its entry sits below, and its exit sits below the result. -/
def CF (ps ps' : ParseState) : Prop :=
  ps'.tokens = ps.tokens ∧ ps.pos ≤ ps'.pos ∧ ps'.tagHandles = ps.tagHandles ∧
  (ps.pos ≤ ps.tokens.size → ps'.pos ≤ ps.tokens.size) ∧
  (TagUsesShaped ps.tokens → ∀ s, Rel ps s →
    ∃ s', runToks (seg ps.tokens ps.pos ps'.pos) s = some s' ∧ Rel ps' s')

lemma CF.refl (ps : ParseState) : CF ps ps :=
  ⟨rfl, Nat.le_refl _, rfl, id, fun _ s hs => ⟨s, by simp [runToks], hs⟩⟩

lemma CF.of_eq {ps ps' : ParseState} (h1 : ps'.tokens = ps.tokens) (h2 : ps'.pos = ps.pos)
    (h3 : ps'.declaredAnchors = ps.declaredAnchors) (h4 : ps'.tagHandles = ps.tagHandles) :
    CF ps ps' :=
  ⟨h1, h2 ▸ Nat.le_refl _, h4, fun h => h2 ▸ h,
   fun _ s hs => ⟨s, by rw [h2]; simp [runToks], hs.of_eq h3 h4⟩⟩

lemma CF.trans {ps1 ps2 ps3 : ParseState} (h12 : CF ps1 ps2) (h23 : CF ps2 ps3) : CF ps1 ps3 := by
  obtain ⟨t12, p12, g12, z12, r12⟩ := h12
  obtain ⟨t23, p23, g23, z23, r23⟩ := h23
  refine ⟨t23.trans t12, Nat.le_trans p12 p23, g23.trans g12, fun h => ?_, fun hsh s hs => ?_⟩
  · have := z23 (by rw [t12]; exact z12 h); rwa [t12] at this
  · obtain ⟨s2, hr2, hs2⟩ := r12 hsh s hs
    obtain ⟨s3, hr3, hs3⟩ := r23 (by rw [t12]; exact hsh) s2 hs2
    refine ⟨s3, ?_, hs3⟩
    rw [seg_append ps1.tokens p12 p23, runToks_append, hr2, Option.bind_some]
    rw [t12] at hr3; exact hr3

/-- Tokens the checker ignores. -/
def neutralTok : YamlToken → Bool
  | .tagDirective .. | .documentStart | .documentEnd | .anchor _ | .alias _ | .tag .. => false
  | _ => true

lemma stepTok_neutral {t : YamlToken} (h : neutralTok t = true) (s : CS) : stepTok s t = some s := by
  cases t <;> simp_all [neutralTok, stepTok]

lemma CF.advance_neutral {ps : ParseState} {t : YamlToken} (h : ps.peek? = some t)
    (hn : neutralTok t = true) : CF ps ps.advance := by
  obtain ⟨p, hp, hv⟩ := peek_some h
  have hlt := pos_lt_of_peek h
  refine ⟨rfl, by simp [ParseState.advance], rfl, fun _ => by simp [ParseState.advance]; omega,
    fun _ s hs => ⟨s, ?_, hs.of_eq rfl rfl⟩⟩
  simp only [ParseState.advance]
  rw [seg_one ps.tokens hp]; simp [runToks, hv, stepTok_neutral hn]

lemma CF.tryConsume {ps : ParseState} {t : YamlToken} (hn : neutralTok t = true) :
    CF ps (ps.tryConsume t).2 := by
  unfold ParseState.tryConsume
  split
  · rename_i t' h
    split
    · rename_i hb
      have : t' = t := eq_of_beq hb
      subst this; exact CF.advance_neutral h hn
    · exact CF.refl ps
  · exact CF.refl ps

/-- The alias guard, composed: `parser_alias_guard_exact` at the token the
parser is looking at. -/
lemma CF.alias {ps : ParseState} {n : String} (h : ps.peek? = some (.alias n))
    (hg : ps.declaredIndex.contains n = true) : CF ps ps.advance := by
  obtain ⟨p, hp, hv⟩ := peek_some h
  have hlt := pos_lt_of_peek h
  refine ⟨rfl, by simp [ParseState.advance], rfl, fun _ => by simp [ParseState.advance]; omega,
    fun _ s hs => ⟨s, ?_, hs.of_eq rfl rfl⟩⟩
  simp only [ParseState.advance]
  rw [seg_one ps.tokens hp]
  have hmem : n ∈ s.1.anchors := hs.1 n ((DeclaredIndex.contains_iff _ _).mp hg)
  simp [runToks, hv, stepTok, AliasAllowed, hmem]

/-! ## The properties stage: anchors are promised, then declared -/

/-- `CF` for a segment that only grows the checker's state and declares
nothing yet, remembering the anchor names it consumed. -/
def CFA (ps ps' : ParseState) (names : List String) : Prop :=
  ps'.tokens = ps.tokens ∧ ps.pos ≤ ps'.pos ∧ ps'.tagHandles = ps.tagHandles ∧
  ps'.declaredAnchors = ps.declaredAnchors ∧
  (ps.pos ≤ ps.tokens.size → ps'.pos ≤ ps.tokens.size) ∧
  (TagUsesShaped ps.tokens → ∀ s, Rel ps s →
    ∃ s' : CS, runToks (seg ps.tokens ps.pos ps'.pos) s = some s' ∧
      (∀ n, n ∈ s.1.anchors → n ∈ s'.1.anchors) ∧
      (∀ h, h ∈ s.1.tagHandles → h ∈ s'.1.tagHandles) ∧
      (∀ n, n ∈ names → n ∈ s'.1.anchors))

lemma CFA.refl (ps : ParseState) : CFA ps ps [] :=
  ⟨rfl, Nat.le_refl _, rfl, rfl, id,
   fun _ s _ => ⟨s, by simp [runToks], fun _ h => h, fun _ h => h, fun _ h => by simp at h⟩⟩

lemma CFA.trans {ps1 ps2 ps3 : ParseState} {l1 l2 : List String}
    (h12 : CFA ps1 ps2 l1) (h23 : CFA ps2 ps3 l2) : CFA ps1 ps3 (l1 ++ l2) := by
  obtain ⟨t12, p12, g12, d12, z12, r12⟩ := h12
  obtain ⟨t23, p23, g23, d23, z23, r23⟩ := h23
  refine ⟨t23.trans t12, Nat.le_trans p12 p23, g23.trans g12, d23.trans d12, fun h => ?_,
    fun hsh s hs => ?_⟩
  · have := z23 (by rw [t12]; exact z12 h); rwa [t12] at this
  · obtain ⟨s2, hr2, a2, h2, n2⟩ := r12 hsh s hs
    have hs2 : Rel ps2 s2 := (hs.of_eq d12 g12).mono a2 h2
    obtain ⟨s3, hr3, a3, h3, n3⟩ := r23 (by rw [t12]; exact hsh) s2 hs2
    refine ⟨s3, ?_, fun n hn => a3 n (a2 n hn), fun n hn => h3 n (h2 n hn), fun n hn => ?_⟩
    · rw [seg_append ps1.tokens p12 p23, runToks_append, hr2, Option.bind_some]
      rw [t12] at hr3; exact hr3
    · rcases List.mem_append.mp hn with hn | hn
      · exact a3 n (n2 n hn)
      · exact n3 n hn

lemma CFA.anchor {ps : ParseState} {n : String} (h : ps.peek? = some (.anchor n)) :
    CFA ps ps.advance [n] := by
  obtain ⟨p, hp, hv⟩ := peek_some h
  have hlt := pos_lt_of_peek h
  refine ⟨rfl, by simp [ParseState.advance], rfl, rfl, fun _ => by simp [ParseState.advance]; omega,
    fun _ s _ => ⟨({ s.1 with anchors := n :: s.1.anchors }, s.2), ?_, ?_, ?_, ?_⟩⟩
  · simp only [ParseState.advance]
    rw [seg_one ps.tokens hp]; simp [runToks, hv, stepTok]
  · intro m hm; exact List.mem_cons_of_mem _ hm
  · intro m hm; exact hm
  · intro m hm; simp at hm; subst hm; exact List.mem_cons_self

/-- The tag guard, composed: `parser_tag_guard_exact`'s Bool at the token the
parser is looking at, under scanner fact A. -/
lemma CFA.tag {ps : ParseState} {h suf : String} (hpk : ps.peek? = some (.tag h suf))
    (hg : parserTagGuard ps h = true) : CFA ps ps.advance [] := by
  obtain ⟨p, hp, hv⟩ := peek_some hpk
  have hlt := pos_lt_of_peek hpk
  refine ⟨rfl, by simp [ParseState.advance], rfl, rfl, fun _ => by simp [ParseState.advance]; omega,
    fun hsh s hs => ⟨s, ?_, fun _ h => h, fun _ h => h, fun _ h => by simp at h⟩⟩
  simp only [ParseState.advance]
  rw [seg_one ps.tokens hp]
  simp only [runToks, hv, stepTok]
  by_cases hh : h = ""
  · simp [hh]
  · have hallowed : TagHandleAllowed s.1 h := by
      simp only [parserTagGuard, Bool.or_eq_true, beq_iff_eq, Array.any_eq_true] at hg
      rcases hg with ((h0 | h1) | h2) | ⟨i, hi, hq'⟩
      · exact absurd h0 hh
      · exact Or.inl (Or.inr (Or.inl h1))
      · exact Or.inl (Or.inr (Or.inr h2))
      · rcases hsh p (mem_of_getElem? hp) h suf hv with hb | hn
        · exact Or.inl hb
        · exact Or.inr (hs.2 h hn ⟨ps.tagHandles[i], Array.getElem_mem hi, hq'⟩)
    simp [hh, hallowed]

lemma CFA.declareOpt {ps ps' : ParseState} {names : List String} {o : Option String}
    (h : CFA ps ps' names) (ho : ∀ n, o = some n → n ∈ names) :
    CF ps (ps'.declareAnchorOpt o) := by
  obtain ⟨t, p, g, d, z, r⟩ := h
  cases o with
  | none =>
    refine ⟨t, p, g, z, fun hsh s hs => ?_⟩
    obtain ⟨s', hr, a, hh, -⟩ := r hsh s hs
    exact ⟨s', hr, (hs.of_eq d g).mono a hh⟩
  | some n =>
    refine ⟨t, by simpa [ParseState.declareAnchor] using p, g, by simpa [ParseState.declareAnchor] using z,
      fun hsh s hs => ?_⟩
    obtain ⟨s', hr, a, hh, hn⟩ := r hsh s hs
    refine ⟨s', by simpa [ParseState.declareAnchor] using hr, ?_, ?_⟩
    · intro m hm
      simp only [ParseState.declareAnchorOpt_some, ParseState.declareAnchor, Array.mem_push, d] at hm
      rcases hm with hm | hm
      · exact a m (hs.1 m hm)
      · subst hm; exact hn _ (ho _ rfl)
    · intro hh' hnm hp
      simp only [ParseState.declareAnchorOpt_some, ParseState.declareAnchor_tagHandles, g] at hp
      exact hh hh' (hs.2 hh' hnm hp)


lemma parserTagGuard_of_builtin (ps : ParseState) (h : String)
    (hb : ¬ ((h != "" && h != "!" && h != "!!") = true)) : parserTagGuard ps h = true := by
  by_cases h0 : h = ""
  · simp [parserTagGuard, h0]
  by_cases h1 : h = "!"
  · simp [parserTagGuard, h1]
  by_cases h2 : h = "!!"
  · simp [parserTagGuard, h2]
  exact absurd (by simp [h0, h1, h2]) hb

lemma parserTagGuard_of_any (ps : ParseState) (h : String)
    (ha : ¬ ((!ps.tagHandles.any fun x => x.fst == h) = true)) : parserTagGuard ps h = true := by
  simp only [parserTagGuard, Bool.or_eq_true]
  simp only [Bool.not_eq_true', Bool.not_eq_false] at ha
  exact Or.inr ha

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 3200000 in
/-- The properties stage: 0–2 `&`/`!` tokens, each anchor promised to the
checker, the surviving one declared at the end (`declareAnchorOpt props.anchor`). -/
lemma parseNodeProperties_cf (ps : ParseState) (props : NodeProperties) (ps' : ParseState)
    (h : parseNodeProperties ps = .ok (props, ps')) : CF ps ps' := by
  unfold parseNodeProperties at h
  dsimp only [] at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
             Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
             show List.range' 0 2 1 = 0 :: List.range' 1 1 1 from by decide,
             show List.range' 1 1 1 = [1] from by decide,
             List.forIn_cons, List.forIn_nil, bind, Except.bind, pure, Except.pure] at h
  cases hpk : ps.peek? with
  | none =>
    simp only [hpk, ParseState.declareAnchorOpt_none, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact CF.refl ps
  | some t =>
    cases t
    case anchor n =>
      rw [hpk] at h
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h
      cases hpk2 : (ps.advance).peek? with
      | none =>
        try simp only [hpk2] at h
        try simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        first
          | exact (CFA.refl _).declareOpt (by simp)
          | exact (CFA.anchor hpk).declareOpt (by simp)
          | exact (CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).declareOpt (by simp)
          | exact (CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).declareOpt (by simp)
          | exact ((CFA.anchor hpk).trans (CFA.anchor hpk2)).declareOpt (by simp)
          | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
          | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
          | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).trans (CFA.anchor hpk2)).declareOpt (by simp)
          | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).trans (CFA.anchor hpk2)).declareOpt (by simp)
          | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
          | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
          | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
          | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
      | some t2 =>
        cases t2 <;> simp only [hpk2, Option.isSome_some, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h
        case tag hd2 suf2 =>
          rcases Decidable.em ((hd2 != "" && hd2 != "!" && hd2 != "!!") = true) with hb2 | hb2 <;>
            simp only [hb2, Bool.false_eq_true, ↓reduceIte] at h
          · rcases Decidable.em ((!(ps.advance).tagHandles.any fun x => x.fst == hd2) = true) with hany2 | hany2 <;>
              simp only [hany2, Bool.false_eq_true, ↓reduceIte] at h
            · simp at h
            · 
              try simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              first
                | exact (CFA.refl _).declareOpt (by simp)
                | exact (CFA.anchor hpk).declareOpt (by simp)
                | exact (CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).declareOpt (by simp)
                | exact (CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).declareOpt (by simp)
                | exact ((CFA.anchor hpk).trans (CFA.anchor hpk2)).declareOpt (by simp)
                | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hany2))).declareOpt (by simp)
                | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).trans (CFA.anchor hpk2)).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).trans (CFA.anchor hpk2)).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hany2))).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hany2))).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
          · 
            try simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            first
              | exact (CFA.refl _).declareOpt (by simp)
              | exact (CFA.anchor hpk).declareOpt (by simp)
              | exact (CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).declareOpt (by simp)
              | exact (CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).declareOpt (by simp)
              | exact ((CFA.anchor hpk).trans (CFA.anchor hpk2)).declareOpt (by simp)
              | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hb2))).declareOpt (by simp)
              | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).trans (CFA.anchor hpk2)).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).trans (CFA.anchor hpk2)).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hb2))).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hb2))).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
        all_goals
          try simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          first
            | exact (CFA.refl _).declareOpt (by simp)
            | exact (CFA.anchor hpk).declareOpt (by simp)
            | exact (CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).declareOpt (by simp)
            | exact (CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).declareOpt (by simp)
            | exact ((CFA.anchor hpk).trans (CFA.anchor hpk2)).declareOpt (by simp)
            | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
            | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
            | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).trans (CFA.anchor hpk2)).declareOpt (by simp)
            | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).trans (CFA.anchor hpk2)).declareOpt (by simp)
            | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
            | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
            | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
            | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hpk)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
    case tag hd suf =>
      rw [hpk] at h
      simp only [] at h
      rcases Decidable.em ((hd != "" && hd != "!" && hd != "!!") = true) with hb | hb <;>
        simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      · rcases Decidable.em ((!ps.tagHandles.any fun x => x.fst == hd) = true) with hany | hany <;>
          simp only [hany, Bool.false_eq_true, ↓reduceIte] at h
        · simp at h
        · 
          cases hpk2 : (ps.advance).peek? with
          | none =>
            try simp only [hpk2] at h
            try simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            first
              | exact (CFA.refl _).declareOpt (by simp)
              | exact (CFA.anchor hpk).declareOpt (by simp)
              | exact (CFA.tag hpk (parserTagGuard_of_any _ _ hany)).declareOpt (by simp)
              | exact (CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).declareOpt (by simp)
              | exact ((CFA.anchor hpk).trans (CFA.anchor hpk2)).declareOpt (by simp)
              | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
              | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hany)).trans (CFA.anchor hpk2)).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.anchor hpk2)).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hany)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hany)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
          | some t2 =>
            cases t2 <;> simp only [hpk2, Option.isSome_some, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h
            case tag hd2 suf2 =>
              rcases Decidable.em ((hd2 != "" && hd2 != "!" && hd2 != "!!") = true) with hb2 | hb2 <;>
                simp only [hb2, Bool.false_eq_true, ↓reduceIte] at h
              · rcases Decidable.em ((!(ps.advance).tagHandles.any fun x => x.fst == hd2) = true) with hany2 | hany2 <;>
                  simp only [hany2, Bool.false_eq_true, ↓reduceIte] at h
                · simp at h
                · 
                  try simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨-, rfl⟩ := h
                  first
                    | exact (CFA.refl _).declareOpt (by simp)
                    | exact (CFA.anchor hpk).declareOpt (by simp)
                    | exact (CFA.tag hpk (parserTagGuard_of_any _ _ hany)).declareOpt (by simp)
                    | exact (CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).declareOpt (by simp)
                    | exact ((CFA.anchor hpk).trans (CFA.anchor hpk2)).declareOpt (by simp)
                    | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hany2))).declareOpt (by simp)
                    | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
                    | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hany)).trans (CFA.anchor hpk2)).declareOpt (by simp)
                    | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.anchor hpk2)).declareOpt (by simp)
                    | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hany)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hany2))).declareOpt (by simp)
                    | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hany)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
                    | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hany2))).declareOpt (by simp)
                    | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
              · 
                try simp only [Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨-, rfl⟩ := h
                first
                  | exact (CFA.refl _).declareOpt (by simp)
                  | exact (CFA.anchor hpk).declareOpt (by simp)
                  | exact (CFA.tag hpk (parserTagGuard_of_any _ _ hany)).declareOpt (by simp)
                  | exact (CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).declareOpt (by simp)
                  | exact ((CFA.anchor hpk).trans (CFA.anchor hpk2)).declareOpt (by simp)
                  | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hb2))).declareOpt (by simp)
                  | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
                  | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hany)).trans (CFA.anchor hpk2)).declareOpt (by simp)
                  | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.anchor hpk2)).declareOpt (by simp)
                  | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hany)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hb2))).declareOpt (by simp)
                  | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hany)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
                  | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hb2))).declareOpt (by simp)
                  | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
            all_goals
              try simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              first
                | exact (CFA.refl _).declareOpt (by simp)
                | exact (CFA.anchor hpk).declareOpt (by simp)
                | exact (CFA.tag hpk (parserTagGuard_of_any _ _ hany)).declareOpt (by simp)
                | exact (CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).declareOpt (by simp)
                | exact ((CFA.anchor hpk).trans (CFA.anchor hpk2)).declareOpt (by simp)
                | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
                | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hany)).trans (CFA.anchor hpk2)).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.anchor hpk2)).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hany)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hany)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
      · 
        cases hpk2 : (ps.advance).peek? with
        | none =>
          try simp only [hpk2] at h
          try simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          first
            | exact (CFA.refl _).declareOpt (by simp)
            | exact (CFA.anchor hpk).declareOpt (by simp)
            | exact (CFA.tag hpk (parserTagGuard_of_any _ _ hb)).declareOpt (by simp)
            | exact (CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).declareOpt (by simp)
            | exact ((CFA.anchor hpk).trans (CFA.anchor hpk2)).declareOpt (by simp)
            | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
            | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
            | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hb)).trans (CFA.anchor hpk2)).declareOpt (by simp)
            | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.anchor hpk2)).declareOpt (by simp)
            | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
            | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
            | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
            | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
        | some t2 =>
          cases t2 <;> simp only [hpk2, Option.isSome_some, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h
          case tag hd2 suf2 =>
            rcases Decidable.em ((hd2 != "" && hd2 != "!" && hd2 != "!!") = true) with hb2 | hb2 <;>
              simp only [hb2, Bool.false_eq_true, ↓reduceIte] at h
            · rcases Decidable.em ((!(ps.advance).tagHandles.any fun x => x.fst == hd2) = true) with hany2 | hany2 <;>
                simp only [hany2, Bool.false_eq_true, ↓reduceIte] at h
              · simp at h
              · 
                try simp only [Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨-, rfl⟩ := h
                first
                  | exact (CFA.refl _).declareOpt (by simp)
                  | exact (CFA.anchor hpk).declareOpt (by simp)
                  | exact (CFA.tag hpk (parserTagGuard_of_any _ _ hb)).declareOpt (by simp)
                  | exact (CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).declareOpt (by simp)
                  | exact ((CFA.anchor hpk).trans (CFA.anchor hpk2)).declareOpt (by simp)
                  | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hany2))).declareOpt (by simp)
                  | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
                  | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hb)).trans (CFA.anchor hpk2)).declareOpt (by simp)
                  | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.anchor hpk2)).declareOpt (by simp)
                  | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hany2))).declareOpt (by simp)
                  | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
                  | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hany2))).declareOpt (by simp)
                  | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
            · 
              try simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              first
                | exact (CFA.refl _).declareOpt (by simp)
                | exact (CFA.anchor hpk).declareOpt (by simp)
                | exact (CFA.tag hpk (parserTagGuard_of_any _ _ hb)).declareOpt (by simp)
                | exact (CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).declareOpt (by simp)
                | exact ((CFA.anchor hpk).trans (CFA.anchor hpk2)).declareOpt (by simp)
                | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hb2))).declareOpt (by simp)
                | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hb)).trans (CFA.anchor hpk2)).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.anchor hpk2)).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hb2))).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hb2))).declareOpt (by simp)
                | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hb2))).declareOpt (by simp)
          all_goals
            try simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            first
              | exact (CFA.refl _).declareOpt (by simp)
              | exact (CFA.anchor hpk).declareOpt (by simp)
              | exact (CFA.tag hpk (parserTagGuard_of_any _ _ hb)).declareOpt (by simp)
              | exact (CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).declareOpt (by simp)
              | exact ((CFA.anchor hpk).trans (CFA.anchor hpk2)).declareOpt (by simp)
              | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
              | exact ((CFA.anchor hpk).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hb)).trans (CFA.anchor hpk2)).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.anchor hpk2)).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_any _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_any _ _ hpk2))).declareOpt (by simp)
              | exact ((CFA.tag hpk (parserTagGuard_of_builtin _ _ hb)).trans (CFA.tag hpk2 (parserTagGuard_of_builtin _ _ hpk2))).declareOpt (by simp)
    all_goals
      simp only [hpk, ParseState.declareAnchorOpt_none, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact CF.refl ps


/-! ## The content clique: one `CF` lemma per parser, mirroring `ParserNodeProofs`'s `AG` family -/

lemma CF.withField (ps : ParseState) (p : YamlPath) : CF ps { ps with currentPath := p } :=
  CF.of_eq rfl rfl rfl rfl

lemma applyNodeFinalization_cf (val : YamlValue) (ps : ParseState) (props : NodeProperties)
    (pos : YamlPos) : CF ps (applyNodeFinalization val ps props pos).2 := by
  unfold applyNodeFinalization
  dsimp only []
  split <;> split <;> exact CF.of_eq rfl rfl rfl rfl

def ParseNodeCF (n : Nat) : Prop :=
  ∀ (ps : ParseState) (m : Nat) (val : YamlValue) (ps' : ParseState),
    m ≤ n → parseNode ps m = .ok (val, ps') → CF ps ps'

variable {n : Nat}

lemma parseBlockSequenceLoop_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (items : Array YamlValue)
    (h_fuel : fuel ≤ n + 1)
    (result : Array YamlValue) (ps' : ParseState)
    (h_ok : parseBlockSequenceLoop ps fuel items = .ok (result, ps')) :
    CF ps ps' := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseBlockSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact CF.refl ps
  | succ k ih_fuel =>
    unfold parseBlockSequenceLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · rename_i hpk
      have h_adv : CF ps ps.advance := CF.advance_neutral hpk rfl
      split at h_ok
      · exact CF.trans h_adv (ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok)
      · exact CF.trans h_adv (ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok)
      · exact CF.trans h_adv (ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok)
      · split at h_ok
        · simp at h_ok
        · rename_i pn_res heq_pn
          obtain ⟨val_n, ps_n⟩ := pn_res
          dsimp only [] at h_ok
          have h_n := h_ih _ k val_n ps_n (by omega) heq_pn
          exact CF.trans h_adv
            (CF.trans (CF.withField ps.advance _)
              (CF.trans h_n
                (CF.trans (CF.withField ps_n _)
                  (ih_fuel _ _ (by omega) h_ok))))
    · simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact CF.refl ps

lemma parseBlockSequence_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (h_peek : ps.peek? = some .blockSequenceStart)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseBlockSequence ps fuel = .ok (val, ps')) :
    CF ps ps' ∧ ps.pos < ps'.pos := by
  unfold parseBlockSequence at h_ok
  cases fuel with
  | zero => simp at h_ok
  | succ k =>
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · simp at h_ok
    · rename_i res heq
      obtain ⟨items, ps_l⟩ := res
      dsimp only [] at h_ok
      have h_adv : CF ps ps.advance := CF.advance_neutral h_peek rfl
      have h_loop := parseBlockSequenceLoop_cf h_ih ps.advance k #[] (by omega) items ps_l heq
      have h_tail : CF ps_l (match ps_l.peek? with | some .blockEnd => ps_l.advance | _ => ps_l) := by
        split
        · exact CF.advance_neutral (by assumption) rfl
        · exact CF.refl _
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
      have h_all := CF.trans h_adv (CF.trans h_loop h_tail)
      refine ⟨h_all, ?_⟩
      have h1 : ps.pos + 1 ≤ ps_l.pos := h_loop.2.1
      exact Nat.lt_of_lt_of_le (by omega) h_tail.2.1

lemma parseImplicitBlockSequenceLoop_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (items : Array YamlValue)
    (h_fuel : fuel ≤ n + 1)
    (result : Array YamlValue) (ps' : ParseState)
    (h_ok : parseImplicitBlockSequenceLoop ps fuel items = .ok (result, ps')) :
    CF ps ps' ∧ (0 < fuel → ps.peek? = some .blockEntry → ps.pos < ps'.pos) := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseImplicitBlockSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact ⟨CF.refl ps, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | succ k ih_fuel =>
    unfold parseImplicitBlockSequenceLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · rename_i hpk
      have h_adv : CF ps ps.advance := CF.advance_neutral hpk rfl
      have key : ∀ ps₂, CF ps.advance ps₂ → CF ps ps₂ ∧ (0 < k + 1 → ps.peek? = some .blockEntry → ps.pos < ps₂.pos) := by
        intro ps₂ h₂
        refine ⟨CF.trans h_adv h₂, fun _ _ => ?_⟩
        have := h₂.2.1; simp only [ParseState.advance] at this; omega
      split at h_ok
      · exact key _ (ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok).1
      · exact key _ (ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok).1
      · exact key _ (ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok).1
      · exact key _ (ih_fuel ps.advance (items.push emptyNode) (by omega) h_ok).1
      · split at h_ok
        · simp at h_ok
        · rename_i pn_res heq_pn
          obtain ⟨val_n, ps_n⟩ := pn_res
          dsimp only [] at h_ok
          have h_n := h_ih _ k val_n ps_n (by omega) heq_pn
          exact key _
            (CF.trans (CF.withField ps.advance _)
              (CF.trans h_n
                (CF.trans (CF.withField ps_n _)
                  (ih_fuel _ _ (by omega) h_ok).1)))
    · rename_i hpk
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
      exact ⟨CF.refl ps, fun _ h => absurd h hpk⟩

lemma parseImplicitBlockSequence_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseImplicitBlockSequence ps fuel = .ok (val, ps')) :
    CF ps ps' ∧ (1 < fuel → ps.peek? = some .blockEntry → ps.pos < ps'.pos) := by
  unfold parseImplicitBlockSequence at h_ok
  cases fuel with
  | zero => simp at h_ok
  | succ k =>
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · simp at h_ok
    · rename_i res heq
      obtain ⟨items, ps_l⟩ := res
      dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
      have := parseImplicitBlockSequenceLoop_cf h_ih ps k #[] (by omega) items ps_l heq
      exact ⟨this.1, fun hk hpk => this.2 (by omega) hpk⟩


lemma parseBlockMappingEntryValue_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (keyHasContent : Bool) (keyLine keyCol : Nat)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseBlockMappingEntryValue ps fuel keyHasContent keyLine keyCol = .ok (val, ps')) :
    CF ps ps' := by
  unfold parseBlockMappingEntryValue at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  have h_tc : CF ps (ps.tryConsume .value).2 := CF.tryConsume rfl
  split at h_ok
  · all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals try (obtain ⟨rfl, rfl⟩ := h_ok; exact h_tc)
    all_goals exact CF.trans h_tc (h_ih _ fuel _ _ h_fuel h_ok)
  · have h_pre : CF ps (((ps.tryConsume .value).2.tryConsume .key).2.tryConsume .value).2 :=
      CF.trans h_tc (CF.trans (CF.tryConsume rfl) (CF.tryConsume rfl))
    split at h_ok
    all_goals (try (split at h_ok))
    all_goals (first
      | (obtain ⟨rfl, rfl⟩ := h_ok; exact h_tc)
      | (obtain ⟨rfl, rfl⟩ := h_ok; exact h_pre)
      | exact CF.trans h_pre (h_ih _ fuel _ _ h_fuel h_ok))

lemma handleBlockMappingKeyEntry_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n) (pairIdx : Nat)
    (h_peek : ps.peek? = some .key)
    (key val : YamlValue) (ps' : ParseState)
    (h_ok : handleBlockMappingKeyEntry ps fuel pairIdx = .ok (key, val, ps')) :
    CF ps ps' := by
  unfold handleBlockMappingKeyEntry at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  have h_adv : CF ps ps.advance := CF.advance_neutral h_peek rfl
  split at h_ok
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (simp only [Except.ok.injEq, Prod.mk.injEq] at h_ok; obtain ⟨-, -, rfl⟩ := h_ok)
  all_goals (first
    | exact CF.trans h_adv (CF.trans (CF.withField _ _)
        (CF.trans (parseBlockMappingEntryValue_cf h_ih _ fuel h_fuel _ _ _ _ _ ‹_›) (CF.withField _ _)))
    | exact CF.trans h_adv (CF.trans (h_ih _ fuel _ _ h_fuel ‹_›) (CF.trans (CF.withField _ _)
        (CF.trans (parseBlockMappingEntryValue_cf h_ih _ fuel h_fuel _ _ _ _ _ ‹_›) (CF.withField _ _)))))

lemma handleBlockMappingValueEntry_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n) (pairIdx : Nat)
    (h_peek : ps.peek? = some .value)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : handleBlockMappingValueEntry ps fuel pairIdx = .ok (val, ps')) :
    CF ps ps' := by
  unfold handleBlockMappingValueEntry at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  have h_adv : CF ps ps.advance := CF.advance_neutral h_peek rfl
  split at h_ok
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (simp only [Except.ok.injEq, Prod.mk.injEq] at h_ok; obtain ⟨-, rfl⟩ := h_ok)
  all_goals (first
    | exact CF.trans h_adv (CF.trans (CF.withField _ _) (CF.withField _ _))
    | exact CF.trans h_adv (CF.trans (CF.withField _ _)
        (CF.trans (h_ih _ fuel _ _ h_fuel ‹_›) (CF.withField _ _))))

lemma parseBlockMappingLoop_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (pairs : Array (YamlValue × YamlValue))
    (h_fuel : fuel ≤ n + 1)
    (result : Array (YamlValue × YamlValue)) (ps' : ParseState)
    (h_ok : parseBlockMappingLoop ps fuel pairs = .ok (result, ps')) :
    CF ps ps' := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseBlockMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact CF.refl ps
  | succ k ih_fuel =>
    unfold parseBlockMappingLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · rename_i hpk
      split at h_ok
      · simp at h_ok
      · rename_i res heq
        obtain ⟨key, val, ps_e⟩ := res
        dsimp only [] at h_ok
        exact CF.trans (handleBlockMappingKeyEntry_cf h_ih ps k (by omega) _ hpk key val ps_e heq)
          (ih_fuel _ _ (by omega) h_ok)
    · rename_i hpk
      split at h_ok
      · simp at h_ok
      · rename_i res heq
        obtain ⟨val, ps_e⟩ := res
        dsimp only [] at h_ok
        exact CF.trans (handleBlockMappingValueEntry_cf h_ih ps k (by omega) _ hpk val ps_e heq)
          (ih_fuel _ _ (by omega) h_ok)
    · simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact CF.refl ps

lemma parseBlockMapping_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (h_peek : ps.peek? = some .blockMappingStart)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseBlockMapping ps fuel = .ok (val, ps')) :
    CF ps ps' ∧ ps.pos < ps'.pos := by
  unfold parseBlockMapping at h_ok
  cases fuel with
  | zero => simp at h_ok
  | succ k =>
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · simp at h_ok
    · rename_i res heq
      obtain ⟨pairs, ps_l⟩ := res
      dsimp only [] at h_ok
      have h_adv : CF ps ps.advance := CF.advance_neutral h_peek rfl
      have h_loop := parseBlockMappingLoop_cf h_ih ps.advance k #[] (by omega) pairs ps_l heq
      have h_tail : CF ps_l (match ps_l.peek? with | some .blockEnd => ps_l.advance | _ => ps_l) := by
        split
        · exact CF.advance_neutral (by assumption) rfl
        · exact CF.refl _
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
      refine ⟨CF.trans h_adv (CF.trans h_loop h_tail), ?_⟩
      have h1 : ps.pos + 1 ≤ ps_l.pos := h_loop.2.1
      exact Nat.lt_of_lt_of_le (by omega) h_tail.2.1


/-- Tokens before which `parseNodeContent` yields an empty node without
consuming (`TokenGrammar.emptyFollower`, extended with the tokens the
scanner never emits there). -/
def emptyFollowerTok : Option YamlToken → Bool
  | some (.scalar ..) | some .blockSequenceStart | some .blockMappingStart | some .blockEntry
  | some .flowSequenceStart | some .flowMappingStart => false
  | _ => true

lemma parseExplicitKey_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseExplicitKey ps fuel = .ok (val, ps')) :
    CF ps ps' := by
  unfold parseExplicitKey at h_ok
  split at h_ok
  · simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact CF.refl _
  · simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact CF.refl _
  · simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact CF.refl _
  · exact h_ih _ fuel _ _ h_fuel h_ok

lemma parseFlowMappingValue_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (savedPath : YamlPath) (keyContent : String)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseFlowMappingValue ps fuel savedPath keyContent = .ok (val, ps')) :
    CF ps ps' := by
  unfold parseFlowMappingValue at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  have h_pre : CF ps (({ ps with currentPath := savedPath.push (.key keyContent) }.tryConsume .key).2.tryConsume .value).2 :=
    CF.trans (CF.withField _ _) (CF.trans (CF.tryConsume rfl) (CF.tryConsume rfl))
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (simp only [Except.ok.injEq, Prod.mk.injEq] at h_ok; obtain ⟨-, rfl⟩ := h_ok)
  all_goals (first
    | exact CF.trans h_pre (CF.withField _ _)
    | exact CF.trans h_pre (CF.trans (h_ih _ fuel _ _ h_fuel ‹_›) (CF.withField _ _)))

lemma parseSinglePairMapping_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (h_peek : ps.peek? = some .key)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseSinglePairMapping ps fuel = .ok (val, ps')) :
    CF ps ps' := by
  unfold parseSinglePairMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  have h_adv : CF ps ps.advance := CF.advance_neutral h_peek rfl
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok <;> first | contradiction | skip
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (simp only [Except.ok.injEq] at h_ok)
    all_goals (obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok)
    all_goals try exact CF.trans h_adv (CF.trans (CF.withField ps.advance _)
        (CF.trans (CF.tryConsume rfl) (CF.withField _ _)))
    all_goals try exact CF.trans h_adv (CF.trans (CF.withField ps.advance _)
        (CF.trans (CF.tryConsume rfl) (CF.trans (h_ih _ k _ _ (by omega) (by assumption))
          (CF.withField _ _))))
    all_goals try exact CF.trans h_adv (CF.trans (h_ih _ k _ _ (by omega) (by assumption))
        (CF.trans (CF.withField _ _) (CF.trans (CF.tryConsume rfl) (CF.withField _ _))))
    all_goals exact CF.trans h_adv (CF.trans (h_ih _ k _ _ (by omega) (by assumption))
        (CF.trans (CF.withField _ _) (CF.trans (CF.tryConsume rfl)
          (CF.trans (h_ih _ k _ _ (by omega) (by assumption)) (CF.withField _ _)))))

lemma parseFlowSequenceLoop_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (items : Array YamlValue)
    (h_fuel : fuel ≤ n + 1)
    (result : Array YamlValue) (ps' : ParseState)
    (h_ok : parseFlowSequenceLoop ps fuel items = .ok (result, ps')) :
    CF ps ps' := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact CF.refl _
  | succ k ih_fuel =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    next =>
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact CF.refl _
    next =>
      split at h_ok
      · split at h_ok
        next hfe =>
          have h_adv : CF ps ps.advance := CF.advance_neutral hfe rfl
          split at h_ok
          next hk =>
            split at h_ok
            next => simp at h_ok
            next spm_res heq_spm =>
              obtain ⟨mv, ps3⟩ := spm_res; dsimp only [] at h_ok
              have hk' : ParseState.peek? { ps.advance with
                currentPath := ps.advance.currentPath.push (.index items.size) } = some .key := hk
              exact CF.trans h_adv (CF.trans (CF.withField ps.advance _)
                  (CF.trans (parseSinglePairMapping_cf h_ih _ k (by omega) hk' mv ps3 heq_spm)
                    (CF.trans (CF.withField ps3 _) (ih_fuel _ _ (by omega) h_ok))))
          next =>
            simp only [Except.ok.injEq] at h_ok
            obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_adv
          next =>
            split at h_ok
            next => simp at h_ok
            next pn_res heq_pn =>
              obtain ⟨v, ps3⟩ := pn_res; dsimp only [] at h_ok
              exact CF.trans h_adv (CF.trans (CF.withField ps.advance _)
                  (CF.trans (h_ih _ k v ps3 (by omega) heq_pn)
                    (CF.trans (CF.withField ps3 _) (ih_fuel _ _ (by omega) h_ok))))
        next =>
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact CF.refl _
      · split at h_ok
        next hk =>
          split at h_ok
          next => simp at h_ok
          next spm_res heq_spm =>
            obtain ⟨mv, ps3⟩ := spm_res; dsimp only [] at h_ok
            have hk' : ParseState.peek? { ps with
              currentPath := ps.currentPath.push (.index items.size) } = some .key := hk
            exact CF.trans (CF.withField ps _)
                (CF.trans (parseSinglePairMapping_cf h_ih _ k (by omega) hk' mv ps3 heq_spm)
                  (CF.trans (CF.withField ps3 _) (ih_fuel _ _ (by omega) h_ok)))
        next =>
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact CF.refl _
        next =>
          split at h_ok
          next => simp at h_ok
          next pn_res heq_pn =>
            obtain ⟨v, ps3⟩ := pn_res; dsimp only [] at h_ok
            exact CF.trans (CF.withField ps _)
                (CF.trans (h_ih _ k v ps3 (by omega) heq_pn)
                  (CF.trans (CF.withField ps3 _) (ih_fuel _ _ (by omega) h_ok)))

lemma parseFlowSequence_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (h_peek : ps.peek? = some .flowSequenceStart)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseFlowSequence ps fuel = .ok (val, ps')) :
    CF ps ps' ∧ ps.pos < ps'.pos := by
  unfold parseFlowSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨items, ps_loop⟩ := loop_res
      dsimp only [] at h_ok
      have h_adv : CF ps ps.advance := CF.advance_neutral h_peek rfl
      have h_loop := parseFlowSequenceLoop_cf h_ih ps.advance k #[] (by omega) items ps_loop heq_loop
      split at h_ok
      · rename_i hend
        simp only [Except.ok.injEq] at h_ok
        obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
        have h1 : ps.pos + 1 ≤ ps_loop.pos := h_loop.2.1
        exact ⟨CF.trans h_adv (CF.trans h_loop (CF.advance_neutral hend rfl)),
          by simp only [ParseState.advance]; omega⟩
      · simp at h_ok

lemma parseFlowMappingLoop_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (pairs : Array (YamlValue × YamlValue))
    (h_fuel : fuel ≤ n + 1)
    (result : Array (YamlValue × YamlValue)) (ps' : ParseState)
    (h_ok : parseFlowMappingLoop ps fuel pairs = .ok (result, ps')) :
    CF ps ps' := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact CF.refl _
  | succ k ih_fuel =>
    unfold parseFlowMappingLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    next =>
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact CF.refl _
    next =>
      split at h_ok
      · split at h_ok
        next hfe =>
          have h_adv : CF ps ps.advance := CF.advance_neutral hfe rfl
          split at h_ok
          next =>
            simp only [Except.ok.injEq] at h_ok
            obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_adv
          next hk =>
            split at h_ok
            next => simp at h_ok
            next ek_res heq_ek =>
              obtain ⟨key_v, ps_ek⟩ := ek_res; dsimp only [] at h_ok
              split at h_ok
              next => simp at h_ok
              next fmv_res heq_fmv =>
                obtain ⟨val_v, ps_fmv⟩ := fmv_res; dsimp only [] at h_ok
                exact CF.trans h_adv (CF.trans (CF.advance_neutral hk rfl)
                    (CF.trans (parseExplicitKey_cf h_ih ps.advance.advance k (by omega) key_v ps_ek heq_ek)
                      (CF.trans (parseFlowMappingValue_cf h_ih ps_ek k (by omega) _ _ val_v ps_fmv heq_fmv)
                        (ih_fuel _ _ (by omega) h_ok))))
          next =>
            split at h_ok
            next => simp at h_ok
            next pn_res heq_pn =>
              obtain ⟨key_v, ps_pn⟩ := pn_res; dsimp only [] at h_ok
              split at h_ok
              next => simp at h_ok
              next fmv_res heq_fmv =>
                obtain ⟨val_v, ps_fmv⟩ := fmv_res; dsimp only [] at h_ok
                exact CF.trans h_adv
                    (CF.trans (h_ih _ k key_v ps_pn (by omega) heq_pn)
                      (CF.trans (parseFlowMappingValue_cf h_ih ps_pn k (by omega) _ _ val_v ps_fmv heq_fmv)
                        (ih_fuel _ _ (by omega) h_ok)))
        next =>
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact CF.refl _
      · split at h_ok
        next =>
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact CF.refl _
        next hk =>
          split at h_ok
          next => simp at h_ok
          next ek_res heq_ek =>
            obtain ⟨key_v, ps_ek⟩ := ek_res; dsimp only [] at h_ok
            split at h_ok
            next => simp at h_ok
            next fmv_res heq_fmv =>
              obtain ⟨val_v, ps_fmv⟩ := fmv_res; dsimp only [] at h_ok
              exact CF.trans (CF.advance_neutral hk rfl)
                  (CF.trans (parseExplicitKey_cf h_ih ps.advance k (by omega) key_v ps_ek heq_ek)
                    (CF.trans (parseFlowMappingValue_cf h_ih ps_ek k (by omega) _ _ val_v ps_fmv heq_fmv)
                      (ih_fuel _ _ (by omega) h_ok)))
        next =>
          split at h_ok
          next => simp at h_ok
          next pn_res heq_pn =>
            obtain ⟨key_v, ps_pn⟩ := pn_res; dsimp only [] at h_ok
            split at h_ok
            next => simp at h_ok
            next fmv_res heq_fmv =>
              obtain ⟨val_v, ps_fmv⟩ := fmv_res; dsimp only [] at h_ok
              exact CF.trans (h_ih _ k key_v ps_pn (by omega) heq_pn)
                  (CF.trans (parseFlowMappingValue_cf h_ih ps_pn k (by omega) _ _ val_v ps_fmv heq_fmv)
                    (ih_fuel _ _ (by omega) h_ok))

lemma parseFlowMapping_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (h_peek : ps.peek? = some .flowMappingStart)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseFlowMapping ps fuel = .ok (val, ps')) :
    CF ps ps' ∧ ps.pos < ps'.pos := by
  unfold parseFlowMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨pairs, ps_loop⟩ := loop_res
      dsimp only [] at h_ok
      have h_adv : CF ps ps.advance := CF.advance_neutral h_peek rfl
      have h_loop := parseFlowMappingLoop_cf h_ih ps.advance k #[] (by omega) pairs ps_loop heq_loop
      split at h_ok
      · rename_i hend
        simp only [Except.ok.injEq] at h_ok
        obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
        have h1 : ps.pos + 1 ≤ ps_loop.pos := h_loop.2.1
        exact ⟨CF.trans h_adv (CF.trans h_loop (CF.advance_neutral hend rfl)),
          by simp only [ParseState.advance]; omega⟩
      · simp at h_ok

/-- Content dispatch; the second component is the stuck analysis: content that
is not an empty node consumes something. -/
lemma parseNodeContent_cf (h_ih : ParseNodeCF n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (props : NodeProperties) (isSeqEntry : Bool) (val : YamlValue) (ps' : ParseState)
    (h_ok : parseNodeContent ps fuel props isSeqEntry = .ok (val, ps')) :
    CF ps ps' ∧ (ps'.pos = ps.pos → 1 < fuel →
      emptyFollowerTok ps.peek? = true ∨ (isSeqEntry = true ∧ ps.peek? = some .blockEntry)) := by
  unfold parseNodeContent at h_ok
  split at h_ok
  · rename_i hpk
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
    exact ⟨CF.advance_neutral hpk rfl, fun h => by simp [ParseState.advance] at h⟩
  · rename_i hpk
    have := parseBlockSequence_cf h_ih ps fuel (by omega) hpk val ps' h_ok
    exact ⟨this.1, fun h => by omega⟩
  · rename_i hpk
    have := parseBlockMapping_cf h_ih ps fuel (by omega) hpk val ps' h_ok
    exact ⟨this.1, fun h => by omega⟩
  · rename_i hpk
    split at h_ok
    · rename_i hse
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
      exact ⟨CF.refl _, fun _ _ => Or.inr ⟨hse, hpk⟩⟩
    · have := parseImplicitBlockSequence_cf h_ih ps fuel (by omega) val ps' h_ok
      exact ⟨this.1, fun h hf => absurd (this.2 hf hpk) (by omega)⟩
  · rename_i hpk
    have := parseFlowSequence_cf h_ih ps fuel (by omega) hpk val ps' h_ok
    exact ⟨this.1, fun h => by omega⟩
  · rename_i hpk
    have := parseFlowMapping_cf h_ih ps fuel (by omega) hpk val ps' h_ok
    exact ⟨this.1, fun h => by omega⟩
  · simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
    refine ⟨CF.refl _, fun _ _ => Or.inl ?_⟩
    unfold emptyFollowerTok
    cases hpk : ps.peek? with
    | none => rfl
    | some t =>
      cases t
      all_goals first
        | rfl
        | exact absurd hpk ‹_›
        | exact absurd hpk (‹∀ c s, ps.peek? = some (YamlToken.scalar c s) → False› _ _)


set_option maxHeartbeats 800000 in
/-- Every `parseNode` call satisfies `CF`: the alias guard (`CF.alias`), the
properties stage (`parseNodeProperties_cf`), content, finalization. Capstone
7.7 via S5. -/
lemma parseNode_cf_all : ∀ n, ParseNodeCF n := by
  intro n
  induction n with
  | zero =>
    intro ps m val ps' h_le h_ok
    have : m = 0 := by omega
    subst this
    simp [parseNode] at h_ok
  | succ n ih =>
    intro ps m val ps' h_le h_ok
    cases m with
    | zero => simp [parseNode] at h_ok
    | succ k =>
      have h_k_le : k ≤ n := by omega
      unfold parseNode at h_ok
      simp only [bind, Except.bind, pure, Except.pure] at h_ok
      split at h_ok
      · rename_i _ name hpk
        split at h_ok <;> first | contradiction | skip
        rename_i hguard
        have hg : ps.declaredIndex.contains name = true := by
          simpa [Bool.not_eq_true'] using hguard
        split at h_ok <;> (
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok)
        · exact CF.trans (CF.alias hpk hg) (CF.of_eq rfl rfl rfl rfl)
        · exact CF.alias hpk hg
      · split at h_ok
        · simp at h_ok
        · rename_i props_res heq_props
          obtain ⟨props, ps_props⟩ := props_res
          dsimp only [] at h_ok
          have h_props := parseNodeProperties_cf ps props ps_props heq_props
          split at h_ok <;> first | contradiction | skip
          split at h_ok
          · simp at h_ok
          · rename_i content_res heq_content
            obtain ⟨val_c, ps_c⟩ := content_res
            dsimp only [] at h_ok
            have h_content := (parseNodeContent_cf ih ps_props k h_k_le props _ val_c ps_c heq_content).1
            simp only [Except.ok.injEq] at h_ok
            obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
            exact CF.trans h_props (CF.trans h_content (applyNodeFinalization_cf val_c ps_c props _))

lemma parseNode_cf (ps : ParseState) (m : Nat) (val : YamlValue) (ps' : ParseState)
    (h_ok : parseNode ps m = .ok (val, ps')) : CF ps ps' :=
  parseNode_cf_all m ps m val ps' (Nat.le_refl m) h_ok

/-- A position `k` at which `parseDocument` can consume nothing: the token is
one `parseNodeContent` treats as an empty node, or a `-` right after a `-`
(the sequence-entry empty node). -/
def StuckAt (ts : Toks) (k : Nat) : Prop :=
  emptyFollowerTok (tok ts k) = true ∨
    (tok ts k = some .blockEntry ∧ 0 < k ∧ tok ts (k - 1) = some .blockEntry)

lemma peek_eq_of_cf {ps ps' : ParseState} (h : CF ps ps') (hpos : ps'.pos = ps.pos) :
    ps'.peek? = ps.peek? := by
  rw [peek_eq_tok, peek_eq_tok, h.1, hpos]

/-- The stuck analysis for one node: a `parseNode` that consumes nothing sits
at a `StuckAt` position. -/
lemma parseNode_stuck (ps : ParseState) (m : Nat) (val : YamlValue) (ps' : ParseState)
    (h_fuel : 2 < m) (h_ok : parseNode ps m = .ok (val, ps')) (hpos : ps'.pos = ps.pos) :
    StuckAt ps.tokens ps.pos := by
  cases m with
  | zero => simp [parseNode] at h_ok
  | succ k =>
    unfold parseNode at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · split at h_ok <;> first | contradiction | skip
      split at h_ok <;> (
        simp only [Except.ok.injEq] at h_ok
        obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok) <;> simp [ParseState.advance] at hpos
    · split at h_ok
      · simp at h_ok
      · rename_i props_res heq_props
        obtain ⟨props, ps_props⟩ := props_res
        dsimp only [] at h_ok
        have h_props := parseNodeProperties_cf ps props ps_props heq_props
        split at h_ok <;> first | contradiction | skip
        split at h_ok
        · simp at h_ok
        · rename_i content_res heq_content
          obtain ⟨val_c, ps_c⟩ := content_res
          dsimp only [] at h_ok
          have h_content := parseNodeContent_cf (parseNode_cf_all k) ps_props k (Nat.le_refl k)
            props _ val_c ps_c heq_content
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
          have hfin : ps_c.pos ≤ (applyNodeFinalization val_c ps_c props
              (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2.pos :=
            (applyNodeFinalization_cf val_c ps_c props _).2.1
          have hfin' : ps_c.pos ≤ ps.pos := Nat.le_trans hfin (Nat.le_of_eq hpos)
          have h1 := h_content.1.2.1
          have h2 := h_props.2.1
          have hpos_c : ps_c.pos = ps_props.pos := by omega
          have hpos_p : ps_props.pos = ps.pos := by omega
          have hpk : ps_props.peek? = ps.peek? := peek_eq_of_cf h_props hpos_p
          rcases h_content.2 hpos_c (by omega) with h | ⟨hse, hbe⟩
          · left; rw [← peek_eq_tok, ← hpk]; exact h
          · right
            rw [hpk] at hbe
            refine ⟨by rw [← peek_eq_tok]; exact hbe, ?_⟩
            have hlt := pos_lt_of_peek hbe
            revert hse
            split
            · rename_i hgt; intro hse
              split at hse
              · rename_i hbe'
                refine ⟨hgt, ?_⟩
                rw [tok, Array.getElem?_eq_getElem (by omega)]
                simp only [Option.map_some, Option.some.injEq]
                rw [getElem!_pos ps.tokens (ps.pos - 1) (by omega)] at hbe'
                exact hbe'
              · simp at hse
            · intro hse; simp at hse


/-! ## Directives, document prefix, document -/

/-- `parseDirectives`'s loop body, as `Id.run` leaves it. -/
def dirBody : Nat → ParseState × Array Directive → Id (ForInStep (ParseState × Array Directive)) :=
  fun _ s => match s.1.peek? with
    | some (.versionDirective major minor) =>
      pure (ForInStep.yield (s.1.advance, s.2.push (.yaml (toString major ++ toString "." ++ toString minor))))
    | some (.tagDirective handle tagPrefix) =>
      pure (ForInStep.yield (s.1.advance, s.2.push (.tag handle tagPrefix)))
    | _ => pure (ForInStep.done (s.1, s.2))

/-- What a directive run does: positions advance over directives only, the
checker accumulates exactly the named handles, every `%TAG` collected is
named-or-pending. -/
lemma dirLoop (l : List Nat) (ps : ParseState) (dirs : Array Directive)
    (ps' : ParseState) (dirs' : Array Directive)
    (h : (forIn l (ps, dirs) dirBody : Id _) = (ps', dirs')) :
    ps'.tokens = ps.tokens ∧ ps.pos ≤ ps'.pos ∧ ps'.pos ≤ ps.pos + l.length ∧
    ps'.declaredAnchors = ps.declaredAnchors ∧ ps'.tagHandles = ps.tagHandles ∧
    (isDirectiveTok (tok ps'.tokens ps'.pos) = false ∨ ps'.pos = ps.pos + l.length) ∧
    ((ps'.pos = ps.pos ∧ dirs' = dirs ∧ (l = [] ∨ isDirectiveTok (tok ps.tokens ps.pos) = false)) ∨
      (ps.pos < ps'.pos ∧ isDirectiveTok (tok ps.tokens (ps'.pos - 1)) = true)) ∧
    ∀ env pending, ∃ pending', runToks (seg ps.tokens ps.pos ps'.pos) (env, pending) = some (env, pending') ∧
      (∀ x, x ∈ pending → x ∈ pending') ∧
      (∀ hd pre, Directive.tag hd pre ∈ dirs' →
        Directive.tag hd pre ∈ dirs ∨ (isNamedHandle hd = true → hd ∈ pending')) := by
  induction l generalizing ps dirs with
  | nil =>
    simp only [List.forIn_nil, Id.run, pure, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, Nat.le_refl _, by simp, rfl, rfl, Or.inr (by simp), Or.inl ⟨rfl, rfl, Or.inl rfl⟩,
      fun env pending => ⟨pending, by simp [runToks], fun _ h => h, fun _ _ h => Or.inl h⟩⟩
  | cons a l ih =>
    rw [List.forIn_cons] at h
    have hstep : ∀ t, ps.peek? = some t → (∃ ma mi, t = .versionDirective ma mi) ∨ (∃ hd pre, t = .tagDirective hd pre) →
        ∀ (dirs₂ : Array Directive), (∀ hd pre, Directive.tag hd pre ∈ dirs₂ →
            Directive.tag hd pre ∈ dirs ∨ t = .tagDirective hd pre) →
        (forIn l (ps.advance, dirs₂) dirBody : Id _) = (ps', dirs') →
        ps'.tokens = ps.tokens ∧ ps.pos ≤ ps'.pos ∧ ps'.pos ≤ ps.pos + (a :: l).length ∧
        ps'.declaredAnchors = ps.declaredAnchors ∧ ps'.tagHandles = ps.tagHandles ∧
        (isDirectiveTok (tok ps'.tokens ps'.pos) = false ∨ ps'.pos = ps.pos + (a :: l).length) ∧
        ((ps'.pos = ps.pos ∧ dirs' = dirs ∧ ((a :: l) = [] ∨ isDirectiveTok (tok ps.tokens ps.pos) = false)) ∨
          (ps.pos < ps'.pos ∧ isDirectiveTok (tok ps.tokens (ps'.pos - 1)) = true)) ∧
        ∀ env pending, ∃ pending', runToks (seg ps.tokens ps.pos ps'.pos) (env, pending) = some (env, pending') ∧
          (∀ x, x ∈ pending → x ∈ pending') ∧
          (∀ hd pre, Directive.tag hd pre ∈ dirs' →
            Directive.tag hd pre ∈ dirs ∨ (isNamedHandle hd = true → hd ∈ pending')) := by
      intro t hpk ht dirs₂ hdirs₂ h
      obtain ⟨p, hp, hv⟩ := peek_some hpk
      have hlt := pos_lt_of_peek hpk
      obtain ⟨t1, p1, p2, d1, g1, nd, lst, r⟩ := ih ps.advance dirs₂ h
      simp only [ParseState.advance] at t1 p1 p2 d1 g1 nd lst r
      have hdir : isDirectiveTok (tok ps.tokens ps.pos) = true := by
        rw [← peek_eq_tok, hpk]
        rcases ht with ⟨ma, mi, rfl⟩ | ⟨hd, pre, rfl⟩ <;> rfl
      refine ⟨t1, by omega, by simp [List.length_cons]; omega, d1, g1, ?_, ?_, fun env pending => ?_⟩
      · rcases nd with nd | nd
        · exact Or.inl nd
        · exact Or.inr (by simp [List.length_cons]; omega)
      · right
        rcases lst with ⟨hp', -, -⟩ | ⟨hp', hd'⟩
        · refine ⟨by omega, ?_⟩
          rw [show ps'.pos - 1 = ps.pos by omega]; exact hdir
        · exact ⟨by omega, hd'⟩
      · have hseg : seg ps.tokens ps.pos ps'.pos = seg ps.tokens ps.pos (ps.pos + 1) ++ seg ps.tokens (ps.pos + 1) ps'.pos :=
          seg_append _ (by omega) p1
        rw [hseg, runToks_append, seg_one ps.tokens hp]
        simp only [runToks, hv]
        rcases ht with ⟨ma, mi, rfl⟩ | ⟨hd, pre, rfl⟩
        · obtain ⟨pending', hr, hsub, hdirs⟩ := r env pending
          refine ⟨pending', by rw [stepTok_neutral rfl]; simpa using hr, hsub, fun hd pre hm => ?_⟩
          rcases hdirs hd pre hm with hm | hm
          · rcases hdirs₂ hd pre hm with hm | hm
            · exact Or.inl hm
            · exact absurd hm (by simp)
          · exact Or.inr hm
        · simp only [stepTok, Option.bind_some]
          split
          · rename_i hnamed
            obtain ⟨pending', hr, hsub, hdirs⟩ := r env (hd :: pending)
            refine ⟨pending', hr, fun x hx => hsub x (List.mem_cons_of_mem _ hx), fun hd' pre' hm => ?_⟩
            rcases hdirs hd' pre' hm with hm | hm
            · rcases hdirs₂ hd' pre' hm with hm | hm
              · exact Or.inl hm
              · cases hm; exact Or.inr (fun _ => hsub _ List.mem_cons_self)
            · exact Or.inr hm
          · rename_i hnamed
            obtain ⟨pending', hr, hsub, hdirs⟩ := r env pending
            refine ⟨pending', hr, hsub, fun hd' pre' hm => ?_⟩
            rcases hdirs hd' pre' hm with hm | hm
            · rcases hdirs₂ hd' pre' hm with hm | hm
              · exact Or.inl hm
              · cases hm; exact Or.inr (fun h => absurd h hnamed)
            · exact Or.inr hm
    cases hpk : ps.peek? with
    | none =>
      simp only [dirBody, hpk, pure, bind, Id.run, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, Nat.le_refl _, by simp, rfl, rfl, Or.inl (by rw [← peek_eq_tok, hpk]; rfl),
        Or.inl ⟨rfl, rfl, Or.inr (by rw [← peek_eq_tok, hpk]; rfl)⟩,
        fun env pending => ⟨pending, by simp [runToks], fun _ h => h, fun _ _ h => Or.inl h⟩⟩
    | some t =>
      cases t
      case versionDirective major minor =>
        simp only [dirBody, hpk, pure, bind, Id.run] at h
        exact hstep _ hpk (Or.inl ⟨major, minor, rfl⟩) _ (fun hd pre hm => by
          simp only [Array.mem_push] at hm
          rcases hm with hm | hm
          · exact Or.inl hm
          · cases hm) h
      case tagDirective hd pre =>
        simp only [dirBody, hpk, pure, bind, Id.run] at h
        exact hstep _ hpk (Or.inr ⟨hd, pre, rfl⟩) _ (fun hd' pre' hm => by
          simp only [Array.mem_push] at hm
          rcases hm with hm | hm
          · exact Or.inl hm
          · cases hm; exact Or.inr rfl) h
      all_goals
        simp only [dirBody, hpk, pure, bind, Id.run, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, Nat.le_refl _, by simp, rfl, rfl, Or.inl (by rw [← peek_eq_tok, hpk]; rfl),
          Or.inl ⟨rfl, rfl, Or.inr (by rw [← peek_eq_tok, hpk]; rfl)⟩,
          fun env pending => ⟨pending, by simp [runToks], fun _ h => h, fun _ _ h => Or.inl h⟩⟩

lemma parseDirectives_cf (ps : ParseState) (dirs : Array Directive) (ps' : ParseState)
    (h : parseDirectives ps = (dirs, ps')) (hsz : ps.pos ≤ ps.tokens.size) :
    ps'.tokens = ps.tokens ∧ ps.pos ≤ ps'.pos ∧ ps'.pos ≤ ps.tokens.size ∧
    ps'.declaredAnchors = ps.declaredAnchors ∧
    isDirectiveTok (tok ps'.tokens ps'.pos) = false ∧
    ((ps'.pos = ps.pos ∧ dirs = #[] ∧ isDirectiveTok (tok ps.tokens ps.pos) = false) ∨
      (ps.pos < ps'.pos ∧ isDirectiveTok (tok ps.tokens (ps'.pos - 1)) = true)) ∧
    ∀ env pending, ∃ pending', runToks (seg ps.tokens ps.pos ps'.pos) (env, pending) = some (env, pending') ∧
      (∀ hd pre, Directive.tag hd pre ∈ dirs → isNamedHandle hd = true → hd ∈ pending') := by
  unfold parseDirectives at h
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one] at h
  have h' : (forIn (List.range' 0 (ps.tokens.size - ps.pos)) (ps, #[]) dirBody : Id _) = (ps', dirs) := by
    obtain ⟨s, hs⟩ : ∃ s, (forIn (List.range' 0 (ps.tokens.size - ps.pos)) (ps, (#[] : Array Directive)) dirBody : Id _) = s := ⟨_, rfl⟩
    have : (s.2, s.1) = (dirs, ps') := by rw [← hs]; exact h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    exact hs
  obtain ⟨t, p1, p2, d, -, nd, lst, r⟩ := dirLoop _ ps #[] ps' dirs h'
  simp only [List.length_range'] at p2 nd
  refine ⟨t, p1, by omega, d, ?_, ?_, fun env pending => ?_⟩
  · rcases nd with nd | nd
    · exact nd
    · have : ps'.pos = ps.tokens.size := by omega
      rw [t, tok, this, Array.getElem?_eq_none (Nat.le_refl _)]; rfl
  · rcases lst with ⟨hp, hd, hl⟩ | h2
    · refine Or.inl ⟨hp, hd, ?_⟩
      rcases hl with hl | hl
      · have : ps.tokens.size - ps.pos = 0 := by simpa using congrArg List.length hl
        rw [tok, Array.getElem?_eq_none (by omega)]; rfl
      · exact hl
    · exact Or.inr h2
  · obtain ⟨pending', hr, -, hdirs⟩ := r env pending
    refine ⟨pending', hr, fun hd pre hm hn => ?_⟩
    rcases hdirs hd pre hm with hm | hm
    · simp at hm
    · exact hm hn


lemma declareAll_mono (env : Env) (l : List String) (x : String) (hx : x ∈ env.tagHandles) :
    x ∈ (declareAll env l).tagHandles := by
  induction l generalizing env with
  | nil => exact hx
  | cons h hs ih => exact ih _ (List.mem_cons_of_mem _ hx)

lemma mem_declareAll (env : Env) (l : List String) (x : String) (hx : x ∈ l) :
    x ∈ (declareAll env l).tagHandles := by
  induction l generalizing env with
  | nil => simp at hx
  | cons h hs ih =>
    simp only [declareAll]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact declareAll_mono _ _ _ List.mem_cons_self
    · exact ih _ hx

lemma tryConsume_eq (ps : ParseState) (t : YamlToken) (b : Bool) (ps' : ParseState)
    (h : ps.tryConsume t = (b, ps')) :
    (b = false ∧ ps' = ps ∧ ps.peek? ≠ some t) ∨
      (b = true ∧ ps.peek? = some t ∧ ps' = ps.advance) := by
  unfold ParseState.tryConsume at h
  split at h
  · rename_i t' hpk
    split at h
    · rename_i hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact Or.inr ⟨rfl, by rw [hpk, eq_of_beq hb], rfl⟩
    · rename_i hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      refine Or.inl ⟨rfl, rfl, fun heq => hb ?_⟩
      rw [hpk] at heq
      cases heq; exact beq_self_eq_true _
  · rename_i hpk
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact Or.inl ⟨rfl, rfl, by rw [hpk]; exact nofun⟩

lemma tryConsume_of_peek (ps : ParseState) (t : YamlToken) (h : ps.peek? = some t) :
    ps.tryConsume t = (true, ps.advance) := by
  unfold ParseState.tryConsume; rw [h]; simp

/-- The document prefix (directives, `---`): the checker's `declareTag` events
are exactly the named `%TAG` handles the parser registers, flushed at `---`.
Capstone 7.7 via S5. -/
lemma prepareDocumentState_cf (ps : ParseState) (dirs : Array Directive) (ps' : ParseState)
    (h : prepareDocumentState ps = .ok (dirs, ps'))
    (hsz : ps.pos ≤ ps.tokens.size) (hD : DirectivesClosed ps.tokens)
    (hdecl : ps.declaredAnchors = #[]) :
    ps'.tokens = ps.tokens ∧ ps.pos ≤ ps'.pos ∧ ps'.pos ≤ ps.tokens.size ∧
    ps'.declaredAnchors = #[] ∧
    (ps'.pos = ps.pos → emptyFollowerTok (tok ps.tokens ps.pos) = true →
      isDirectiveTok (tok ps.tokens ps.pos) = false ∧ tok ps.tokens ps.pos ≠ some .documentStart) ∧
    ∀ s : CS, ∃ s', runToks (seg ps.tokens ps.pos ps'.pos) s = some s' ∧ Rel ps' s' := by
  unfold prepareDocumentState at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hpd : parseDirectives ps = pr at h
  obtain ⟨dirs₀, ps_d⟩ := pr
  obtain ⟨t_d, p1, p2, d_d, nd, lst, r⟩ := parseDirectives_cf ps dirs₀ ps_d hpd hsz
  try dsimp only at h
  generalize htc : ParseState.tryConsume _ YamlToken.documentStart = tc at h
  obtain ⟨b, ps_t⟩ := tc
  try dsimp only at h
  have hmemTH : ∀ q ∈ dirs₀.filterMap (fun d : Directive => match d with
      | .tag handle tagPrefix => some (handle, tagPrefix) | _ => none),
      Directive.tag q.1 q.2 ∈ dirs₀ := by
    intro q hq
    obtain ⟨d, hd, hf⟩ := Array.mem_filterMap.mp hq
    cases d
    case tag h' p' =>
      simp only [Option.some.injEq] at hf
      subst hf; exact hd
    all_goals simp at hf
  rcases tryConsume_eq _ _ _ _ htc with ⟨rfl, rfl, hne⟩ | ⟨rfl, hpkT, rfl⟩
  · -- `---` absent: the directive run must be empty
    have hdirs : dirs₀ = #[] := by
      rcases lst with ⟨-, hd, -⟩ | ⟨hlt, hdir⟩
      · exact hd
      · exfalso
        rcases hD (ps_d.pos - 1) hdir with h1 | h1
        · rw [show ps_d.pos - 1 + 1 = ps_d.pos by omega, ← t_d] at h1
          rw [h1] at nd; exact Bool.noConfusion nd
        · apply hne
          rw [peek_eq_tok]
          show tok ps_d.tokens ps_d.pos = some .documentStart
          rw [t_d, ← h1, show ps_d.pos - 1 + 1 = ps_d.pos by omega]
    subst hdirs
    have hclose : ∀ dirs' ps'', (dirs', ps'') = (dirs, ps') →
        dirs' = (#[] : Array Directive) → ps'' = { ps_d with tagHandles := #[] } →
        ps'.tokens = ps.tokens ∧ ps.pos ≤ ps'.pos ∧ ps'.pos ≤ ps.tokens.size ∧
        ps'.declaredAnchors = #[] ∧
        (ps'.pos = ps.pos → emptyFollowerTok (tok ps.tokens ps.pos) = true →
          isDirectiveTok (tok ps.tokens ps.pos) = false ∧ tok ps.tokens ps.pos ≠ some .documentStart) ∧
        ∀ s : CS, ∃ s', runToks (seg ps.tokens ps.pos ps'.pos) s = some s' ∧ Rel ps' s' := by
      intro dirs' ps'' heq h1 h2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      subst h2
      refine ⟨t_d, p1, p2, by simpa using d_d.trans hdecl, fun hpos _ => ?_, fun s => ?_⟩
      · have hpos' : ps_d.pos = ps.pos := hpos
        refine ⟨?_, ?_⟩
        · rcases lst with ⟨-, -, hd⟩ | ⟨hlt, -⟩
          · exact hd
          · omega
        · intro hds; apply hne
          rw [peek_eq_tok]
          show tok ps_d.tokens ps_d.pos = some .documentStart
          rw [t_d, hpos']; exact hds
      · obtain ⟨pending', hr, -⟩ := r s.1 s.2
        refine ⟨(s.1, pending'), hr, fun n hn => ?_, fun hd _ hp => ?_⟩
        · simp [d_d, hdecl] at hn
        · obtain ⟨q, hq, -⟩ := hp; simp at hq
    split at h
    all_goals (first | contradiction | (split at h <;> first | contradiction | skip) | skip)
    all_goals (first | contradiction | (split at h <;> first | contradiction | skip) | skip)
    all_goals (first | contradiction | (split at h <;> first | contradiction | skip) | skip)
    all_goals (simp only [Except.ok.injEq] at h; exact hclose _ _ h rfl (by simp))
  · -- `---` consumed: flush the pending handles into the fresh environment
    have hlt := pos_lt_of_peek hpkT
    simp only [t_d] at hlt
    have hclose : ∀ dirs' ps'', (dirs', ps'') = (dirs, ps') →
        dirs' = dirs₀ → ps'' = ParseState.advance { ps_d with tagHandles := dirs₀.filterMap (fun d : Directive => match d with
          | .tag handle tagPrefix => some (handle, tagPrefix) | _ => none) } →
        ps'.tokens = ps.tokens ∧ ps.pos ≤ ps'.pos ∧ ps'.pos ≤ ps.tokens.size ∧
        ps'.declaredAnchors = #[] ∧
        (ps'.pos = ps.pos → emptyFollowerTok (tok ps.tokens ps.pos) = true →
          isDirectiveTok (tok ps.tokens ps.pos) = false ∧ tok ps.tokens ps.pos ≠ some .documentStart) ∧
        ∀ s : CS, ∃ s', runToks (seg ps.tokens ps.pos ps'.pos) s = some s' ∧ Rel ps' s' := by
      intro dirs' ps'' heq h1 h2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      subst h2
      simp only [ParseState.advance, Nat.succ_eq_add_one]
      refine ⟨t_d, by omega, by omega, by simpa using d_d.trans hdecl, fun hpos => by omega, fun s => ?_⟩
      obtain ⟨pending', hr, hdirs⟩ := r s.1 s.2
      obtain ⟨q, hq, hv⟩ := peek_some hpkT
      simp only [t_d] at hq hv
      refine ⟨(declareAll s.1.reset pending'.reverse, []), ?_, fun n hn => ?_, fun hd hn hp => ?_⟩
      · rw [seg_append _ p1 (Nat.le_succ _), runToks_append, hr, seg_one _ hq]
        simp [runToks, hv, stepTok]
      · simp [d_d, hdecl] at hn
      · obtain ⟨q', hq', rfl⟩ := hp
        exact mem_declareAll _ _ _ (List.mem_reverse.mpr (hdirs _ _ (hmemTH q' hq') hn))
    split at h
    all_goals (first | contradiction | (split at h <;> first | contradiction | skip) | skip)
    all_goals (first | contradiction | (split at h <;> first | contradiction | skip) | skip)
    all_goals (first | contradiction | (split at h <;> first | contradiction | skip) | skip)
    all_goals (simp only [Except.ok.injEq] at h; exact hclose _ _ h rfl rfl)

/-- One document: prefix, root node, and the stuck analysis (`StuckAt` when
nothing was consumed). Capstone 7.7 via S5. -/
lemma parseDocument_cf (ps : ParseState) (doc : YamlDocument) (ps' : ParseState)
    (h : parseDocument ps = .ok (doc, ps'))
    (hsz : ps.pos ≤ ps.tokens.size) (hD : DirectivesClosed ps.tokens) (hT : TagUsesShaped ps.tokens)
    (hdecl : ps.declaredAnchors = #[]) :
    ps'.tokens = ps.tokens ∧ ps.pos ≤ ps'.pos ∧ ps'.pos ≤ ps.tokens.size ∧
    (ps'.pos = ps.pos → StuckAt ps.tokens ps.pos) ∧
    ∀ s : CS, ∃ s', runToks (seg ps.tokens ps.pos ps'.pos) s = some s' := by
  unfold parseDocument at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i pr hpre
    obtain ⟨dirs, ps_p⟩ := pr
    dsimp only at h
    obtain ⟨t_p, p1, p2, d_p, stuck_p, r_p⟩ := prepareDocumentState_cf ps dirs ps_p hpre hsz hD hdecl
    have hT' : TagUsesShaped ps_p.tokens := t_p ▸ hT
    have hempty : ∀ (hpk : emptyFollowerTok ps_p.peek? = true), ps' = ps_p →
        ps'.tokens = ps.tokens ∧ ps.pos ≤ ps'.pos ∧ ps'.pos ≤ ps.tokens.size ∧
        (ps'.pos = ps.pos → StuckAt ps.tokens ps.pos) ∧
        ∀ s : CS, ∃ s', runToks (seg ps.tokens ps.pos ps'.pos) s = some s' := by
      intro hpk heq; subst heq
      refine ⟨t_p, p1, p2, fun hpos => Or.inl ?_, fun s => ?_⟩
      · rw [peek_eq_tok, t_p, hpos] at hpk; exact hpk
      · obtain ⟨s', hr, -⟩ := r_p s; exact ⟨s', hr⟩
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact hempty (by rename_i hpk; rw [hpk]; rfl) h.2.symm
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact hempty (by rename_i hpk; rw [hpk]; rfl) h.2.symm
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact hempty (by rename_i hpk; rw [hpk]; rfl) h.2.symm
    · split at h
      · simp at h
      · rename_i pn hpn
        obtain ⟨val, ps_n⟩ := pn
        dsimp only at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have hcf := parseNode_cf _ _ _ _ hpn
        refine ⟨hcf.1.trans t_p, Nat.le_trans p1 hcf.2.1, ?_, fun hpos => ?_, fun s => ?_⟩
        · have := hcf.2.2.2.1 (by rw [t_p]; exact p2); rw [t_p] at this; exact this
        · have hpos_p : ps_p.pos = ps.pos := by have := hcf.2.1; omega
          have := parseNode_stuck ps_p _ val ps_n (by omega) hpn (by omega)
          rw [t_p, hpos_p] at this; exact this
        · obtain ⟨s₁, hr₁, hrel⟩ := r_p s
          obtain ⟨s₂, hr₂, -⟩ := hcf.2.2.2.2 hT' s₁ hrel
          refine ⟨s₂, ?_⟩
          rw [seg_append _ p1 hcf.2.1, runToks_append, hr₁, ← t_p]
          exact hr₂

/-- The stream loop: from any position with a clean declaration set, the
checker runs successfully up to where the loop stops (`streamEnd`, end of
input, or a `StuckAt` position). Capstone 7.7 via S5. -/
lemma parseStreamLoop_cf (fuel : Nat) : ∀ (ps : ParseState) (docs : Array YamlDocument)
    (st : StreamState) (docs' : Array YamlDocument),
    parseStreamLoop ps docs st fuel = .ok docs' →
    ps.pos ≤ ps.tokens.size → ps.tokens.size < fuel + ps.pos →
    ps.declaredAnchors = #[] → DirectivesClosed ps.tokens → TagUsesShaped ps.tokens →
    ∀ s : CS, ∃ k s', ps.pos ≤ k ∧ k ≤ ps.tokens.size ∧
      (k = ps.tokens.size ∨ tok ps.tokens k = some .streamEnd ∨ StuckAt ps.tokens k) ∧
      runToks (seg ps.tokens ps.pos k) s = some s' := by
  induction fuel with
  | zero => intro ps _ _ _ _ hsz hf; omega
  | succ fuel ih =>
    intro ps docs st docs' h hsz hf hdecl hD hT s
    unfold parseStreamLoop at h
    split at h
    · rename_i hpk
      exact ⟨ps.pos, s, Nat.le_refl _, hsz, Or.inr (Or.inl (by rw [← peek_eq_tok]; exact hpk)),
        by simp [runToks]⟩
    · rename_i hpk
      have h0 : ps.tokens[ps.pos]? = none := by
        rw [peek_eq_tok] at hpk; unfold tok at hpk
        exact Option.map_eq_none_iff.mp hpk
      have := Array.getElem?_eq_none_iff.mp h0
      exact ⟨ps.pos, s, Nat.le_refl _, hsz, Or.inl (by omega), by simp [runToks]⟩
    · rename_i hpk
      split at h
      rename_i b ps_t htc
      rw [tryConsume_of_peek _ _ hpk] at htc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj htc
      have hlt := pos_lt_of_peek hpk
      obtain ⟨k, s', hk1, hk2, hk3, hr⟩ := ih ps.advance docs .afterDocumentEnd docs' h
        (by simp only [ParseState.advance]; omega) (by simp only [ParseState.advance]; omega)
        hdecl hD hT (s.1.reset, s.2)
      simp only [ParseState.advance] at hk1 hk2 hk3 hr
      refine ⟨k, s', by omega, hk2, hk3, ?_⟩
      obtain ⟨p, hp, hv⟩ := peek_some hpk
      rw [seg_append _ (Nat.le_succ _) hk1, runToks_append, seg_one _ hp]
      simpa [runToks, hv, stepTok] using hr
    · rename_i t hpk
      split at h
      · simp at h
      · generalize hpd : parseDocument ps = pr at h
        rcases pr with e | ⟨doc, ps_d⟩
        · simp at h
        · try dsimp only at h
          obtain ⟨t_d, p1, p2, stuck_d, r_d⟩ := parseDocument_cf ps doc ps_d hpd hsz hD hT hdecl
          generalize htc : ParseState.tryConsume _ YamlToken.documentEnd = tc at h
          obtain ⟨b, ps_t⟩ := tc
          try dsimp only at h
          rcases tryConsume_eq _ _ _ _ htc with ⟨rfl, rfl, -⟩ | ⟨rfl, hpkR, rfl⟩
          · split at h
            · rename_i heqpos
              simp only [beq_iff_eq] at heqpos
              exact ⟨ps.pos, s, Nat.le_refl _, hsz, Or.inr (Or.inr (stuck_d heqpos)), by simp [runToks]⟩
            · rename_i hnepos
              have hlt : ps.pos < ps_d.pos := by
                simp only [beq_iff_eq] at hnepos
                have : ps_d.pos ≠ ps.pos := fun heq => hnepos (by simpa using heq)
                omega
              obtain ⟨s₁, hr₁⟩ := r_d s
              obtain ⟨k, s', hk1, hk2, hk3, hr⟩ := ih _ _ _ docs' h (by simpa [t_d] using p2)
                (by simp only [t_d]; omega) rfl (by simpa [t_d] using hD) (by simpa [t_d] using hT) s₁
              simp only [t_d] at hk1 hk2 hk3 hr
              refine ⟨k, s', by omega, hk2, hk3, ?_⟩
              rw [seg_append _ p1 hk1, runToks_append, hr₁]
              exact hr
          · have hlt := pos_lt_of_peek hpkR
            simp only [t_d] at hlt
            split at h
            · rename_i heqpos
              simp only [beq_iff_eq, ParseState.advance] at heqpos
              omega
            · obtain ⟨s₁, hr₁⟩ := r_d s
              obtain ⟨q, hq, hv⟩ := peek_some hpkR
              simp only [t_d] at hq hv
              obtain ⟨k, s', hk1, hk2, hk3, hr⟩ := ih _ _ _ docs' h
                (by simp only [ParseState.advance, t_d]; omega)
                (by simp only [ParseState.advance, t_d]; omega) rfl
                (by simpa [ParseState.advance, t_d] using hD)
                (by simpa [ParseState.advance, t_d] using hT) (s₁.1.reset, s₁.2)
              simp only [ParseState.advance, t_d] at hk1 hk2 hk3 hr
              refine ⟨k, s', by omega, hk2, hk3, ?_⟩
              rw [seg_append _ p1 (Nat.le_trans (Nat.le_succ _) hk1), runToks_append, hr₁,
                seg_append _ (Nat.le_succ _) hk1]
              show runToks (seg ps.tokens ps_d.pos (ps_d.pos + 1) ++ seg ps.tokens (ps_d.pos + 1) k) s₁ = some s'
              rw [runToks_append, seg_one _ hq]
              simpa [runToks, hv, stepTok] using hr

/-- **S5(→), parser side.** A successful `parseStream` run is well-formed up to
the position `k` where the loop stopped: `checkFrom {} (tokenEvents (ts.extract 0 k))`.
`k` is the end of input, a `streamEnd`, or a `StuckAt` position (the loop's
no-progress exit). Under scanner-shaped tokens (`TagUsesShaped`,
`DirectivesClosed`), the parser's anchor/tag guards compose to the checker.
Capstone 7.7 `parse_iff_grammar` via S5 (EVENTSOF-CONCEPT §9). -/
lemma parseStream_ok_checkFrom (ts : Toks) (docs : Array YamlDocument)
    (hT : TagUsesShaped ts) (hD : DirectivesClosed ts)
    (h : parseStream ts = .ok docs) :
    ∃ k, k ≤ ts.size ∧ (k = ts.size ∨ tok ts k = some .streamEnd ∨ StuckAt ts k) ∧
      checkFrom {} (tokenEvents (ts.extract 0 k)) = true := by
  unfold parseStream at h
  simp only [bind, Except.bind] at h
  generalize hex : ParseState.expect _ YamlToken.streamStart "STREAM-START" = ex at h
  rcases ex with e | ps1
  · simp at h
  · try dsimp only at h
    unfold ParseState.expect at hex
    split at hex
    · rename_i t hpk
      split at hex
      · rename_i hb
        have ht : t = .streamStart := eq_of_beq hb
        subst ht
        simp only [Except.ok.injEq] at hex
        subst hex
        have hlt := pos_lt_of_peek hpk
        simp only at hlt
        obtain ⟨k, s', hk1, hk2, hk3, hr⟩ := parseStreamLoop_cf ts.size _ #[] .initial docs h
          (by simp only [ParseState.advance]; omega) (by simp only [ParseState.advance]; omega)
          rfl hD hT ({}, [])
        simp only [ParseState.advance, Nat.succ_eq_add_one] at hk1 hk2 hk3 hr
        refine ⟨k, hk2, hk3, ?_⟩
        obtain ⟨p, hp, hv⟩ := peek_some hpk
        simp only at hp hv
        have hall : runToks (seg ts 0 k) ({}, []) = some s' := by
          rw [seg_append _ (Nat.zero_le _) hk1, runToks_append, seg_one _ hp]
          simpa [runToks, hv, stepTok] using hr
        unfold tokenEvents
        rw [← seg_zero_eq, checkFrom_go_iff, hall]
        rfl
      · simp at hex
    · simp at hex

/-- **S5(→) over `parseYaml`.** For every input the scanner-then-parser
pipeline accepts, the parser's serialization check equals the event checker's
on the consumed token prefix. The scanner-shape premises are the token-level
facts the scanner guarantees but which are not yet lemmas (S3's territory);
`k = tokens.size` follows once the scanner side supplies `TokenGrammar`'s
`streamEnd`-last shape. Capstone 7.7 `parse_iff_grammar` via S5. -/
lemma parse_ok_checkFrom (input : String) (docs : Array YamlDocument)
    (h : parseYaml input = .ok docs) :
    ∃ tokens, Scanner.scanFiltered input = .ok tokens ∧ (∃ raw, parseStream tokens = .ok raw) ∧
      (TagUsesShaped tokens → DirectivesClosed tokens →
        ∃ k, k ≤ tokens.size ∧ (k = tokens.size ∨ tok tokens k = some .streamEnd ∨ StuckAt tokens k) ∧
          checkFrom {} (tokenEvents (tokens.extract 0 k)) = true) := by
  unfold parseYaml parseYamlRaw at h
  split at h
  · rename_i raw hraw
    split at hraw
    · rename_i tokens hs
      exact ⟨tokens, hs, ⟨raw, hraw⟩, fun hT hD => parseStream_ok_checkFrom tokens raw hT hD hraw⟩
    · simp at hraw
  · simp at h

end L4YAML.Proofs.Serialization.ParseCheckFrom

end Blanket
