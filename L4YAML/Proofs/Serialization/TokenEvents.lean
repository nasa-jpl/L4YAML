/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Token.Token
public import L4YAML.Proofs.Serialization.SerializationWellFormed

public meta import L4YAML.Token.Token
public meta import L4YAML.Proofs.Serialization.SerializationWellFormed

/-!
# Serialization events of a token stream (EVENTSOF-CONCEPT §9, S2)

`tokenEvents` reads the scanner's token stream the way `eventsOfSegs` reads a
lexical skeleton: anchors, aliases and shorthand tags become events in stream
order, `documentEnd` is `endDocument`, and `documentStart` is `beginDocument`
followed by the `%TAG` directives scanned before it (`RuntimeScopes.documentEvents`
pins that order: the directives belong to the document the reset opens).

It is executable and mentions no `Prop`; S3 proves the scan's skeleton witness
has exactly this trace, S5 relates it to the parser's own anchor/tag checks.
-/

namespace L4YAML.Proofs.Serialization.TokenEvents

public section

open L4YAML.Proofs.Serialization.SerializationWellFormed

/-- The event a single token contributes, if any; directives and document
starts are handled by `tokenEvents` because their order is not local. -/
@[expose] def tokenEvent : YamlToken → Option Event
  | .anchor name => some (.defineAnchor name)
  | .alias name => some (.useAlias name)
  | .tag handle _ => if handle.isEmpty then none else some (.useTag handle)
  | .documentEnd => some .endDocument
  | _ => none

/-- `[89] c-named-tag-handle`: `!` word-chars `!`.  The scanner copies a `%TAG`
handle without checking its closing `!`, so `%TAG !h …` scans; a handle of that
shape can never be used (every shorthand use is `!`, `!!` or `!…!`), and the
skeleton's `declaredHandle` declares nothing for it — nor does this. -/
@[expose] def isNamedHandle (h : String) : Bool :=
  match h.toList with
  | '!' :: rest => rest.length ≥ 2 && rest.getLast? == some '!' &&
      rest.dropLast.all (fun c => c.isAlphanum || c = '-')
  | _ => false

#guard isNamedHandle "!e!" = true
#guard isNamedHandle "!my-tag!" = true
#guard isNamedHandle "!" = false
#guard isNamedHandle "!!" = false
#guard isNamedHandle "!h" = false
#guard isNamedHandle "!a b!" = false

/-! The leaf bridge (`TraceOf/LeafBridge.lean`) reads `tokenEvent` through these equations. -/

@[simp] lemma tokenEvent_anchor (name : String) :
    tokenEvent (.anchor name) = some (.defineAnchor name) := rfl

@[simp] lemma tokenEvent_alias (name : String) :
    tokenEvent (.alias name) = some (.useAlias name) := rfl

@[simp] lemma tokenEvent_tag (handle suffix : String) :
    tokenEvent (.tag handle suffix) = if handle.isEmpty then none else some (.useTag handle) := rfl

/-- Fold over the stream with the named `%TAG` handles pending until the next
`documentStart`; handles still pending at the end are emitted there.  `!` and
`!!` are builtin (`TagHandleAllowed`) and malformed handles are unusable, so
neither is an event — the same reading as the skeleton's `declaredHandle`. -/
def go : List (Positioned YamlToken) → List String → List Event
  | [], pending => pending.reverse.map .declareTag
  | t :: ts, pending =>
    match t.val with
    | .tagDirective handle _ =>
      if isNamedHandle handle then go ts (handle :: pending) else go ts pending
    | .documentStart => .beginDocument :: (pending.reverse.map .declareTag ++ go ts [])
    | v => match tokenEvent v with
      | some e => e :: go ts pending
      | none => go ts pending

def tokenEvents (tokens : Array (Positioned YamlToken)) : List Event :=
  go tokens.toList []

/-- A token at a default position, for the guards. -/
def tok (v : YamlToken) : Positioned YamlToken := ⟨default, v, default⟩

#guard tokenEvents #[] = []
#guard tokenEvents #[tok (.anchor "x"), tok (.alias "x")] =
  [.defineAnchor "x", .useAlias "x"]
#guard tokenEvents #[tok (.tagDirective "!" "!x"), tok (.documentStart), tok (.tag "!" "a")] =
  [.beginDocument, .useTag "!"]
#guard tokenEvents #[tok (.tag "" "tag:x")] = []
#guard tokenEvents #[tok (.documentEnd), tok (.documentStart)] = [.endDocument, .beginDocument]
#guard tokenEvents #[tok (.tagDirective "!h!" "p")] = [.declareTag "!h!"]
#guard tokenEvents #[tok (.tagDirective "!" "p"), tok (.tagDirective "!!" "q"), tok .documentStart] = [.beginDocument]
#guard tokenEvents #[tok (.tagDirective "!h" "p"), tok .documentStart] = [.beginDocument]

/-! ## The algebra of `go` (S3 slice (2), item 462)

`go` is a fold with one piece of state, the named `%TAG` handles pending until the next
`---`.  `goOut` is the same fold returning that state instead of flushing it, so a token
list splits anywhere: `go (l₁ ++ l₂) p = (goOut l₁ p).1 ++ go l₂ (goOut l₁ p).2`.  The
scanner-arm bridges (`TraceOf/DocBridge.lean`) read the tokens an arm pushes through
`goOut`. -/

/-- `go` without the final flush: the events of `l` from pending `p`, and what is still
pending after `l`. -/
@[expose] def goOut : List (Positioned YamlToken) → List String → List Event × List String
  | [], pending => ([], pending)
  | t :: ts, pending =>
    match t.val with
    | .tagDirective handle _ =>
      goOut ts (if isNamedHandle handle then handle :: pending else pending)
    | .documentStart =>
      let r := goOut ts []
      (.beginDocument :: (pending.reverse.map .declareTag ++ r.1), r.2)
    | v =>
      let r := goOut ts pending
      match tokenEvent v with
      | some e => (e :: r.1, r.2)
      | none => r

/-- `go` is `goOut` followed by the flush of what is still pending. -/
lemma go_eq_goOut (l : List (Positioned YamlToken)) (p : List String) :
    go l p = (goOut l p).1 ++ (goOut l p).2.reverse.map .declareTag := by
  induction l generalizing p with
  | nil => simp [go, goOut]
  | cons t ts ih =>
    obtain ⟨_, v, _⟩ := t
    cases v <;> simp [go, goOut, tokenEvent, ih]
    all_goals (try (split <;> simp [ih]))
    all_goals (try (rename_i handle _; by_cases h : handle = "" <;> simp [h, ih]))

lemma goOut_append (l₁ l₂ : List (Positioned YamlToken)) (p : List String) :
    goOut (l₁ ++ l₂) p =
      ((goOut l₁ p).1 ++ (goOut l₂ (goOut l₁ p).2).1, (goOut l₂ (goOut l₁ p).2).2) := by
  induction l₁ generalizing p with
  | nil => simp [goOut]
  | cons t ts ih =>
    obtain ⟨_, v, _⟩ := t
    cases v <;> simp [goOut, tokenEvent, ih]
    all_goals (try (split <;> simp [ih]))
    all_goals (try (rename_i handle _; by_cases h : handle = "" <;> simp [h, ih]))

/-- The split law: the events of `l₁ ++ l₂` are those of `l₁`, then those of `l₂` from
the handles `l₁` left pending. -/
lemma go_append (l₁ l₂ : List (Positioned YamlToken)) (p : List String) :
    go (l₁ ++ l₂) p = (goOut l₁ p).1 ++ go l₂ (goOut l₁ p).2 := by
  rw [go_eq_goOut, goOut_append, go_eq_goOut]; simp [List.append_assoc]

lemma tokenEvents_eq_goOut (ts : Array (Positioned YamlToken)) :
    tokenEvents ts =
      (goOut ts.toList []).1 ++ (goOut ts.toList []).2.reverse.map .declareTag :=
  go_eq_goOut _ _

@[simp] lemma goOut_nil (p : List String) : goOut [] p = ([], p) := rfl

/-- `---` emits `beginDocument`, then the pending handles as `declareTag` in directive
order, and the handles are cleared. -/
lemma goOut_documentStart (t : Positioned YamlToken) (ht : t.val = .documentStart)
    (ts : List (Positioned YamlToken)) (p : List String) :
    goOut (t :: ts) p =
      (.beginDocument :: (p.reverse.map .declareTag ++ (goOut ts []).1), (goOut ts []).2) := by
  obtain ⟨_, v, _⟩ := t; simp only at ht; subst ht; rfl

/-- `...` emits `endDocument`; the pending handles are untouched. -/
lemma goOut_documentEnd (t : Positioned YamlToken) (ht : t.val = .documentEnd)
    (ts : List (Positioned YamlToken)) (p : List String) :
    goOut (t :: ts) p = (.endDocument :: (goOut ts p).1, (goOut ts p).2) := by
  obtain ⟨_, v, _⟩ := t; simp only at ht; subst ht; rfl

/-- A `%TAG` directive emits nothing; its handle is pending iff it is named. -/
lemma goOut_tagDirective (t : Positioned YamlToken) (handle pfx : String)
    (ht : t.val = .tagDirective handle pfx)
    (ts : List (Positioned YamlToken)) (p : List String) :
    goOut (t :: ts) p = goOut ts (if isNamedHandle handle then handle :: p else p) := by
  obtain ⟨_, v, _⟩ := t; simp only at ht; subst ht; rfl

/-- A token without an event, other than the two above, is invisible to `goOut`. -/
lemma goOut_silent (t : Positioned YamlToken) (hev : tokenEvent t.val = none)
    (hds : t.val ≠ .documentStart) (htd : ∀ h pfx, t.val ≠ .tagDirective h pfx)
    (ts : List (Positioned YamlToken)) (p : List String) :
    goOut (t :: ts) p = goOut ts p := by
  obtain ⟨_, v, _⟩ := t
  cases v <;> simp_all [goOut, tokenEvent]

/-- `blockEnd`s are silent: what `unwindIndents` pushes before a marker. -/
lemma goOut_blockEnds (ends : List (Positioned YamlToken))
    (hends : ∀ t ∈ ends, t.val = .blockEnd) (ts : List (Positioned YamlToken)) (p : List String) :
    goOut (ends ++ ts) p = goOut ts p := by
  induction ends with
  | nil => rfl
  | cons t rest ih =>
    rw [List.cons_append, goOut_silent t (by rw [hends t (by simp)]; rfl)
      (by rw [hends t (by simp)]; simp) (by intro h pfx; rw [hends t (by simp)]; simp)]
    exact ih (fun u hu => hends u (by simp [hu]))

#guard goOut [tok .documentStart] ["!e!"] = ([.beginDocument, .declareTag "!e!"], [])
#guard goOut [tok (.tagDirective "!e!" "p"), tok (.tagDirective "!" "q")] [] = ([], ["!e!"])
#guard goOut [tok .documentEnd] ["!e!"] = ([.endDocument], ["!e!"])
#guard goOut [tok .blockEnd, tok .blockEnd, tok .documentStart] ["!b!", "!a!"] =
  ([.beginDocument, .declareTag "!a!", .declareTag "!b!"], [])

end

end L4YAML.Proofs.Serialization.TokenEvents
