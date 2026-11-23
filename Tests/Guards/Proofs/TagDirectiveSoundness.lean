/-
Group 7.7 / YAML §6.8.2: the repaired real parser enforces uniqueness of
explicit TAG declarations in every successfully returned document.
The property is the independent per-document List.Nodup requirement;
the proof follows actual document and stream consumers without scanner
acceptance or grammar correctness assumptions.
-/
module
public import L4YAML.Parser.Composition
public import L4YAML.Parser.IndexedComposition

@[expose] public section
namespace L4YAML.Tests.Guards.TagDirectiveSoundness
open L4YAML
open L4YAML.TokenParser

lemma duplicate_directives_refused (ps : ParseState)
    (h : ¬ TagDirectivesUnique (parseDirectives ps).1) :
    prepareDocumentState ps = .error .duplicateTagDirective := by
  simp [prepareDocumentState, h, bind, Except.bind]
  rfl

lemma duplicate_directives_refused_ix {input : String}
    (ps : Indexed.ParseStateIx input)
    (h : ¬ TagDirectivesUnique (Indexed.parseDirectives ps).1) :
    Indexed.prepareDocumentState ps = .error .duplicateTagDirective := by
  simp [Indexed.prepareDocumentState, h, bind, Except.bind]
  rfl

lemma prepared_directives_unique (ps : ParseState) (dirs : Array Directive)
    (ps' : ParseState) (h : prepareDocumentState ps = .ok (dirs, ps')) :
    TagDirectivesUnique dirs := by
  unfold prepareDocumentState at h
  generalize he : parseDirectives ps = result at h
  rcases result with ⟨ds, st⟩
  by_cases hu : TagDirectivesUnique ds
  · simp only [hu, decide_true, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, bind, Except.bind] at h
    repeat' split at h
    all_goals simp_all
  · simp [hu, bind, Except.bind] at h

lemma document_directives_unique (ps : ParseState) (doc : YamlDocument)
    (ps' : ParseState) (h : parseDocument ps = .ok (doc, ps')) :
    TagDirectivesUnique doc.directives := by
  unfold parseDocument at h
  cases hp : prepareDocumentState ps with
  | error e => simp [hp, bind, Except.bind] at h
  | ok v =>
    rcases v with ⟨dirs, ps1⟩
    have hu := prepared_directives_unique ps dirs ps1 hp
    simp only [hp, bind, Except.bind] at h
    split at h
    all_goals first
      | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
         rcases h with ⟨rfl, rfl⟩
         exact hu)
      | (cases hn : parseNode ps1 (4 * ps1.tokens.size + 4) with
         | error e => simp [hn] at h
         | ok v =>
           rcases v with ⟨val, ps2⟩
           simp only [hn, Except.ok.injEq, Prod.mk.injEq] at h
           rcases h with ⟨rfl, rfl⟩
           exact hu)

def DocumentsUnique (docs : Array YamlDocument) : Prop :=
  ∀ doc ∈ docs.toList, TagDirectivesUnique doc.directives

lemma stream_loop_directives_unique (fuel : Nat) (ps : ParseState)
    (docs result : Array YamlDocument) (st : StreamState)
    (hacc : DocumentsUnique docs)
    (h : parseStreamLoop ps docs st fuel = .ok result) : DocumentsUnique result := by
  induction fuel generalizing ps docs st with
  | zero =>
    simp only [parseStreamLoop, Except.ok.injEq] at h
    subst result
    exact hacc
  | succ fuel ih =>
    unfold parseStreamLoop at h
    split at h
    · cases h; exact hacc
    · cases h; exact hacc
    · exact ih _ _ _ hacc h
    · split at h
      · simp at h
      · dsimp only [] at h
        cases hp : parseDocument ps with
        | error e => simp [hp] at h
        | ok v =>
          rcases v with ⟨doc, ps'⟩
          have hu := document_directives_unique ps doc ps' hp
          have hacc' : DocumentsUnique (docs.push doc) := by
            intro d hd
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hd
            rcases hd with hd | rfl
            · exact hacc d hd
            · exact hu
          simp only [hp] at h
          split at h
          · simp at h
          · exact ih _ _ _ hacc' h

lemma parseStream_directives_unique (ts : Array (Positioned YamlToken))
    (track : Bool) (docs : Array YamlDocument)
    (h : parseStream ts track = .ok docs) : DocumentsUnique docs := by
  unfold parseStream at h
  cases hp : (ParseState.expect
      { tokens := ts, trackPositions := track } .streamStart "STREAM-START") with
  | error e => simp [hp, bind, Except.bind] at h
  | ok ps =>
    simp only [hp, bind, Except.bind] at h
    exact stream_loop_directives_unique ts.size ps #[] docs .initial
      (by simp [DocumentsUnique]) h

lemma parseYamlRaw_directives_unique (input : String) (docs : Array YamlDocument)
    (h : parseYamlRaw input = .ok docs) : DocumentsUnique docs := by
  unfold parseYamlRaw at h
  cases hs : Scanner.scanFiltered input with
  | error e => simp [hs] at h
  | ok ts =>
    simp only [hs] at h
    exact parseStream_directives_unique ts false docs h

lemma parseYaml_directives_unique (input : String) (docs : Array YamlDocument)
    (h : parseYaml input = .ok docs) : DocumentsUnique docs := by
  unfold parseYaml at h
  cases hp : parseYamlRaw input with
  | error e => simp [hp] at h
  | ok raw =>
    simp only [hp, Except.ok.injEq] at h
    subst docs
    have hu := parseYamlRaw_directives_unique input raw hp
    intro doc hd
    simp only [Array.toList_map, List.mem_map] at hd
    rcases hd with ⟨d, hd, rfl⟩
    exact hu d hd

#print axioms duplicate_directives_refused
#print axioms duplicate_directives_refused_ix
#print axioms parseStream_directives_unique
#print axioms parseYamlRaw_directives_unique
#print axioms parseYaml_directives_unique

end L4YAML.Tests.Guards.TagDirectiveSoundness
end
