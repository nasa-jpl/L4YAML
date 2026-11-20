/-
Group 7.7 / YAML §6.8.2: the repaired indexed parser enforces uniqueness
of explicit TAG declarations in every successfully returned document.
This mirrors the classic parser argument through the actual indexed
document and stream consumers, with no scanner or grammar assumptions.
-/
module
public import Tests.Guards.Proofs.TagDirectiveSoundness

@[expose] public section
namespace L4YAML.Tests.Guards.TagDirectiveSoundnessIx
open L4YAML
open L4YAML.TokenParser.Indexed
open L4YAML.Tests.Guards.TagDirectiveSoundness (DocumentsUnique)

lemma prepared_directives_unique {input : String} (ps : ParseStateIx input)
    (dirs : Array Directive) (ps' : ParseStateIx input)
    (h : prepareDocumentState ps = .ok (dirs, ps')) :
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

lemma document_directives_unique {input : String} (ps : ParseStateIx input)
    (doc : YamlDocument) (ps' : ParseStateIx input)
    (h : parseDocument ps = .ok (doc, ps')) :
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

lemma stream_loop_directives_unique {input : String} (fuel : Nat)
    (ps : ParseStateIx input) (docs result : Array YamlDocument)
    (st : StreamState) (hacc : DocumentsUnique docs)
    (h : parseStreamLoop ps docs st fuel = .ok result) :
    DocumentsUnique result := by
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

lemma parseStreamIx_directives_unique {input : String}
    (ts : L4YAML.Indexed.TokenStream input) (track : Bool)
    (docs : Array YamlDocument) (h : parseStreamIx ts track = .ok docs) :
    DocumentsUnique docs := by
  unfold parseStreamIx at h
  cases hp : (ParseStateIx.expect
      { tokens := ts, trackPositions := track } .streamStart "STREAM-START") with
  | error e => simp [hp, bind, Except.bind] at h
  | ok ps =>
    simp only [hp, bind, Except.bind] at h
    exact stream_loop_directives_unique ts.size ps #[] docs .initial
      (by simp [DocumentsUnique]) h

lemma parseYamlRawIx_directives_unique (input : String)
    (docs : Array YamlDocument) (h : parseYamlRawIx input = .ok docs) :
    DocumentsUnique docs := by
  unfold parseYamlRawIx scanAndParseIx at h
  cases hs : Scanner.Indexed.ScannerStateIx.scanFilteredIx input with
  | error e => simp [hs] at h
  | ok ts =>
    simp only [hs] at h
    exact parseStreamIx_directives_unique ts false docs h

lemma parseYamlIx_directives_unique (input : String) (docs : Array YamlDocument)
    (h : parseYamlIx input = .ok docs) : DocumentsUnique docs := by
  unfold parseYamlIx at h
  cases hp : parseYamlRawIx input with
  | error e => simp [hp] at h
  | ok raw =>
    simp only [hp, Except.ok.injEq] at h
    subst docs
    have hu := parseYamlRawIx_directives_unique input raw hp
    intro doc hd
    simp only [Array.toList_map, List.mem_map] at hd
    rcases hd with ⟨d, hd, rfl⟩
    exact hu d hd

#print axioms prepared_directives_unique
#print axioms document_directives_unique
#print axioms stream_loop_directives_unique
#print axioms parseStreamIx_directives_unique
#print axioms parseYamlRawIx_directives_unique
#print axioms parseYamlIx_directives_unique

end L4YAML.Tests.Guards.TagDirectiveSoundnessIx
end
