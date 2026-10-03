import L4YAML.Parser.TokenParser
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Serialization.SerializationWellFormed

/-!
# Runtime document-scope bridges

The independent semantics resets anchor and custom-tag state at document
boundaries.  This file pins the corresponding executable scope facts:

* scanner document-start resets its anchor-name environment;
* parser document preparation replaces (rather than extends) its tag-handle
  table with the declarations of the current document.

These are family-level facts; no fixed-input evaluation is used.
-/

namespace L4YAMLSerializationRuntimeScopes

open L4YAML
open L4YAMLSerializationWellFormed

lemma scanner_document_start_resets_aliases
    (s : L4YAML.Scanner.ScannerState) :
    (ofScannerAliases (L4YAML.Scanner.scanDocumentStart s)).anchors = [] := by
  rfl

def tagTableOfDirectives (dirs : Array Directive) : Array (String × String) :=
  dirs.filterMap fun
    | .tag handle tagPrefix => some (handle, tagPrefix)
    | _ => none

lemma tryConsume_tagHandles
    (ps : L4YAML.TokenParser.ParseState) (tok : YamlToken) :
    (ps.tryConsume tok).2.tagHandles = ps.tagHandles := by
  unfold L4YAML.TokenParser.ParseState.tryConsume
  split
  · split <;> rfl
  · rfl

/-- On every successful document preparation, the parser's handle table is
exactly the declarations parsed for that document.  Any handle table inherited
in the input state is overwritten. -/
lemma prepareDocumentState_tagHandles_exact
    (ps : L4YAML.TokenParser.ParseState)
    (dirs : Array Directive)
    (ps' : L4YAML.TokenParser.ParseState)
    (h_ok : L4YAML.TokenParser.prepareDocumentState ps = .ok (dirs, ps')) :
    ps'.tagHandles = tagTableOfDirectives dirs := by
  unfold L4YAML.TokenParser.prepareDocumentState at h_ok
  simp only [bind, Except.bind] at h_ok
  all_goals (first | split at h_ok | skip)
  all_goals (first | split at h_ok | skip)
  all_goals (first | split at h_ok | skip)
  all_goals (first | split at h_ok | skip)
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq, Prod.mk.injEq] at h_ok)
  all_goals (
    obtain ⟨hdirs, rfl⟩ := h_ok
    calc
      _ = tagTableOfDirectives (L4YAML.TokenParser.parseDirectives ps).1 :=
        tryConsume_tagHandles
          ({ (L4YAML.TokenParser.parseDirectives ps).2 with
              tagHandles :=
                tagTableOfDirectives (L4YAML.TokenParser.parseDirectives ps).1 })
          (.documentStart : YamlToken)
      _ = tagTableOfDirectives dirs :=
        congrArg tagTableOfDirectives hdirs)

/-- The minimal semantic projection after successful document preparation
therefore contains exactly the names declared in the current document. -/
lemma prepareDocumentState_tag_projection_exact
    (ps : L4YAML.TokenParser.ParseState)
    (dirs : Array Directive)
    (ps' : L4YAML.TokenParser.ParseState)
    (h_ok : L4YAML.TokenParser.prepareDocumentState ps = .ok (dirs, ps')) :
    (ofParserTags ps').tagHandles =
      (tagTableOfDirectives dirs).toList.map Prod.fst := by
  rw [ofParserTags, prepareDocumentState_tagHandles_exact ps dirs ps' h_ok]

end L4YAMLSerializationRuntimeScopes

#print axioms L4YAMLSerializationRuntimeScopes.scanner_document_start_resets_aliases
#print axioms L4YAMLSerializationRuntimeScopes.prepareDocumentState_tagHandles_exact
