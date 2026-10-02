import L4YAML.Parser.State
import L4YAML.Proofs.Serialization.SerializationWellFormed

/-!
# Executable anchor-commitment bridge

The independent semantics places anchor commitment at node completion.
L4YAML's `applyNodeFinalization` calls `addAnchor` in its node-finalization
tail. This file proves the name-set effect of that operation directly.

The lemmas here do not establish a whole-parser trace theorem or show that
every earlier parser state lacks the pending name. That correspondence remains
open alongside the input-to-event extraction theorem.
-/

namespace L4YAMLSerializationAnchorRuntime

open L4YAML
open L4YAML.TokenParser
open L4YAMLSerializationWellFormed

lemma addAnchor_name_projection
    (ps : ParseState) (name : String) (val : YamlValue) :
    (ofParserAliases (ps.addAnchor name val)).anchors =
      (ofParserAliases ps).anchors ++ [name] := by
  simp [ofParserAliases, ParseState.addAnchor, Array.toList_push]

lemma addAnchor_authorizes_name
    (ps : ParseState) (name : String) (val : YamlValue) :
    AliasAllowed (ofParserAliases (ps.addAnchor name val)) name := by
  simp [AliasAllowed, addAnchor_name_projection]

lemma addAnchor_preserves_old_names
    (ps : ParseState) (name old : String) (val : YamlValue)
    (h : AliasAllowed (ofParserAliases ps) old) :
    AliasAllowed (ofParserAliases (ps.addAnchor name val)) old := by
  simp only [AliasAllowed] at h ⊢
  rw [addAnchor_name_projection]
  exact List.mem_append_left _ h

/-- If finalization has an anchor property, the output parser state contains
that anchor name.  This pins the independent defineAnchor event to the actual
executable node-completion operation. -/
lemma applyNodeFinalization_commits_anchor
    (val : YamlValue) (ps : ParseState) (name : String)
    (tag : Option String) (dup : Bool) (start : YamlPos) :
    AliasAllowed
      (ofParserAliases
        (applyNodeFinalization val ps
          { anchor := some name, tag := tag, hadDuplicateAnchor := dup } start).2)
      name := by
  unfold applyNodeFinalization
  split <;> simp only
  all_goals
    split <;> simp [AliasAllowed, ofParserAliases, ParseState.addAnchor,
      Array.toList_push]

/-- With no anchor property, finalization does not change the alias-name
projection. -/
lemma applyNodeFinalization_no_anchor_projection
    (val : YamlValue) (ps : ParseState)
    (tag : Option String) (dup : Bool) (start : YamlPos) :
    (ofParserAliases
      (applyNodeFinalization val ps
        { anchor := none, tag := tag, hadDuplicateAnchor := dup } start).2).anchors =
      (ofParserAliases ps).anchors := by
  unfold applyNodeFinalization
  split <;> simp only
  all_goals
    split <;> rfl

end L4YAMLSerializationAnchorRuntime

#print axioms L4YAMLSerializationAnchorRuntime.addAnchor_name_projection
#print axioms L4YAMLSerializationAnchorRuntime.applyNodeFinalization_commits_anchor
#print axioms L4YAMLSerializationAnchorRuntime.applyNodeFinalization_no_anchor_projection
