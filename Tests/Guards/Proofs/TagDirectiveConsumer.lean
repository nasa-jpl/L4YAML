/-
Concrete qualification of the repaired Group 7.7 token-completeness consumer.
The positive premises come from the actual scanner output and independent
grammar/state checkers. The negative grammar result inspects TG derivations;
it does not infer non-membership merely from a failed sound-only checker.
-/
module
public import L4YAML.Proofs.Parser.StreamCompleteness
public import L4YAML.Parser.Composition
public import Tests.Guards.Proofs.TagDirectiveRepair
public meta import L4YAML.Proofs.Parser.TokenGrammar
public meta import L4YAML.Parser.Composition
public meta import Tests.Guards.Proofs.TagDirectiveRepair
import all Init.Data.Range.Basic
import all L4YAML.Proofs.Serialization.TokenEvents

@[expose] public section
namespace L4YAML.Tests.Guards.TagDirectiveConsumer

open L4YAML
open L4YAML.Proofs.TokenGrammar
open L4YAML.Proofs.Serialization.SerializationWellFormed

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

def singleInput : String := "%TAG ! !x\n--- a"
def duplicateInput : String := "%TAG ! !x\n%TAG ! !x\n--- a"

def singleTokens : Toks := (Scanner.scanFiltered singleInput).toOption.getD #[]
def duplicateTokens : Toks := (Scanner.scanFiltered duplicateInput).toOption.getD #[]

lemma single_scan : Scanner.scanFiltered singleInput = .ok singleTokens := by cbv
lemma duplicate_scan : Scanner.scanFiltered duplicateInput = .ok duplicateTokens := by cbv

lemma single_tokenGrammar : TokenGrammar singleTokens :=
  checkTokenGrammar_sound (by cbv)

lemma single_tokenStateOk : TokenStateOk singleTokens := by
  apply (serializationWellFormed_iff_check _).2
  cbv

/-- Both corrected premises hold on real scanner output, and the actual
completeness consumer establishes parser acceptance from them. -/
lemma single_consumer : ∃ docs, TokenParser.parseStream singleTokens = .ok docs :=
  parseStream_accepts singleTokens single_tokenGrammar single_tokenStateOk

/-- The consumer composes with the actual scanner equality to reach the public
raw pipeline, without assuming or directly computing parser acceptance. -/
lemma single_pipeline : ∃ docs, TokenParser.parseYamlRaw singleInput = .ok docs := by
  obtain ⟨docs, hp⟩ := single_consumer
  refine ⟨docs, ?_⟩
  unfold TokenParser.parseYamlRaw
  rw [single_scan]
  exact hp

lemma duplicate_not_tokenGrammar : ¬ TokenGrammar duplicateTokens := by
  intro ⟨_, j, hs, _⟩
  have hfirst : tok duplicateTokens 1 = some (.tagDirective "!" "!x") := by cbv
  obtain ⟨m, hdoc⟩ : ∃ m, TG duplicateTokens .document 1 m := by
    cases hs with
    | stream_end h => rcases h with h | h <;> simp [hfirst] at h
    | stream_docEnd h _ => simp [hfirst] at h
    | stream_doc _ _ _ _ hd _ _ _ => exact ⟨_, hd⟩
    | stream_docTerminated _ _ _ _ hd _ _ => exact ⟨_, hd⟩
  cases hdoc with
  | document hd hunique hstart hnode =>
    rename_i d e
    have hdir1 : isDirective (tok duplicateTokens 1) = true := by cbv
    have hdir2 : isDirective (tok duplicateTokens 2) = true := by cbv
    have hdir3 : isDirective (tok duplicateTokens 3) = false := by cbv
    have hend : d = 3 := by
      cases hd with
      | directives_nil hn => simp [hdir1] at hn
      | directives_cons _ hd2 =>
        cases hd2 with
        | directives_nil hn => simp [hdir2] at hn
        | directives_cons _ hd3 =>
          cases hd3 with
          | directives_nil _ => rfl
          | directives_cons hn _ => simp [hdir3] at hn
    subst hend
    exact (by cbv; decide : ¬ DirectiveHandlesUnique duplicateTokens 1 3) hunique

#guard checkTokenGrammar singleTokens
#guard !checkTokenGrammar duplicateTokens

-- The oracle labels come from handle equality and document scope. These cases
-- cover builtin/named handles, equal/different prefixes, and document resets.
#guard TagDirectiveRepair.directivePairs.all (fun (s, expected) =>
  match Scanner.scanFiltered s with
  | .ok ts => checkTokenGrammar ts == expected
  | .error _ => false)

#print axioms L4YAML.Proofs.TokenGrammar.parseStream_accepts
#print axioms L4YAML.Proofs.TokenGrammar.checkTokenGrammar_sound
#print axioms single_scan
#print axioms duplicate_scan
#print axioms single_tokenGrammar
#print axioms single_tokenStateOk
#print axioms single_consumer
#print axioms single_pipeline
#print axioms duplicate_not_tokenGrammar

end L4YAML.Tests.Guards.TagDirectiveConsumer
end
