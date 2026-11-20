/-
Group 7.7 admission regression for YAML 1.2.2 §6.8.2.
The external requirement counts explicit TAG handles per document, including
the builtin handles, irrespective of their prefixes. These controls exercise
the real classic and indexed public APIs before the universal proof below.
-/
module
public import L4YAML.Parser.Composition
public import L4YAML.Parser.IndexedComposition
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Parser.IndexedComposition

@[expose] public section
namespace L4YAML.Tests.Guards.TagDirectiveRepair
open L4YAML

def duplicateError {α : Type} : Except ScanError α → Bool
  | .error .duplicateTagDirective => true
  | _ => false

def apiVerdicts (s : String) : List Bool :=
  [(TokenParser.parseYamlRaw s).isOk,
   (TokenParser.parseYaml s).isOk,
   (TokenParser.parseYamlWithComments s).isOk,
   (TokenParser.Indexed.parseYamlRawIx s).isOk,
   (TokenParser.Indexed.parseYamlIx s).isOk,
   (TokenParser.Indexed.parseYamlWithCommentsIx s).isOk]

def apiDuplicateErrors (s : String) : List Bool :=
  [duplicateError (TokenParser.parseYamlRaw s),
   duplicateError (TokenParser.parseYaml s),
   duplicateError (TokenParser.parseYamlWithComments s),
   duplicateError (TokenParser.Indexed.parseYamlRawIx s),
   duplicateError (TokenParser.Indexed.parseYamlIx s),
   duplicateError (TokenParser.Indexed.parseYamlWithCommentsIx s)]

def positiveControls : List String :=
  ["", "a", "a\n*x", "%TAG ! !x\n--- a", "%TAG !! !x\n--- a",
   "%TAG !h! !x\n--- !h!v a", "%TAG ! !x\n%TAG !! !y\n--- a",
   "%YAML 1.2\n%TAG !h! !x\n--- a", "%TAG !h! !x\n%YAML 1.2\n--- a",
   "%TAG !h! !x\n--- [!h!a x, !h!b y]",
   "[&x a, &x b, *x]", "&x [*x]",
   "%TAG ! !x\n--- a\n...\n%TAG ! !y\n--- b"]

def duplicateControls : List String :=
  ["%TAG ! !x\n%TAG ! !x\n--- a",
   "%TAG !! !x\n%TAG !! !y\n--- a",
   "%TAG !h! !x\n%TAG !h! !x\n--- a",
   "%TAG !h! !x\n# comment\n%TAG !h! !y\n--- a"]

-- The expected answer comes from handle equality and document scope, not
-- agreement with an existing parser or serialization checker.
def directivePairs : List (String × Bool) := Id.run do
  let mut cases := []
  for h₁ in ["!", "!!", "!h!", "!g!"] do
    for h₂ in ["!", "!!", "!h!", "!g!"] do
      for p₁ in ["!x", "!y"] do
        for p₂ in ["!x", "!y"] do
          cases := (s!"%TAG {h₁} {p₁}\n%TAG {h₂} {p₂}\n--- a", h₁ != h₂) :: cases
          cases := (s!"%TAG {h₁} {p₁}\n--- a\n...\n%TAG {h₂} {p₂}\n--- b", true) :: cases
  return cases

#guard positiveControls.all (fun s => (apiVerdicts s).all id)
#guard duplicateControls.all (fun s => (apiDuplicateErrors s).all id)
#guard directivePairs.length == 128
#guard directivePairs.all (fun (s, expected) =>
  (apiVerdicts s).all (· == expected) &&
    (expected || (apiDuplicateErrors s).all id))

#eval s!"TAG repair: {positiveControls.length} positive controls, {duplicateControls.length} duplicate controls, {directivePairs.length} independently labelled pairs; six public APIs"

end L4YAML.Tests.Guards.TagDirectiveRepair
end
