/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Parser.Document
import Lean4Yaml.Stream

/-!
# Completeness Exploration

Exploration file for Step 5d: understanding what unfolds and what doesn't
when trying to prove per-parser specification lemmas.
-/

open Lean4Yaml
open Lean4Yaml.Parse
open Parser

/-! ## §1 Basic Infrastructure

Establish what `parseYaml` reduces to and what the proof obligations look like.
-/

-- Confirm parseYaml type
#check @parseYaml  -- String → Except String (Array YamlDocument)

-- Confirm Parser.run is just function application
#check @Parser.run  -- Parser ε σ τ α → σ → Parser.Result ε σ α

-- Confirm YamlParser is a type alias
#check @yamlStream  -- YamlParser (Array YamlDocument)

-- What does parseYaml unfold to?
-- parseYaml input =
--   let stream := YamlStream.ofString input
--   match Parser.run yamlStream stream with
--   | .ok stream' docs =>
--     match stream'.validationError with
--     | some msg => .error msg
--     | none => .ok docs
--   | .error stream' err =>
--     match stream'.validationError with
--     | some msg => .error msg
--     | none => .error (toString err)

/-! ## §2 Computational verification

Check that specific inputs compute to expected results at compile time.
-/

-- The simplest possible case: single ASCII character
#guard match parseYaml "a" with
  | .ok docs => docs.size == 1 && docs[0]!.value == .scalar ⟨"a", .plain, none⟩
  | _ => false

-- Simple word
#guard match parseYaml "hello" with
  | .ok docs => docs.size == 1 && docs[0]!.value == .scalar ⟨"hello", .plain, none⟩
  | _ => false

-- Double-quoted scalar
#guard match parseYaml "\"hello\"" with
  | .ok docs => docs.size == 1 && docs[0]!.value == .scalar ⟨"hello", .doubleQuoted, none⟩
  | _ => false

-- Single-quoted scalar
#guard match parseYaml "'hello'" with
  | .ok docs => docs.size == 1 && docs[0]!.value == .scalar ⟨"hello", .singleQuoted, none⟩
  | _ => false

/-! ## §3 Unfolding depth exploration

Try to understand what `simp` and `unfold` can do with parser definitions.
-/

-- Can we state a basic theorem?
-- theorem parseYaml_plain_a : parseYaml "a" = .ok #[{ value := .scalar ⟨"a", .plain, none⟩, directives := #[] }] := by
--   native_decide

-- Try with decide (will likely fail due to DecidableEq on YamlValue)
-- theorem parseYaml_plain_a' : parseYaml "a" = .ok #[{ value := .scalar ⟨"a", .plain, none⟩, directives := #[] }] := by
--   decide

-- Try with rfl (will likely fail — too much computation)
-- theorem parseYaml_plain_a'' : parseYaml "a" = .ok #[{ value := .scalar ⟨"a", .plain, none⟩, directives := #[] }] := by
--   rfl

/-! ## §4 Stream lemmas

Basic properties of YamlStream that will be needed for parser proofs.
-/

-- YamlStream.ofString creates a stream with no validation error
theorem ofString_no_validationError (s : String) :
    (YamlStream.ofString s).validationError = none := by
  rfl

-- YamlStream.ofString starts at position 0
theorem ofString_startPos (s : String) :
    (YamlStream.ofString s).startPos = ⟨0⟩ := by
  rfl

-- YamlStream.ofString has correct stopPos
theorem ofString_stopPos (s : String) :
    (YamlStream.ofString s).stopPos = s.rawEndPos := by
  rfl

-- remaining for ofString
theorem ofString_remaining (s : String) :
    Parser.Stream.remaining (YamlStream.ofString s) = s.rawEndPos.byteIdx := by
  rfl

-- YamlStream.ofString has empty anchor map
theorem ofString_anchorMap (s : String) :
    (YamlStream.ofString s).anchorMap = AnchorMap.empty := by
  rfl

-- YamlStream.ofString starts at line 0, col 0
theorem ofString_line (s : String) :
    (YamlStream.ofString s).line = 0 := by
  rfl

theorem ofString_col (s : String) :
    (YamlStream.ofString s).col = 0 := by
  rfl

/-! ## §5 Parser.Result matching lemma

When Parser.run succeeds, we can extract the result.
-/

-- parseYaml success means Parser.run yamlStream succeeded with no validation error
theorem parseYaml_ok_iff (input : String) (docs : Array YamlDocument) :
    parseYaml input = .ok docs ↔
    ∃ stream' : YamlStream,
      Parser.run yamlStream (YamlStream.ofString input) = .ok stream' docs ∧
      stream'.validationError = none := by
  constructor
  · intro h
    simp only [parseYaml] at h
    split at h
    · next stream' docs' heq =>
      split at h
      · contradiction
      · next hnone =>
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨stream', heq, hnone⟩
    · next stream' err heq =>
      split at h <;> contradiction
  · intro ⟨stream', hrun, hval⟩
    simp only [parseYaml]
    rw [hrun]
    simp [hval]


/-! ## §6 Concrete parse theorems via native_decide

Test whether native_decide can prove concrete parse equality.
-/

-- First check: does YamlDocument have DecidableEq?
-- #check (inferInstance : DecidableEq YamlDocument)
-- #check (inferInstance : DecidableEq YamlValue)

-- Check BEq instances
#check (inferInstance : BEq YamlValue)
#check (inferInstance : BEq YamlDocument)

/-! ## §7 DecidableEq exploration

Check if we have DecidableEq for the types we need.
-/

-- Check if Except has DecidableEq when both components do
-- The issue is: does Array YamlDocument have DecidableEq?
-- YamlDocument has BEq but might not have DecidableEq.

-- Let's check what instances we can synthesize:
-- #check (inferInstance : DecidableEq ScalarData)   -- probably derived
-- #check (inferInstance : DecidableEq YamlValue)    -- probably not (recursive)
-- #check (inferInstance : DecidableEq YamlDocument)

-- Try a simple parseYaml result check with match:
theorem parseYaml_a_ok :
    (match parseYaml "a" with | .ok _ => true | .error _ => false) = true := by
  native_decide

-- Can we go further and check the specific value?
theorem parseYaml_a_value :
    (match parseYaml "a" with
     | .ok docs => docs.size == 1 && docs[0]!.value == .scalar ⟨"a", .plain, none⟩
     | .error _ => false) = true := by
  native_decide

-- Can we check double-quoted?
theorem parseYaml_dq_hello :
    (match parseYaml "\"hello\"" with
     | .ok docs => docs.size == 1 && docs[0]!.value == .scalar ⟨"hello", .doubleQuoted, none⟩
     | .error _ => false) = true := by
  native_decide

-- Can we check single-quoted?
theorem parseYaml_sq_hello :
    (match parseYaml "'hello'" with
     | .ok docs => docs.size == 1 && docs[0]!.value == .scalar ⟨"hello", .singleQuoted, none⟩
     | .error _ => false) = true := by
  native_decide

-- Can we check a flow sequence?
theorem parseYaml_flow_seq :
    (match parseYaml "[1, 2, 3]" with
     | .ok docs => docs.size == 1
     | .error _ => false) = true := by
  native_decide

-- Can we check a block mapping?
theorem parseYaml_block_map :
    (match parseYaml "key: value" with
     | .ok docs => docs.size == 1 && docs[0]!.value == .mapping .block #[(.scalar ⟨"key", .plain, none⟩, .scalar ⟨"value", .plain, none⟩)] none
     | .error _ => false) = true := by
  native_decide

-- Can we prove exact equality using Except.ok with native_decide?
-- This requires DecidableEq for Except String (Array YamlDocument)
-- which requires DecidableEq for Array YamlDocument
-- which requires DecidableEq for YamlDocument
-- which requires DecidableEq for YamlValue (recursive!)
-- Let's test:

-- instance : DecidableEq YamlValue := by
--   intro a b; exact decidable_of_iff _ (beq_iff_eq a b)  -- needs LawfulBEq

-- Alternative: prove via BEq + native_decide
-- First, let's try to get DecidableEq for YamlValue

-- Check if DecidableEq can be synthesized after-the-fact
-- #check (inferInstance : DecidableEq YamlValue) -- should work if deriving works

-- Try proving exact equality via native_decide with a DecidableEq instance
-- We need DecidableEq for: YamlValue, YamlDocument, Array YamlDocument, Except String ...

-- Actually, let's try a different approach: prove it via BEq reflection
-- Since YamlValue derives BEq structurally, we can try to prove
-- (a == b) = true → a = b for our specific types

-- Simplest approach: use the fact that #guard already proves the computational check
-- and combine with a manual proof about the structure.

-- Approach 1: Just use native_decide on a Bool predicate
-- This works (proved above). For completeness proofs, what we really need is:
-- "for this specific input, parseYaml produces .ok with these docs"
-- The Bool version IS a theorem — it says the computation evaluates to true.
-- The question is whether we can lift it to propositional equality.

-- Try: define a checked parse function that returns a Prop
def parseYamlEq (input : String) (expected : Array YamlDocument) : Bool :=
  match parseYaml input with
  | .ok docs => docs == expected
  | .error _ => false

-- Now try native_decide on the Prop version
theorem parseYaml_a_eq : parseYamlEq "a" #[{ value := .scalar ⟨"a", .plain, none⟩, directives := #[] }] = true := by
  native_decide

-- Can we go from parseYamlEq = true to parseYaml = .ok?
-- We need: (docs == expected) = true → docs = expected
-- This is exactly LawfulBEq.

-- Let's check if we can derive it for our types
-- The key is: does Array YamlValue have LawfulBEq?
-- Array α has LawfulBEq if α does.
-- YamlValue has BEq (derived). Does it have LawfulBEq?

-- For now, let's try the DecidableEq route.
-- Even though YamlValue doesn't derive DecidableEq, we can define it manually
-- using the BEq instance.

-- Test: can we get Decidable (a = b) for concrete values?
-- example : (.scalar ⟨"a", .plain, none⟩ : YamlValue) = .scalar ⟨"a", .plain, none⟩ := by rfl

-- Actually this works because it's definitionally equal!
-- The question is whether we can do:
-- example : Decidable ((.scalar ⟨"a", .plain, none⟩ : YamlValue) = .scalar ⟨"b", .plain, none⟩) := by
--   exact isFalse (by intro h; injection h; ...)

-- For completeness proofs, the real question is:
-- can we state and prove ∀-quantified theorems about the parser?
-- Not just concrete instances.

-- Let's pivot to the real work: per-parser specification lemmas.
-- The concrete native_decide theorems are interesting but not the goal.
-- The goal is: for each ValidNode constructor, prove the parser succeeds.
-- That's a universally quantified statement.

-- Key insight: we DON'T need propositional equality on parse results.
-- We need: "there exist docs such that parseYaml input = .ok docs"
-- combined with: "the docs have the expected structure"
-- Both can be proved via the biconditional parseYaml_ok_iff + parser unfolding.

/-! ## §8 Per-parser specification: strategy

For each ValidNode constructor (12 total), we need:
1. A predicate characterizing valid inputs for that constructor
2. A theorem: valid input → parser succeeds with correct result

The simplest case is plainScalarBlock: a non-empty string containing
only "safe" characters (no YAML metacharacters).
-/

-- Helper: check if a character is "plain-safe" in block context
-- (simplified — real plain scalar rules are complex)
-- For proof purposes, we start with the simplest sub-case:
-- a single ASCII letter as the entire document.

-- Theorem: parseYaml produces .ok for a single-character string
-- (when the character is a safe plain scalar character)
-- This is the calibration theorem — tells us what proof infrastructure we need.

-- For now, record what we learned:
-- 1. native_decide works for concrete parse results (Bool predicates)
-- 2. #guard works for compile-time verification
-- 3. parseYaml_ok_iff bridges parseYaml to Parser.run + validationError = none
-- 4. ofString lemmas characterize the initial stream state
-- 5. Propositional equality on parse results needs DecidableEq or LawfulBEq
-- 6. The real challenge is universally quantified per-parser lemmas
