import L4YAML.Scanner.Scanner
import L4YAML.Parser.TokenParser

/-!
# SerializationWellFormed v1

Independent semantic state for the two stateful acceptance families identified
by the L4YAML grammar-completeness audit:

* anchor definitions / alias uses;
* %TAG declarations / named tag-handle uses.

The specification is deliberately not a wrapper around `scanFiltered` or
`parseStream`.  It is a small trace semantics with its own state and
well-formedness predicate.  Runtime-local bridge lemmas then show that the
actual scanner/parser guards implement the same decisions at their respective
boundaries.

This is the first brick toward:

  ExactSurfaceLanguage input ∧ SerializationWellFormed input
    ↔ InExecutableLanguage input

No `native_decide` is used in the generalized claims in this file.
-/

namespace L4YAMLSerializationWellFormed

open L4YAML

/-- Stateful serialization events, independent of scanner/parser state types. -/
inductive Event where
  | beginDocument
  | endDocument
  | defineAnchor (name : String)
  | useAlias (name : String)
  | declareTag (handle : String)
  | useTag (handle : String)
  deriving Repr, DecidableEq

/-- Minimal semantic environment needed by the two currently identified
stateful acceptance families. -/
structure Env where
  anchors : List String := []
  tagHandles : List String := []
  deriving Repr, Inhabited

def Env.reset (_ : Env) : Env := {}

/-- The handles that do not require an explicit %TAG declaration. -/
def BuiltinTagHandle (h : String) : Prop :=
  h = "" ∨ h = "!" ∨ h = "!!"

instance (h : String) : Decidable (BuiltinTagHandle h) := by
  unfold BuiltinTagHandle
  infer_instance

def AliasAllowed (env : Env) (name : String) : Prop :=
  name ∈ env.anchors

instance (env : Env) (name : String) : Decidable (AliasAllowed env name) := by
  unfold AliasAllowed
  infer_instance

def TagHandleAllowed (env : Env) (handle : String) : Prop :=
  BuiltinTagHandle handle ∨ handle ∈ env.tagHandles

instance (env : Env) (handle : String) : Decidable (TagHandleAllowed env handle) := by
  unfold TagHandleAllowed
  infer_instance

/-- Declarative trace well-formedness.

Document boundaries reset both environments.  A definition/declaration extends
the current document state; a use is permitted exactly when its corresponding
state condition holds. -/
def WellFormedFrom : Env → List Event → Prop
  | _, [] => True
  | env, .beginDocument :: rest =>
      WellFormedFrom env.reset rest
  | env, .endDocument :: rest =>
      WellFormedFrom env.reset rest
  | env, .defineAnchor name :: rest =>
      WellFormedFrom { env with anchors := name :: env.anchors } rest
  | env, .useAlias name :: rest =>
      AliasAllowed env name ∧ WellFormedFrom env rest
  | env, .declareTag handle :: rest =>
      WellFormedFrom { env with tagHandles := handle :: env.tagHandles } rest
  | env, .useTag handle :: rest =>
      TagHandleAllowed env handle ∧ WellFormedFrom env rest

def SerializationWellFormed (events : List Event) : Prop :=
  WellFormedFrom {} events

/-- Executable checker for the independent semantic specification.
It exists to prove decidability/completeness of the trace relation; it is not
defined in terms of L4YAML's scanner/parser. -/
def checkFrom : Env → List Event → Bool
  | _, [] => true
  | env, .beginDocument :: rest =>
      checkFrom env.reset rest
  | env, .endDocument :: rest =>
      checkFrom env.reset rest
  | env, .defineAnchor name :: rest =>
      checkFrom { env with anchors := name :: env.anchors } rest
  | env, .useAlias name :: rest =>
      if _h : AliasAllowed env name then checkFrom env rest else false
  | env, .declareTag handle :: rest =>
      checkFrom { env with tagHandles := handle :: env.tagHandles } rest
  | env, .useTag handle :: rest =>
      if _h : TagHandleAllowed env handle then checkFrom env rest else false

/-- Family-level correctness of the independent semantic checker. -/
lemma checkFrom_correct (env : Env) (events : List Event) :
    checkFrom env events = true ↔ WellFormedFrom env events := by
  induction events generalizing env with
  | nil =>
      simp [checkFrom, WellFormedFrom]
  | cons e rest ih =>
      cases e <;> simp [checkFrom, WellFormedFrom, ih]

lemma serializationWellFormed_iff_check (events : List Event) :
    SerializationWellFormed events ↔ checkFrom {} events = true := by
  simpa [SerializationWellFormed] using (checkFrom_correct (env := ({} : Env)) events).symm

/-! ## Scope laws: independent semantic consequences -/

lemma define_then_use_alias (env : Env) (name : String) (rest : List Event) :
    WellFormedFrom env (.defineAnchor name :: .useAlias name :: rest) ↔
      WellFormedFrom { env with anchors := name :: env.anchors } rest := by
  simp [WellFormedFrom, AliasAllowed]

lemma undeclared_alias_rejected (env : Env) (name : String)
    (h : name ∉ env.anchors) (rest : List Event) :
    ¬ WellFormedFrom env (.useAlias name :: rest) := by
  simp [WellFormedFrom, AliasAllowed, h]

lemma declare_then_use_tag (env : Env) (handle : String) (rest : List Event) :
    WellFormedFrom env (.declareTag handle :: .useTag handle :: rest) ↔
      WellFormedFrom { env with tagHandles := handle :: env.tagHandles } rest := by
  simp [WellFormedFrom, TagHandleAllowed]

lemma undeclared_named_tag_rejected (env : Env) (handle : String)
    (h_builtin : ¬ BuiltinTagHandle handle)
    (h_decl : handle ∉ env.tagHandles)
    (rest : List Event) :
    ¬ WellFormedFrom env (.useTag handle :: rest) := by
  simp [WellFormedFrom, TagHandleAllowed, h_builtin, h_decl]

lemma document_reset_forgets_anchor (env : Env) (name : String) (rest : List Event) :
    WellFormedFrom env
      (.defineAnchor name :: .endDocument :: .beginDocument :: .useAlias name :: rest) →
      False := by
  intro h
  simpa [WellFormedFrom, AliasAllowed, Env.reset] using h

lemma document_reset_forgets_custom_tag (env : Env) (handle : String)
    (h_builtin : ¬ BuiltinTagHandle handle) (rest : List Event) :
    WellFormedFrom env
      (.declareTag handle :: .endDocument :: .beginDocument :: .useTag handle :: rest) →
      False := by
  intro h
  simpa [WellFormedFrom, TagHandleAllowed, Env.reset, h_builtin] using h


/-! ## Extensional semantic state

The list representation is intentionally not semantically observable.  Only
membership matters: order and duplicate definitions/declarations are erased.
-/

def EnvEquivalent (env₁ env₂ : Env) : Prop :=
  (∀ name : String, name ∈ env₁.anchors ↔ name ∈ env₂.anchors) ∧
  (∀ handle : String, handle ∈ env₁.tagHandles ↔ handle ∈ env₂.tagHandles)

lemma envEquivalent_reset {env₁ env₂ : Env}
    (_h : EnvEquivalent env₁ env₂) :
    EnvEquivalent env₁.reset env₂.reset := by
  simp [EnvEquivalent, Env.reset]

lemma envEquivalent_defineAnchor {env₁ env₂ : Env}
    (h : EnvEquivalent env₁ env₂) (name : String) :
    EnvEquivalent
      { env₁ with anchors := name :: env₁.anchors }
      { env₂ with anchors := name :: env₂.anchors } := by
  constructor
  · intro x
    simp only [List.mem_cons]
    rw [h.1 x]
  · exact h.2

lemma envEquivalent_declareTag {env₁ env₂ : Env}
    (h : EnvEquivalent env₁ env₂) (handle : String) :
    EnvEquivalent
      { env₁ with tagHandles := handle :: env₁.tagHandles }
      { env₂ with tagHandles := handle :: env₂.tagHandles } := by
  constructor
  · exact h.1
  · intro x
    simp only [List.mem_cons]
    rw [h.2 x]

lemma aliasAllowed_equiv {env₁ env₂ : Env}
    (h : EnvEquivalent env₁ env₂) (name : String) :
    AliasAllowed env₁ name ↔ AliasAllowed env₂ name :=
  h.1 name

lemma tagHandleAllowed_equiv {env₁ env₂ : Env}
    (h : EnvEquivalent env₁ env₂) (handle : String) :
    TagHandleAllowed env₁ handle ↔ TagHandleAllowed env₂ handle := by
  unfold TagHandleAllowed
  constructor
  · intro hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr ((h.2 handle).mp hx)
  · intro hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr ((h.2 handle).mpr hx)

/-- The independent checker factors through set-membership equivalence of
semantic environments for every future event trace. -/
lemma checkFrom_envEquivalent {env₁ env₂ : Env}
    (h : EnvEquivalent env₁ env₂) (events : List Event) :
    checkFrom env₁ events = checkFrom env₂ events := by
  induction events generalizing env₁ env₂ with
  | nil =>
      rfl
  | cons event rest ih =>
      cases event with
      | beginDocument =>
          simpa [checkFrom] using ih (envEquivalent_reset h)
      | endDocument =>
          simpa [checkFrom] using ih (envEquivalent_reset h)
      | defineAnchor name =>
          simpa [checkFrom] using ih (envEquivalent_defineAnchor h name)
      | useAlias name =>
          have ha := aliasAllowed_equiv h name
          by_cases h₁ : AliasAllowed env₁ name
          · have h₂ : AliasAllowed env₂ name := ha.mp h₁
            simpa [checkFrom, h₁, h₂] using ih h
          · have h₂ : ¬ AliasAllowed env₂ name := by
              intro hx
              exact h₁ (ha.mpr hx)
            simp [checkFrom, h₁, h₂]
      | declareTag handle =>
          simpa [checkFrom] using ih (envEquivalent_declareTag h handle)
      | useTag handle =>
          have ht := tagHandleAllowed_equiv h handle
          by_cases h₁ : TagHandleAllowed env₁ handle
          · have h₂ : TagHandleAllowed env₂ handle := ht.mp h₁
            simpa [checkFrom, h₁, h₂] using ih h
          · have h₂ : ¬ TagHandleAllowed env₂ handle := by
              intro hx
              exact h₁ (ht.mpr hx)
            simp [checkFrom, h₁, h₂]

/-- Declarative well-formedness itself therefore factors through exactly the
same extensional state. -/
lemma wellFormedFrom_envEquivalent {env₁ env₂ : Env}
    (h : EnvEquivalent env₁ env₂) (events : List Event) :
    WellFormedFrom env₁ events ↔ WellFormedFrom env₂ events := by
  rw [← checkFrom_correct, ← checkFrom_correct, checkFrom_envEquivalent h events]

/-! ## Runtime bridge: scanner alias guard -/

/-- Projection of exactly the alias-relevant part of the scanner state into
our independent semantic environment. -/
def ofScannerAliases (s : L4YAML.Scanner.ScannerState) : Env :=
  { anchors := s.definedAnchors.toList }

/-- The scanner's family-level alias guard agrees with the independent
specification: an alias name is accepted exactly when it is in the semantic
anchor environment. -/
lemma scanner_alias_guard_exact (s : L4YAML.Scanner.ScannerState) (name : String) :
    s.definedAnchors.any (fun x => x == name) = true ↔
      AliasAllowed (ofScannerAliases s) name := by
  simp [AliasAllowed, ofScannerAliases, Array.mem_iff_getElem]

/-! ## Runtime bridge: parser alias guard

The scanner rejects an undefined alias before tokenization, but the token parser
also carries an anchor table and repeats the same membership condition for any
alias token it receives.  This second bridge shows that both executable stages
factor through the same independent semantic distinction.
-/

def ofParserAliases (ps : L4YAML.TokenParser.ParseState) : Env :=
  { anchors := ps.anchors.toList.map Prod.fst }

def parserAliasGuard (ps : L4YAML.TokenParser.ParseState) (name : String) : Bool :=
  ps.anchors.any (fun p => p.1 == name)

lemma parser_declared_anchor_exact
    (ps : L4YAML.TokenParser.ParseState) (name : String) :
    ps.anchors.any (fun p => p.1 == name) = true ↔
      name ∈ ps.anchors.toList.map Prod.fst := by
  constructor
  · rw [Array.any_eq_true]
    rintro ⟨i, hi, hname⟩
    apply List.mem_map.mpr
    exact ⟨ps.anchors[i], by simpa using Array.getElem_mem hi,
      by simpa only [beq_iff_eq] using hname⟩
  · intro h
    rw [Array.any_eq_true]
    obtain ⟨entry, hmem, hname⟩ := List.mem_map.mp h
    have hmem' : entry ∈ ps.anchors := by simpa using hmem
    rw [Array.mem_iff_getElem] at hmem'
    obtain ⟨i, hi, heq⟩ := hmem'
    exact ⟨i, hi, by simpa [heq, beq_iff_eq] using hname⟩

lemma parser_alias_guard_exact
    (ps : L4YAML.TokenParser.ParseState) (name : String) :
    parserAliasGuard ps name = true ↔
      AliasAllowed (ofParserAliases ps) name := by
  simp only [parserAliasGuard, AliasAllowed, ofParserAliases]
  exact parser_declared_anchor_exact ps name

/-! ## Runtime bridge: parser tag-handle guard -/

/-- Projection of exactly the tag-relevant part of parser state. -/
def ofParserTags (ps : L4YAML.TokenParser.ParseState) : Env :=
  { tagHandles := ps.tagHandles.toList.map Prod.fst }

/-- Boolean form of the guard implemented inside `parseNodeProperties`.
Built-in handles need no declaration; every other handle must occur in the
per-document tag-handle environment. -/
def parserTagGuard (ps : L4YAML.TokenParser.ParseState) (handle : String) : Bool :=
  (handle == "") || (handle == "!") || (handle == "!!") ||
    ps.tagHandles.any (fun p => p.1 == handle)

/-- Presence of a named handle in the parser's richer handle→prefix table
is exactly presence of that handle in the minimal semantic projection.  The
prefix is intentionally discarded: it affects tag resolution, but not the
accept/reject decision for declaration well-formedness. -/
lemma parser_declared_handle_exact
    (ps : L4YAML.TokenParser.ParseState) (handle : String) :
    ps.tagHandles.any (fun p => p.1 == handle) = true ↔
      handle ∈ ps.tagHandles.toList.map Prod.fst := by
  constructor
  · rw [Array.any_eq_true]
    rintro ⟨i, hi, hname⟩
    apply List.mem_map.mpr
    exact ⟨ps.tagHandles[i], by simpa using Array.getElem_mem hi,
      by simpa only [beq_iff_eq] using hname⟩
  · intro h
    rw [Array.any_eq_true]
    obtain ⟨entry, hmem, hname⟩ := List.mem_map.mp h
    have hmem' : entry ∈ ps.tagHandles := by simpa using hmem
    rw [Array.mem_iff_getElem] at hmem'
    obtain ⟨i, hi, heq⟩ := hmem'
    exact ⟨i, hi, by simpa [heq, beq_iff_eq] using hname⟩

/-- The parser's tag-handle decision agrees with the independent semantic
specification for every parser state and handle. -/
lemma parser_tag_guard_exact (ps : L4YAML.TokenParser.ParseState) (handle : String) :
    parserTagGuard ps handle = true ↔
      TagHandleAllowed (ofParserTags ps) handle := by
  simp only [parserTagGuard, Bool.or_eq_true, beq_iff_eq,
    TagHandleAllowed, BuiltinTagHandle, ofParserTags]
  rw [parser_declared_handle_exact]
  simp [or_assoc]


/-! ## Minimum-sufficient-state consequences -/

/-- For alias acceptance, every scanner field except the projected anchor-name
environment is irrelevant. -/
lemma scanner_alias_guard_ext
    (s₁ s₂ : L4YAML.Scanner.ScannerState)
    (hproj : (ofScannerAliases s₁).anchors = (ofScannerAliases s₂).anchors)
    (name : String) :
    (s₁.definedAnchors.any (fun x => x == name) = true) ↔
      (s₂.definedAnchors.any (fun x => x == name) = true) := by
  rw [scanner_alias_guard_exact, scanner_alias_guard_exact]
  simp [AliasAllowed, hproj]

/-- For named-tag declaration acceptance, the parser's richer handle→prefix
table can be quotiented to the list of handle names: tag prefixes do not affect
this accept/reject decision. -/
lemma parser_tag_guard_ext
    (ps₁ ps₂ : L4YAML.TokenParser.ParseState)
    (hproj : (ofParserTags ps₁).tagHandles = (ofParserTags ps₂).tagHandles)
    (handle : String) :
    parserTagGuard ps₁ handle = true ↔ parserTagGuard ps₂ handle = true := by
  rw [parser_tag_guard_exact, parser_tag_guard_exact]
  simp [TagHandleAllowed, hproj]



/-- Alias acceptance depends only on set-membership, not list order or
multiplicity in the projected state. -/
lemma scanner_alias_guard_set_ext
    (s₁ s₂ : L4YAML.Scanner.ScannerState)
    (hproj : ∀ name : String,
      name ∈ (ofScannerAliases s₁).anchors ↔
      name ∈ (ofScannerAliases s₂).anchors)
    (name : String) :
    (s₁.definedAnchors.any (fun x => x == name) = true) ↔
      (s₂.definedAnchors.any (fun x => x == name) = true) := by
  rw [scanner_alias_guard_exact, scanner_alias_guard_exact]
  exact hproj name

/-- Named-tag declaration acceptance likewise depends only on the set of
declared handle names, not parser-table order, duplicate declarations, or tag
prefix values. -/
lemma parser_tag_guard_set_ext
    (ps₁ ps₂ : L4YAML.TokenParser.ParseState)
    (hproj : ∀ handle : String,
      handle ∈ (ofParserTags ps₁).tagHandles ↔
      handle ∈ (ofParserTags ps₂).tagHandles)
    (handle : String) :
    parserTagGuard ps₁ handle = true ↔ parserTagGuard ps₂ handle = true := by
  rw [parser_tag_guard_exact, parser_tag_guard_exact]
  unfold TagHandleAllowed
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ((hproj handle).mp h)
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ((hproj handle).mpr h)

/-! ## Necessity / separator laws -/

/-- Anchor-name membership is not merely sufficient state: changing it can
change an observable acceptance decision immediately. -/
lemma alias_membership_separator
    (env₁ env₂ : Env) (name : String)
    (h₁ : AliasAllowed env₁ name)
    (h₂ : ¬ AliasAllowed env₂ name) :
    checkFrom env₁ [.useAlias name] ≠ checkFrom env₂ [.useAlias name] := by
  simp [checkFrom, h₁, h₂]

/-- For a non-builtin tag handle, declaration membership is likewise an
observable distinction. -/
lemma tag_membership_separator
    (env₁ env₂ : Env) (handle : String)
    (h_builtin : ¬ BuiltinTagHandle handle)
    (h₁ : handle ∈ env₁.tagHandles)
    (h₂ : handle ∉ env₂.tagHandles) :
    checkFrom env₁ [.useTag handle] ≠ checkFrom env₂ [.useTag handle] := by
  have ha₁ : TagHandleAllowed env₁ handle := Or.inr h₁
  have ha₂ : ¬ TagHandleAllowed env₂ handle := by
    simp [TagHandleAllowed, h_builtin, h₂]
  simp [checkFrom, ha₁, ha₂]

end L4YAMLSerializationWellFormed

#print axioms L4YAMLSerializationWellFormed.checkFrom_correct
#print axioms L4YAMLSerializationWellFormed.scanner_alias_guard_exact
#print axioms L4YAMLSerializationWellFormed.parser_tag_guard_exact

#print axioms L4YAMLSerializationWellFormed.scanner_alias_guard_ext
#print axioms L4YAMLSerializationWellFormed.parser_tag_guard_ext

#print axioms L4YAMLSerializationWellFormed.alias_membership_separator
#print axioms L4YAMLSerializationWellFormed.tag_membership_separator

#print axioms L4YAMLSerializationWellFormed.scanner_alias_guard_set_ext
#print axioms L4YAMLSerializationWellFormed.parser_tag_guard_set_ext

#print axioms L4YAMLSerializationWellFormed.checkFrom_envEquivalent
#print axioms L4YAMLSerializationWellFormed.wellFormedFrom_envEquivalent

#print axioms L4YAMLSerializationWellFormed.parser_alias_guard_exact
