# BRIDGING.md — Grammar Specification Gap Analysis

## Problem Statement

`Grammar.lean` defines a formal YAML 1.2.2 specification with 19 definitions.
The doc-verification-bridge analysis found **0 theorems** about 13 of them.
The existing proof suite (33 files under `Lean4Yaml/Proofs/`) proves properties
about `NodeToValue`, `toYamlValue`, `stripAnnotations`, and `Grammable`, but
leaves the character-level predicates, indentation, token stream, and top-level
structures entirely unconnected to the parser implementation.

This document catalogs each gap and proposes the theorems needed to bridge
the Grammar specification to the implementation.

---

## Architecture Overview

### Target Architecture (Revised)

The specification mirrors the implementation's two-layer architecture
(scanner + parser) with a shared predicate foundation. This prevents
specification drift by coupling Bool and Prop definitions via iff theorems
that break the build if either side changes.

```
CharPredicates.lean  (Bool + Prop + iff theorems, no project imports)
        ↑
  Types.lean ← Token.lean ← Scanner.lean   (uses Bool predicates)
                           ← Grammar.lean   (uses Prop predicates;
                                             defines Scannable, Grammable,
                                             ValidNode, ValidYaml)

Proof chain:
  String ──[scan]──▸ tokens ──[parseStream]──▸ raw docs
                        │                         │
                   Scannable                   compose
                  (per-token)                     │
                                                  ▼
                                         ──[Grammable]──▸ composed docs
                                                  │
                                            ∃ ValidNode
                                                  │
                                            NodeToValue
                                                  │
                                          Grammar.ValidYaml ◀── capstone
```

### Three Specification Layers

| Layer | Predicate | Scope | Handles |
|-------|-----------|-------|---------|
| **Char-level** | `CharPredicates.lean` | Individual chars and strings | `isWhiteSpaceProp/Bool`, `canStartPlainScalarProp/Bool`, `validPlainFirstProp/Bool`, `noColonSpaceProp/Bool`, `noSpaceHashProp/Bool`, `noFlowIndicatorsProp/Bool` — with `_iff` coupling theorems |
| **Token-level** | `Scannable` | Pre-compose `YamlValue` tree | Scanner contract: char predicates satisfied, aliases allowed, context-aware (`inFlow`) |
| **Grammar-level** | `Grammable` | Post-compose `YamlValue` tree | Parser contract: char predicates satisfied, no aliases, context-aware (`inFlow`) |

### Anti-Drift Mechanism

Each predicate in `CharPredicates.lean` has three parts:

```lean
-- 1. Bool (runtime — used by Scanner)
def isWhiteSpaceBool (c : Char) : Bool := c == ' ' || c == '\t'

-- 2. Prop (specification — used by Grammar/proofs)
def isWhiteSpaceProp (c : Char) : Prop := c = ' ' ∨ c = '\t'

-- 3. Coupling theorem (the "drift alarm" — build breaks if either side changes)
@[simp] theorem isWhiteSpace_iff (c : Char) :
    isWhiteSpaceBool c = true ↔ isWhiteSpaceProp c := by ...
```

If someone changes the Bool version in a refactor, the iff proof fails →
build error. Silent drift is impossible.

### Two `ValidYaml` Definitions (THE CENTRAL PROBLEM)

| Definition | Location | Type | Status |
|---|---|---|---|
| `Grammar.ValidYaml` | Grammar.lean:541–548 | `structure` with `input`, `value`, `grammar : ValidNode`, `corresponds : NodeToValue grammar value` | **Dead** — no theorem constructs or consumes it from parser output |
| `EndToEndCorrectness.ValidYaml` | EndToEndCorrectness.lean:93 | `def ... : Prop` — `∃ filtered_tokens raw_docs, scanFiltered = ok ∧ parseStream = ok ∧ docs = raw_docs.map compose` | **Tautological** — `parse_sound`/`parse_complete` just decompose/recompose the pipeline |

**No theorem connects these two definitions.** The Grammar-level `ValidYaml` bundles
a `ValidNode` witness and `NodeToValue` correspondence, while the E2E `ValidYaml` only
asserts pipeline success. The entire Grammar specification is therefore disconnected
from verified properties.

---

## Gap Inventory

### Gap 0: The `h_grammable` Hypothesis (BLOCKING)

**Severity: CRITICAL — blocks all downstream Grammar connections**

`ParserCorrectness.lean` has two theorems:

```lean
theorem parseStream_values_have_witnesses
    (h_grammable : ∀ doc ∈ docs.toList, Grammable (doc.compose.value))
    ...

theorem parseStream_respects_grammar
    (h_grammable : ∀ doc ∈ docs.toList, Grammable (doc.compose.value))
    ...
```

Both **assume** `h_grammable` — that parser output is `Grammable` — but this is
never proven. `Grammable v` requires:
- No `alias` nodes (after composition — likely holds)
- Every plain scalar satisfies `validPlainFirst`, `noColonSpace`, `noSpaceHash`

This is ultimately a **scanner obligation**: the scanner must emit tokens whose
content satisfies these character predicates. Until this is proven, the Grammable
assumption is an axiom-in-disguise.

**Required theorems:**

```lean
-- Scanner-level: tokens satisfy character constraints
theorem scan_plain_scalar_valid (input : String) (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens)
    (i : Fin tokens.size) (s : Scalar)
    (hs : tokens[i].val = .scalar s) (hplain : s.style = .plain)
    (hne : s.content.length > 0) :
    validPlainFirst s.content ∧ noColonSpace s.content ∧ noSpaceHash s.content

-- Parser-level: composed output is Grammable
theorem parseStream_output_grammable (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h : TokenParser.parseStream tokens = .ok docs) :
    ∀ doc ∈ docs.toList, Grammable (doc.compose.value)
```

**Proof strategy:** The scanner already enforces these constraints operationally
(it reads characters matching `ns-plain-first` and `ns-plain-char`). The proof
must show the scanner's character-matching logic implies the formal predicates.
This likely requires a scanner invariant that tracks character constraints through
the scanning state machine.

---

### Gap 1: `validPlainFirst`

**Severity: CRITICAL**

**Definition** (Grammar.lean:296–300):
```lean
def validPlainFirst (content : String) : Prop :=
  match content.toList with
  | c :: _ => canStartPlainScalar c
  | [] => True
```

**Current state:** Used as a proof obligation in `ValidNode.plainScalarBlock` and
`ValidNode.plainScalarFlow`. The `Grammable` predicate requires it for plain scalars.
`scalar_has_witness` in `ParserSoundness.lean` takes it as a hypothesis. No theorem
proves the scanner produces tokens satisfying it.

**Has `Decidable` instance:** Yes.

**Required theorems:**

```lean
-- Scanner enforces validPlainFirst on emitted plain scalar tokens
theorem scan_enforces_validPlainFirst (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens) :
    ∀ i (hi : i < tokens.size),
      ∀ s : Scalar, tokens[i].val = .scalar s →
        s.style = .plain → s.content.length > 0 →
        validPlainFirst s.content

-- Characterization: validPlainFirst ↔ canStartPlainScalar on first char
theorem validPlainFirst_iff (content : String) (hne : content.length > 0) :
    validPlainFirst content ↔ canStartPlainScalar (content.toList.head (by ...))
```

---

### Gap 2: `noColonSpace`

**Severity: CRITICAL**

**Definition** (Grammar.lean:313–314):
```lean
def noColonSpace (content : String) : Prop :=
  ¬ ∃ i, content.toList[i]? = some ':' ∧ content.toList[i + 1]? = some ' '
```

**Current state:** Used in `ValidNode.plainScalarBlock/Flow` and `Grammable`.
No theorem proves the scanner enforces it. ✅ `Decidable` instance added (Phase A)
via `hasAdjacentChars` helper.

**Required theorems:**

```lean
-- Scanner enforcement (subsumed by Gap 0's scan_plain_scalar_valid)
```

---

### Gap 3: `noSpaceHash`

**Severity: CRITICAL**

**Definition** (Grammar.lean:322–323):
```lean
def noSpaceHash (content : String) : Prop :=
  ¬ ∃ i, content.toList[i]? = some ' ' ∧ content.toList[i + 1]? = some '#'
```

**Current state:** Same as `noColonSpace` — used in `ValidNode` and `Grammable`,
never proven enforced. ✅ `Decidable` instance added (Phase A) via `hasAdjacentChars`.

**Required theorems:**

```lean
-- Scanner enforcement (subsumed by Gap 0's scan_plain_scalar_valid)
```

---

### Gap 4: `noFlowIndicators`

**Severity: CRITICAL**

**Definition** (Grammar.lean:331–332):
```lean
def noFlowIndicators (content : String) : Prop :=
  ∀ c ∈ content.toList, ¬isFlowIndicator c
```

**Current state:** Used only in `ValidNode.plainScalarFlow`. Not included in
`Grammable` (which does not distinguish block/flow context). No theorem proves
the scanner enforces it in flow context.

✅ `Decidable` instance added (Phase A) via `List.decidableBAll`.

**Required theorems:**

```lean
-- Scanner enforcement in flow context
theorem scan_flow_plain_no_indicators (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens)
    (i : Fin tokens.size) (s : Scalar)
    (hs : tokens[i].val = .scalar s)
    (hplain : s.style = .plain)
    (hflow : -- token is in flow context --) :
    noFlowIndicators s.content
```

**Note:** The `Grammable` predicate currently does not track flow context.
Either `Grammable` needs a flow-context variant, or `noFlowIndicators` must be
proven separately when constructing `ValidNode.plainScalarFlow` from parser output.

---

### Gap 5: `canStartPlainScalar`

**Severity: HIGH** (used transitively via `validPlainFirst`)

**Definition** (Grammar.lean:115–123):
```lean
def canStartPlainScalar (c : Char) : Prop :=
  isPrintable c ∧ ¬ isWhiteSpace c ∧ ¬ isLineBreak c
  ∧ c ∉ ['-', '?', ':', ',', '[', ']', '{', '}', '#', '&', '*', '!', '|', '>',
         '\'', '"', '%', '@', '`']
```

**Current state:** Has a `Decidable` instance (Grammar.lean:124). Referenced
indirectly through `validPlainFirst`. No direct theorems characterize it.

**Required theorems:**

```lean
-- Relationship to YAML spec character classes
theorem canStartPlainScalar_iff (c : Char) :
    canStartPlainScalar c ↔
    isPrintable c ∧ ¬isWhiteSpace c ∧ ¬isLineBreak c ∧ ¬isIndicator c

-- Scanner uses this predicate at plain-scalar entry points
theorem scan_plain_entry_char (c : Char)
    (h : -- scanner enters plain scalar state at char c --) :
    canStartPlainScalar c
```

---

### Gap 6: `IndentedAtLeast` / `Indented` / `decideIndented`

**Severity: HIGH** (block structure correctness depends on indentation)

**Definitions** (Grammar.lean:150–195):
```lean
inductive Indented : Nat → List Char → Prop where
  | zero (cs : List Char) : Indented 0 cs
  | space (n : Nat) (cs : List Char) : Indented n cs → Indented (n + 1) (' ' :: cs)

def IndentedAtLeast (n : Nat) (cs : List Char) : Prop :=
  ∃ m, m ≥ n ∧ Indented m cs
```

**Current state:** Both have `Decidable` instances. `indented_weaken` is proven.
These definitions are used in the `ValidNode` block constructors' intended semantics
(block-seq/block-map carry an `indent` field) but are never referenced in `NodeToValue`
or any proof file.

**Required theorems:**

```lean
-- Scanner emits correct indentation levels
theorem scan_block_indent_correct (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens) :
    -- For each blockSeq/blockMap token, the indent field matches
    -- the actual leading spaces in the source line
    sorry

-- Indentation monotonicity for nested blocks
theorem indented_nested {n m : Nat} {cs : List Char}
    (h : Indented m cs) (hlt : n < m) :
    ∃ rest, Indented n rest

-- IndentedAtLeast transitivity
theorem indentedAtLeast_trans {n m : Nat} {cs : List Char}
    (h : IndentedAtLeast m cs) (hle : n ≤ m) :
    IndentedAtLeast n cs
```

---

### Gap 7: `ValidTokenStream`

**Severity: HIGH** (scanner/parser bridge contract)

**Definition** (Grammar.lean:436–451):
```lean
structure ValidTokenStream where
  input : String
  tokens : Array (Positioned YamlToken)
  sizeGe2 : tokens.size ≥ 2
  firstIsStreamStart : (tokens[0]'...).val = .streamStart
  lastIsStreamEnd : (tokens[tokens.size - 1]'...).val = .streamEnd
  positionsOrdered : ∀ (i j : Fin tokens.size), i.val < j.val →
    (tokens[i]).pos.offset ≤ (tokens[j]).pos.offset
```

**Current state:** Defined but never used in any theorem. The scanner does
not produce a `ValidTokenStream` — neither `Scanner.scan` nor
`Scanner.scanFiltered` return this type. The comment in Grammar.lean
explicitly says:

> The scanner's correctness theorem (future work) will state:
> `theorem scan_valid (input : String) ... : ValidTokenStream input tokens`

**Required theorems:**

```lean
-- THE scanner correctness theorem
theorem scan_produces_valid_token_stream (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens) :
    ValidTokenStream.mk input tokens
      (by sorry) -- sizeGe2
      (by sorry) -- firstIsStreamStart
      (by sorry) -- lastIsStreamEnd
      (by sorry) -- positionsOrdered

-- Parser consumes ValidTokenStream correctly
theorem parseStream_consumes_valid_tokens
    (vts : ValidTokenStream)
    (h : TokenParser.parseStream vts.tokens = .ok docs) :
    -- parseStream succeeds on any ValidTokenStream
    True  -- exact obligation TBD
```

---

### Gap 8: `ValidYaml` (Grammar-level)

**Severity: CRITICAL** (the entire specification target)

**Definition** (Grammar.lean:541–548):
```lean
structure ValidYaml where
  input : String
  value : YamlValue
  grammar : ValidNode
  corresponds : NodeToValue grammar value
```

**Current state:** `Soundness.lean` has `validYaml_construct` and
`validYaml_value_eq_toYamlValue` for construction/decomposition, but
these are about the structure itself — not about connecting parser output
to it. No theorem states:

```
parse input = .ok docs → Grammar.ValidYaml input docs[i].value
```

**Required theorem (the main soundness goal):**

```lean
theorem parse_produces_valid_yaml (input : String)
    (docs : Array YamlDocument)
    (h : TokenParser.parseYaml input = .ok docs) :
    ∀ i : Fin docs.size,
      ∃ vy : Grammar.ValidYaml,
        vy.input = input ∧
        stripAnnotations vy.value = stripAnnotations docs[i].compose.value
```

**Dependencies:** This requires Gap 0 (`h_grammable` discharge) which requires
Gaps 1–4 (character predicates). It is the capstone theorem.

---

### Gap 9: `ValidStream`

**Severity: LOW (dead code)**

**Definition** (Grammar.lean:409–413):
```lean
structure ValidStream where
  documents : List ValidDocument
  nonempty : documents.length > 0
```

**Current state:** Never referenced outside Grammar.lean. `ValidDocument` is
also unreferenced.

**Recommendation:** Either:
1. Remove as dead code, or
2. Connect to `parseStream` output by proving multi-document stream validity

If kept, the required theorem would be:

```lean
theorem parseStream_produces_valid_stream
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h : TokenParser.parseStream tokens = .ok docs)
    (hne : docs.size > 0) :
    ∃ vs : ValidStream, vs.documents.length = docs.size
```

---

### Gap 10: `isContentChar`

**Severity: LOW** (block scalar header parsing)

**Definition** (Grammar.lean:758–759):
```lean
def isContentChar (c : Char) : Prop :=
  isBlockScalarHeaderChar c = false
```

**Current state:** Has `Decidable` instance. Used to classify characters during
block scalar header parsing. The block scalar header proofs
(`BlockScalarHeader.lean`, `BlockScalarHeaderSpec.lean`) likely use this — needs
verification.

**Required theorems:**

```lean
-- isContentChar is the complement of isBlockScalarHeaderChar
theorem isContentChar_iff_not_header (c : Char) :
    isContentChar c ↔ ¬(isBlockScalarHeaderChar c = true)

-- Block scalar header parser stops at content chars
theorem blockScalarHeader_stops_at_content (cs : List Char)
    (c : Char) (rest : List Char)
    (h : isContentChar c) :
    -- header parser does not consume c
    sorry
```

---

### Gap 11: `isNamedEscapeChar`

**Severity: LOW** (double-quoted scalar parsing)

**Definition** (Grammar.lean:278–279):
```lean
def isNamedEscapeChar (c : Char) : Prop :=
  resolveNamedEscape c ≠ none
```

**Current state:** Has `Decidable` instance. Used to validate escape sequences
in double-quoted scalars. No theorems characterize the escape resolution.

**Required theorems:**

```lean
-- Named escape chars resolve to exactly one output char
theorem isNamedEscapeChar_resolves (c : Char) (h : isNamedEscapeChar c) :
    ∃ out : Char, resolveNamedEscape c = some out

-- Exhaustive characterization
theorem isNamedEscapeChar_chars :
    isNamedEscapeChar c ↔ c ∈ ['0', 'a', 'b', 't', '\t', 'n', 'v', 'f',
                                'r', 'e', ' ', '"', '/', '\\', 'N', '_']
```

---

### Gap 12: `validHeaderLength`

**Severity: LOW** (block scalar header constraint)

**Definition** (Grammar.lean:747–748):
```lean
def validHeaderLength (cs : List Char) : Prop :=
  (extractHeaderChars cs).1.length ≤ 2
```

**Current state:** Has `Decidable` instance. Used to bound the header indicator
count. Likely referenced in block scalar header proofs.

**Required theorems:**

```lean
-- At most one chomp + one indent indicator
theorem validHeaderLength_spec (cs : List Char) :
    validHeaderLength cs ↔ (extractHeaderChars cs).1.length ≤ 2

-- extractHeaderChars terminates within 2 chars for valid input
theorem extractHeaderChars_bounded (cs : List Char)
    (h : validHeaderLength cs) :
    ∀ c ∈ (extractHeaderChars cs).1, isBlockScalarHeaderChar c = true
```

---

## Specification Drift Analysis (Phase B pre-investigation)

Investigation conducted after Phase A to determine whether Grammar.lean's
definitions are provably connected to the scanner/parser implementation.

**Finding: Grammar.lean has drifted from the implementation in 4 ways.**
The specification is **salvageable** but requires targeted fixes before
Phase B proofs can proceed.

### Drift 1: `canStartPlainScalar` — Context-free vs Context-sensitive

**YAML 1.2.2 spec** ([123] ns-plain-first): characters `-`, `?`, `:` MAY
start a plain scalar *when followed by a non-whitespace, non-break character*
(and in flow context, not followed by a flow indicator).

**Grammar.lean** (line 115): **Unconditionally excludes** `-`, `?`, `:`:
```lean
def canStartPlainScalar (c : Char) : Prop :=
  isPrintable c ∧ ¬ isWhiteSpace c ∧ ¬ isLineBreak c
  ∧ c ∉ ['-', '?', ':', ',', '[', ']', '{', '}', '#', '&', '*', '!', '|', '>',
         '\'', '"', '%', '@', '`']
```

**Scanner.lean** (line 1556): **Conditionally allows** them (correct per spec):
```lean
def canStartPlainScalar (c : Char) (next : Option Char) (inFlow : Bool) : Bool :=
  if c == '-' || c == '?' || c == ':' then
    match next with
    | some n => !isWhiteSpace n && !isLineBreak n && !(inFlow && isFlowIndicator n)
    | none => false
  else
    !isIndicator c && !isWhiteSpace c && !isLineBreak c
```

**Empirical evidence:** The scanner/parser accepts `?foo`, `-bar`, `:baz`
as plain scalars. Grammar's `validPlainFirst` rejects all three. These are
**valid YAML** per the spec.

**Impact:** `validPlainFirst`, `ValidNode.plainScalarBlock`, `ValidNode.plainScalarFlow`,
and `Grammable` all share this bug. No `ValidNode` can represent a plain scalar
whose content starts with `-`, `?`, or `:`.

**Fix:** Change `canStartPlainScalar` to a 2-argument version that takes the
first two characters of the content string (or the content string itself):
```lean
def canStartPlainScalar (c : Char) (next : Option Char) : Prop :=
  if c == '-' ∨ c == '?' ∨ c == ':' then
    match next with
    | some n => ¬isWhiteSpace n ∧ ¬isLineBreak n
    | none => False
  else
    isPrintable c ∧ ¬isWhiteSpace c ∧ ¬isLineBreak c ∧ ¬isIndicator c
```

And update `validPlainFirst` to extract the first two characters:
```lean
def validPlainFirst (content : String) : Prop :=
  match content.toList with
  | c :: n :: _ => canStartPlainScalar c (some n)
  | [c] => canStartPlainScalar c none
  | [] => True
```

### Drift 2: `noColonSpace` — Missing tab and flow-indicator termination

**Scanner** terminates plain scalars at `:` followed by any blank
(`isWhiteSpace` = space OR tab) or `:` followed by a flow indicator in
flow context.

**Grammar** checks only for `:` followed by literal `' '` (space):
```lean
def noColonSpace (content : String) : Prop :=
  ¬ ∃ i, content.toList[i]? = some ':' ∧ content.toList[i + 1]? = some ' '
```

**Impact:** `noColonSpace` is **weaker than what the scanner enforces**.
This means the Grammar accepts strings like `"foo:\tbar"` that the scanner
would never produce. For bridging proofs, this is actually **fine** for
soundness (scanner output satisfies a stronger property that implies
`noColonSpace`), but the spec is less precise than it could be.

**Fix (optional):** Could strengthen to `noColonBlank` checking for both
space and tab. For bridging purposes, the current definition is sufficient
since the scanner's stronger guarantee implies `noColonSpace`.

### Drift 3: `noSpaceHash` — Missing tab

Same pattern as Drift 2. Scanner terminates at ANY whitespace + `#`
(space or tab), but Grammar only checks for space + `#`. Again, this is
fine for soundness — the weaker Grammar predicate is implied by the
scanner's stronger behavior.

### Drift 4: Tags and Anchors — `NodeToValue` is annotation-free only

**Parser output:** `YamlValue.scalar { tag := some "!!str", anchor := some "a" }`

**NodeToValue:** All constructors produce `tag := none, anchor := none`:
```lean
| plainScalarBlock content h ... :
    NodeToValue (.plainScalarBlock content h ...)
      (.scalar ⟨content, .plain, none, none, none⟩)
```

**Impact:** A tagged plain scalar like `!!str hello` cannot be represented
by any `ValidNode` → `NodeToValue` pair. The Grammar specification only
covers annotation-free values.

**Current mitigation:** `stripAnnotations` removes tags/anchors, and the
existing proofs (ParserSoundness, ParserCompleteness) work modulo
`stripAnnotations`. The `Grammable` predicate ignores tags/anchors.
This is architecturally intentional — Grammar.lean models the
*representation graph* (YAML 1.2.2 §3.2.1) where tags and anchors are
metadata, not structural content.

**Fix:** None needed for Phase B. The existing `stripAnnotations`-modulo
approach is sound. The real specification target is:
```
stripAnnotations (toYamlValue witness) = stripAnnotations (parser_output)
```
which is what `parseStream_sound` and `parseStream_complete` already state.

### Drift Summary

| Drift | Severity | Fix Required for Phase B? | Effort |
|-------|----------|--------------------------|--------|
| 1. `canStartPlainScalar` | **BLOCKING** | **Yes** — spec is wrong per YAML 1.2.2 | Low (definition + Decidable) |
| 2. `noColonSpace` weaker | Cosmetic | No — scanner implies Grammar's weaker predicate | — |
| 3. `noSpaceHash` weaker | Cosmetic | No — same reasoning | — |
| 4. Tags/anchors | Architectural | No — `stripAnnotations`-modulo works | — |

### Parallel Definitions (Bool vs Prop)

Grammar.lean and Scanner.lean define **parallel** character predicates
that are semantically identical but have different types:

| Predicate | Scanner (Bool) | Grammar (Prop) | Semantics |
|-----------|---------------|----------------|-----------|
| `isLineBreak` | L300 | L73 | ✅ Identical |
| `isWhiteSpace` | L302 | L88 | ✅ Identical |
| `isFlowIndicator` | L306 | L133 | ✅ Identical |
| `isIndicator` | L308 | (inline list) | ✅ Identical chars |
| `isPrintable` | — | L56 | Grammar-only |

These are maintained in sync by convention, not by sharing. A future
cleanup could extract shared definitions to a `CharPredicates.lean` module,
but this is not blocking.

---

## Priority Plan (Revised — v2)

### Phase A: Decidable Instances ✅ COMPLETE

Added missing `Decidable` instances for:
1. ✅ `noColonSpace` — via `hasAdjacentChars ':' ' '` boolean helper + iff proof
2. ✅ `noSpaceHash` — via `hasAdjacentChars ' ' '#'` boolean helper + iff proof
3. ✅ `noFlowIndicators` — via `List.decidableBAll`

All added to `Grammar.lean`. Build: 211/211, tests: 869/869, 0 sorry, 0 axioms.

#### Phase A Reflections

**Approach chosen:** Instead of trying to get `Decidable` for the negated
existential `¬ ∃ i, ...` directly, we introduced a boolean scanning function
`hasAdjacentChars` and proved the bidirectional `hasAdjacentChars_iff` theorem
that connects it to the `∃ i, cs[i]? = ...` proposition. The `Decidable`
instance then pattern-matches on the boolean result.

**Unexpected challenges:**
- `beq_iff_eq.mp`/`.mpr` produces `(c == a) = true` not `c = a`. Using `subst`
  after `simp` destructures the BEq hypothesis cleanly. First attempt failed
  because `simp [beq_iff_eq.mp h]` doesn't substitute into the goal — `subst`
  is required.
- `push_neg` is Mathlib-only. The `isFalse` branch uses
  `absurd ((iff).mp h) hn` instead.
- `List.getElem?` is not a valid identifier in Lean 4.28 (it's notation, not
  a def). Simplification lemmas `List.getElem?_cons_zero` and
  `List.getElem?_cons_succ` work with bare `simp`.

**Simplifications:**
- `noFlowIndicators` was trivial: `List.decidableBAll` from core Lean handles
  `∀ c ∈ list, ¬P c` directly, given `Decidable (isFlowIndicator c)` which
  already existed.
- The `hasAdjacentChars` helper is reusable — it works for any two-character
  adjacency pattern, making `noColonSpace` and `noSpaceHash` share the same
  proof infrastructure.

**Idiom:** For `¬ ∃ i, P i` decidability without Mathlib, the pattern is:
```lean
match h : booleanCheck args with
| false => .isTrue (fun hex => absurd (iff.mpr hex) (by simp [h]))
| true  => .isFalse (fun hn => absurd (iff.mp h) hn)
```

### Phase B0: Create `CharPredicates.lean` (COMPLETE ✅)

Extract all character-level and string-level predicates into a shared module
that both Scanner.lean and Grammar.lean import. Each predicate gets three
parts: Bool (runtime), Prop (specification), iff theorem (drift alarm).

**Module:** `Lean4Yaml/CharPredicates.lean` — imports nothing from the project.

**Contents:**

| Predicate | Bool name | Prop name | Coupling theorem | YAML Spec |
|-----------|-----------|-----------|------------------|-----------|
| White space | `isWhiteSpaceBool` | `isWhiteSpaceProp` | `isWhiteSpace_iff` | §5.4 [34] |
| Line break | `isLineBreakBool` | `isLineBreakProp` | `isLineBreak_iff` | §5.4 [27–28] |
| Flow indicator | `isFlowIndicatorBool` | `isFlowIndicatorProp` | `isFlowIndicator_iff` | §7.4 [23] |
| Indicator | `isIndicatorBool` | `isIndicatorProp` | `isIndicator_iff` | §5.3 [22] |
| Printable | `isPrintableBool` | `isPrintableProp` | `isPrintable_iff` | §5.1 [1–4] |
| Plain first | `canStartPlainScalarBool` | `canStartPlainScalarProp` | `canStartPlainScalar_iff` | §7.3.3 [123] |
| Valid first | `validPlainFirstBool` | `validPlainFirstProp` | `validPlainFirst_iff` | §7.3.3 [123] |
| No colon-space | `noColonSpaceBool` | `noColonSpaceProp` | `noColonSpace_iff` | §7.3.3 [127] |
| No space-hash | `noSpaceHashBool` | `noSpaceHashProp` | `noSpaceHash_iff` | §7.3.3 [127] |
| No flow indicators | `noFlowIndicatorsBool` | `noFlowIndicatorsProp` | `noFlowIndicators_iff` | §7.3.3 [126] |

**Key design for `canStartPlainScalarProp` — 3-arg, matching Scanner:**

```lean
def canStartPlainScalarBool (c : Char) (next : Option Char) (inFlow : Bool) : Bool :=
  if c == '-' || c == '?' || c == ':' then
    match next with
    | some n => !isWhiteSpaceBool n && !isLineBreakBool n
                && !(inFlow && isFlowIndicatorBool n)
    | none => false
  else
    !isIndicatorBool c && !isWhiteSpaceBool c && !isLineBreakBool c

def canStartPlainScalarProp (c : Char) (next : Option Char) (inFlow : Bool) : Prop :=
  if c = '-' ∨ c = '?' ∨ c = ':' then
    match next with
    | some n => ¬isWhiteSpaceProp n ∧ ¬isLineBreakProp n
                ∧ ¬(inFlow ∧ isFlowIndicatorProp n)
    | none => False
  else
    ¬isIndicatorProp c ∧ ¬isWhiteSpaceProp c ∧ ¬isLineBreakProp c

theorem canStartPlainScalar_iff (c : Char) (next : Option Char) (inFlow : Bool) :
    canStartPlainScalarBool c next inFlow = true ↔
    canStartPlainScalarProp c next inFlow := by ...
```

**`validPlainFirstProp` — 2-arg, with `inFlow`:**

```lean
def validPlainFirstProp (content : String) (inFlow : Bool) : Prop :=
  match content.toList with
  | c :: n :: _ => canStartPlainScalarProp c (some n) inFlow
  | [c] => canStartPlainScalarProp c none inFlow
  | [] => True
```

**Moved helpers:** `hasAdjacentChars` + `hasAdjacentChars_iff` (from Phase A)
relocate into `CharPredicates.lean`. All `Decidable` instances relocate too.

**Steps:**
1. Create `CharPredicates.lean` with all Bool + Prop + iff + Decidable
2. Update `Scanner.lean`: import `CharPredicates`, delete inline predicate defs,
   use `Bool` names (e.g., `isWhiteSpaceBool` replaces `isWhiteSpace`)
3. Update `Grammar.lean`: import `CharPredicates`, delete inline predicate defs,
   use `Prop` names (e.g., `isWhiteSpaceProp` replaces `isWhiteSpace`)
4. Update all 33 proof files + tests for renamed predicates
5. Build: 213/213, tests: all passing, 0 sorry, 0 axioms

#### Phase B0 Reflections

**Status:** COMPLETE. 213/213 build, 0 sorry, 0 axioms.

**Unexpected challenges:**

1. **Bool ↔ Prop gap in `canStartPlainScalar_iff`**. The Bool version uses
   `if c == '-' || c == '?' || c == ':' then ...` (BEq/Bool) while the Prop
   version uses `if c = '-' ∨ c = '?' ∨ c = ':' then ...` (Prop equality). Lean
   treats these as structurally different `if` conditions.  The proof required
   manual `split` + helper lemma `neg_eq_false_iff_eq_true` rather than a simple
   `simp`. **Idiom learned:** when bridging Bool/Prop `if` conditions, use
   `split` to case-split on the Prop version, then convert each branch's
   Bool `if` with `simp [show c = '-' from ...]` or its negation.

2. **Missing `Bool.not_eq_true_iff`**. Lean 4.28 provides `Bool.eq_false_iff`
   but not `Bool.not_eq_true_iff`. The pattern `rw [Bool.eq_false_iff]` converts
   `¬(b = true)` to `b = false`, which is the correct replacement.

3. **CharClass.lean `canStartPlainScalar_base` proof cascade**. The old proof
   used `simp only [h1, h2, h3, Bool.false_or]` which worked because the old
   Grammar definition expanded the indicator list inline as `c ∉ [...]`. The new
   definition uses `¬ isIndicatorProp c`, requiring the proof to go through
   `isIndicator_equiv` instead.  Fixed with `rw [Bool.eq_false_iff]; intro h;
   exact hNotInd ((isIndicator_equiv c).mpr h)`.

4. **`noFlowIndicators` uses `isFlowIndicator` which was deleted**. The old
   `Grammar.noFlowIndicators` body referenced `Grammar.isFlowIndicator`, which
   was removed when character predicates moved to CharPredicates. Replaced with
   `abbrev noFlowIndicators := noFlowIndicatorsProp`.

5. **Hidden dependency: `ScannerCorrectness.lean`**. Initial `lake build` after
   Scanner.lean changes showed only 3 failing files. After fixing those, a 4th
   file (`ScannerCorrectness.lean`) appeared — it had been cached and was only
   rebuilt after its dependencies changed.

**Simplifications discovered:**

1. **`abbrev` aliases eliminate Decidable boilerplate**. Using
   `abbrev noColonSpace := noColonSpaceProp` instead of re-defining the
   predicate + separately proving `Decidable` meant zero proof obligations —
   Lean's kernel unfolds `abbrev` to the original + inherits the existing
   `Decidable` instance automatically.

2. **`export` re-exports eliminate `open` cascades**. Adding
   `export Lean4Yaml.CharPredicates (isPrintableProp ...)` in Grammar.lean's
   namespace means files that `open Lean4Yaml.Grammar` automatically see all
   CharPredicates names. This avoided adding `import CharPredicates` /
   `open CharPredicates` to every proof file that imports Grammar.

3. **Backward-compatible aliases in Scanner.lean** (`def isLineBreak :=
   isLineBreakBool`) kept ~60 internal usage sites working with zero renames.
   Only externally-qualified references (`Scanner.isLineBreak` in proof files)
   needed updating.

4. **`cases inFlow <;> simp [...]`** is the universal proof pattern for
   `inFlow : Bool` conditions. It splits into the `true`/`false` branches and
   `simp` handles each independently.

**Architecture outcome:**

```
CharPredicates.lean (standalone, ~470 lines)
  ├── Bool predicates: isPrintableBool, isLineBreakBool, ...
  ├── Prop predicates: isPrintableProp, isLineBreakProp, ...
  ├── iff theorems:    isPrintable_iff, isLineBreak_iff, ...
  └── Decidable instances for all Prop predicates

Scanner.lean ──imports CharPredicates──▸ uses Bool names via aliases
Grammar.lean ──imports CharPredicates──▸ re-exports Prop names; keeps
     canStartPlainScalar (1-arg compat), validPlainFirst (1-arg compat),
     isFoldAppendChar, isMarkerFollower, isCForbiddenPrefix
```

Files changed: CharPredicates.lean (new), Scanner.lean, Grammar.lean,
CharClass.lean, ScannerProofs.lean, ScannerDoubleQuoted.lean,
ScannerCorrectness.lean, EscapeResolution.lean — 8 files total.

### Phase B1: Add `Scannable` Predicate (COMPLETE ✅)

Define `Scannable` in `Grammar.lean` — the **scanner contract** that mirrors
the implementation's token-level guarantees. `Scannable` is the pre-compose
specification: it allows `.alias` nodes and threads flow context.

```lean
/-- Scanner contract: per-scalar character constraints in flow context. -/
def ScalarScannable (s : Scalar) (inFlow : Bool) : Prop :=
  s.style = .plain → s.content.length > 0 →
    validPlainFirstProp s.content inFlow
    ∧ noColonSpaceProp s.content
    ∧ noSpaceHashProp s.content
    ∧ (inFlow → noFlowIndicatorsProp s.content)

/-- Pre-compose tree validity. Allows aliases. Threads flow context. -/
inductive Scannable : YamlValue → Bool → Prop where
  | scalar (s : Scalar) (inFlow : Bool)
      (h : ScalarScannable s inFlow) :
      Scannable (.scalar s) inFlow
  | alias (name : String) (inFlow : Bool) :
      Scannable (.alias name) inFlow
  | sequence (style : CollectionStyle) (items : Array YamlValue)
      (tag anchor : Option String) (inFlow : Bool)
      (h : ∀ i : Fin items.size,
        Scannable items[i] (inFlow || style == .flow)) :
      Scannable (.sequence style items tag anchor) inFlow
  | mapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
      (tag anchor : Option String) (inFlow : Bool)
      (hk : ∀ i : Fin pairs.size,
        Scannable pairs[i].1 (inFlow || style == .flow))
      (hv : ∀ i : Fin pairs.size,
        Scannable pairs[i].2 (inFlow || style == .flow)) :
      Scannable (.mapping style pairs tag anchor) inFlow
```

**Context-threading rule:** Once a value is inside a `.flow` collection,
`inFlow` becomes `true` and stays `true` for all descendants. This matches
YAML 1.2.2 — flow context is inherited.

#### Phase B1 Reflections

**Status:** COMPLETE. 213/213 build, 0 sorry, 0 axioms.

B1 was purely additive — `Scannable` and `ScalarScannable` were added to
Grammar.lean without changing any existing definitions or proofs.

**Implementation note — `ScalarScannable` uses old 1-arg predicates:**
The B1 plan specified `validPlainFirstProp s.content inFlow` (2-arg Prop),
but the implementation uses `validPlainFirst s.content` (old 1-arg Bool
wrapper from `canStartPlainScalar`). This was a deliberate choice to keep
`ValidNode` UNCHANGED — the old `.plainScalarBlock` and `.plainScalarFlow`
constructors carry 1-arg `validPlainFirst` proofs, so using the same
predicate in `ScalarScannable` avoids a conversion step. The 1-arg version
is strictly stronger (rejects ALL indicators including `-`, `?`, `:`) so
it implies the 2-arg version for any `inFlow`.

**Files changed:** Grammar.lean (1 file — additive only).

### Phase B2: Update `Grammable` to Context-Aware (Option C) (COMPLETE ✅)

Replace the current `Grammable` with a context-aware version that threads
`inFlow : Bool` and excludes aliases (post-compose guarantee).

```lean
/-- Post-compose tree validity. No aliases. Context-aware. -/
inductive Grammable : YamlValue → Bool → Prop where
  | scalar (s : Scalar) (inFlow : Bool)
      (h : ScalarScannable s inFlow) :
      Grammable (.scalar s) inFlow
  -- NO alias constructor — Grammable is post-compose only
  | sequence (style : CollectionStyle) (items : Array YamlValue)
      (tag anchor : Option String) (inFlow : Bool)
      (h : ∀ i : Fin items.size,
        Grammable items[i] (inFlow || style == .flow)) :
      Grammable (.sequence style items tag anchor) inFlow
  | mapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
      (tag anchor : Option String) (inFlow : Bool)
      (hk : ∀ i : Fin pairs.size,
        Grammable pairs[i].1 (inFlow || style == .flow))
      (hv : ∀ i : Fin pairs.size,
        Grammable pairs[i].2 (inFlow || style == .flow)) :
      Grammable (.mapping style pairs tag anchor) inFlow
```

**Bridging theorem (Phase C1):**

```lean
theorem compose_scannable_to_grammable (doc : YamlDocument)
    (h : Scannable doc.value false) :
    Grammable (doc.compose.value) false
```

This theorem captures: alias resolution removes all `.alias` nodes,
anchor stripping doesn't affect character predicates, and the
composed tree satisfies `Grammable`.

**Update `ValidNode` constructors:**

```lean
| plainScalarBlock ... (firstValid : validPlainFirstProp content false) ...
| plainScalarFlow  ... (firstValid : validPlainFirstProp content true) ...
```

**Update existing proof files** that reference `Grammable` — they now
require the `inFlow` parameter. Top-level documents start with
`inFlow = false`.

#### Phase B2 Reflections

**Status:** COMPLETE. 213/213 build, 0 sorry, 0 axioms.

**Unexpected challenges:**

1. **`toYamlValue_grammable` became unprovable.** The old `Grammable` was
   context-free, so `∀ n : ValidNode, Grammable (toYamlValue n)` held
   trivially — every constructor had the right proofs. With context-aware
   `Grammable`, the theorem `∀ n, Grammable (toYamlValue n) inFlow` fails
   for any fixed `inFlow`:
   - At `false`: `.flowSeq` children need `Grammable child true`, but IH
     only gives `false`.
   - At `true`: `.plainScalarBlock` lacks `noFlowIndicators`.
   - At `∀ inFlow`: same `.plainScalarBlock` problem.

   **Root cause:** `ValidNode` is a free inductive — you can construct
   `.flowSeq [.plainScalarBlock "hello{bad}"]` which is syntactically valid
   but semantically inconsistent (block scalar with flow indicators inside
   a flow collection). Context-aware `Grammable` correctly rejects this,
   but `toYamlValue_grammable` was trying to prove ALL ValidNodes grammable.

2. **Solution: remove `toYamlValue_grammable` entirely.** The "no-junk"
   property it provided was actually guaranteed by construction in
   `yamlValue_has_witness`: when soundness constructs a witness `n` from
   `Grammable v inFlow`, it picks the RIGHT constructor (`.plainScalarBlock`
   at `false`, `.plainScalarFlow` at `true`), so the witness is always
   context-consistent. The separate `toYamlValue_grammable` was redundant.

**Simplifications discovered:**

1. **Return type simplification cascaded nicely.** Dropping
   `Grammable (toYamlValue n)` from the return types of `parseStream_complete`,
   `soundness_completeness_compose`, `grammable_has_witness`,
   `canonical_roundtrip_conditional`, and `emit_parse_has_witness` made all
   these theorems trivial wrappers around `yamlValue_has_witness`. The proof
   bodies reduced from multi-line compositions to single-line calls.

2. **`nofun` works for non-plain scalar `ScalarScannable`.** Since
   `ScalarScannable s inFlow` starts with `s.style = .plain → ...`, non-plain
   scalars (`.singleQuoted`, `.doubleQuoted`, `.literal`, `.folded`) are
   handled by `nofun` — identical to the old Grammable.

3. **`grammar_value_roundtrip` became conditional.** Previously unconditional
   (`∀ n, ∃ n', ...`), it now requires `Grammable (toYamlValue n) inFlow`.
   This is semantically correct: only context-consistent ValidNodes can
   roundtrip through the soundness bridge.

**Idiom learned:** When a free inductive type gains semantic constraints
(like flow context), properties proven "for all constructors" may become
unprovable. The fix is to carry the constraint as a hypothesis, not to
force the property to hold universally. This matches the standard approach
of conditional correctness theorems throughout the codebase.

**Architecture outcome:**

```
Grammar.lean:
  ScalarScannable s inFlow                    — scanner contract (B1)
  Scannable v inFlow                          — pre-compose validity + aliases (B1)
  Grammable v inFlow                          — post-compose validity, no aliases (B2)

ParserSoundness.lean:
  scalar_has_witness s inFlow h               — scalar witness at context
  yamlValue_has_witness v inFlow hg           — value witness at context
  parseStream_sound ... (hg : ∀ i, Grammable docs[i].value false)

ParserCompleteness.lean:
  grammar_value_roundtrip n inFlow hg         — conditional roundtrip
  parseStream_complete ... (hg : ∀ i, Grammable docs[i].value false)
  soundness_completeness_compose v (hg : Grammable v false)

ParserCorrectness.lean:
  parseStream_values_have_witnesses ... (hg : ∀ doc ∈ ..., Grammable ... false)
  parseStream_respects_grammar      ... (hg : ∀ doc ∈ ..., Grammable ... false)

ScannerEmitBridge.lean:
  grammable_has_witness v (hg : Grammable v false)
  canonical_roundtrip_conditional ... (hg : ∀ i, Grammable docs[i].value false)
  emit_parse_has_witness          ... (hg : ∀ i, Grammable docs[i].value false)
```

Files changed: Grammar.lean, ParserSoundness.lean, ParserCompleteness.lean,
ParserCorrectness.lean, ScannerEmitBridge.lean — 5 files total.

### Phase B3: Scanner Predicate Enforcement

**Goal.** Prove that every plain scalar token emitted by the scanner
satisfies `ScalarScannable`:

```lean
theorem scan_plain_scalar_valid (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens)
    (i : Fin tokens.size) (s : Scalar)
    (hs : tokens[i].val = .scalar s) (hplain : s.style = .plain)
    (hne : s.content.length > 0)
    (inFlow : Bool)
    (hctx : -- token i was scanned in flow context ↔ inFlow --) :
    ScalarScannable s inFlow
```

This uses the `_iff` theorems from `CharPredicates.lean` to bridge from
the scanner's Bool computations to the specification's Prop predicates.

#### B3 Architecture: Proof Strategy

The proof decomposes into three layers, modeled on the `scanNextToken`
refactoring documented in PLAN-scanNextToken-ScanInv.md:

```
scan_plain_scalar_valid                   [B3.5 — global theorem]
  ├── scanFiltered → scanLoop threading   [token provenance]
  └── scanPlainScalar_content_valid       [B3.4 — per-function theorem]
        └── collectPlainScalarLoop_preserves_contentInv  [B3.3 — loop invariant]
              ├── PlainContentInv definition            [B3.2]
              ├── collectPlainScalar_charDecision        [B3.1 — refactored sub-fn]
              ├── collectPlainScalar_lineBreakBlock      [B3.1 — refactored sub-fn]
              └── string property lemmas                [B3.0]
                    ├── noColonSpace_append_*            [CharPredicates.lean]
                    ├── noSpaceHash_append_*             [CharPredicates.lean]
                    ├── noFlowIndicators_append_*        [CharPredicates.lean]
                    ├── validPlainFirst_preserved_*      [CharPredicates.lean]
                    └── trimTrailingWS_preserves_*       [StringProperties.lean]
```

#### B3 Sub-phases

##### **B3.0: String Property Lemmas** (~10–15 theorems, ~200 lines) (COMPLETE ✅)

Append/prefix preservation lemmas for the four `ScalarScannable`
predicates. These go in `CharPredicates.lean` (Prop-level lemmas that
compose with the existing `_iff` theorems) and `StringProperties.lean`
(for `trimTrailingWS`).

Required lemmas (representative, not exhaustive):

| Lemma | Module | Purpose |
|-------|--------|---------|
| `noColonSpace_append_char h_prev h_not_colon_space` | CharPredicates | `: ` not introduced by append |
| `noSpaceHash_append_char h_prev h_not_space_hash` | CharPredicates | ` #` not introduced by append |
| `noFlowIndicators_append_nonflow h_prev h_not_flow` | CharPredicates | Flow indicator not introduced |
| `validPlainFirst_prefix h_first` | CharPredicates | First char(s) unchanged by append |
| `noColonSpace_concat h1 h2 h_boundary` | CharPredicates | Boundary safety when concatenating |
| `noSpaceHash_concat h1 h2 h_boundary` | CharPredicates | Boundary safety when concatenating |
| `hasAdjacentChars_append_iff` | CharPredicates | General adjacent-pair append decomposition |
| `trimTrailingWS_preserves_noColonSpace` | StringProperties | Prefix preservation under WS trim |
| `trimTrailingWS_preserves_noSpaceHash` | StringProperties | Prefix preservation under WS trim |
| `trimTrailingWS_preserves_noFlowIndicators` | StringProperties | Prefix preservation under WS trim |
| `trimTrailingWS_preserves_validPlainFirst` | StringProperties | First char unchanged by suffix trim |

**Key insight for `trimTrailingWS`:** `trimTrailingWS s` removes trailing
spaces/tabs. This is a *suffix* operation — it cannot introduce new
adjacent pairs and cannot change the first character. So the `_preserves_`
lemmas should be straightforward: `trimTrailingWS s` is a prefix of `s`
(modulo trailing WS), and all four predicates are prefix-stable.

###### B3.0 Reflections

**Status:** Complete. 213/213 build, 0 sorry, 0 axioms, 0 warnings.

**Delivered: 31 theorems** (25 in CharPredicates.lean, 6 in StringProperties.lean)

*CharPredicates.lean — new sections:*

| Section | Theorems | Key result |
|---------|----------|------------|
| hasAdjacentChars append decomposition | 4 | `hasAdjacentChars_append`: full 3-disjunct `↔` decomposition for `xs ++ ys` |
| noColonSpace preservation | 3 | `_empty`, `_push`, `_append` — covers all accumulation patterns |
| noSpaceHash preservation | 3 | Same structure as noColonSpace |
| noFlowIndicators preservation | 3 | `_empty`, `_push`, `_append` via pointwise membership |
| validPlainFirst preservation | 3 | `_empty`, `_push_of_nonempty`, `_append_of_nonempty` (requires ≥2 chars) |
| Boundary helpers | 7 | `mem_of_getElemQ_some`, `not_space_of_plainSafe`, whitespace `getLast?` cases, `noColonSpaceProp_of_whitespace`, `noSpaceHashProp_of_whitespace`, `noFlowIndicatorsProp_of_whitespace` |
| **Subtotal** | **23 + 2 earlier** | |

*StringProperties.lean — new §4 Trim Preservation:*

| Theorem | Purpose |
|---------|---------|
| `reverse_dropWhile_reverse_isPrefix` | Trimmed list is a prefix of the original |
| `hasAdjacentChars_false_of_append` | Prefix inherits no-adjacent-chars from whole |
| `trim_preserves_noColonSpace` | Trimming preserves no `: ` |
| `trim_preserves_noSpaceHash` | Trimming preserves no ` #` |
| `trim_preserves_noFlowIndicators` | Trimming preserves no flow indicators |
| `trim_preserves_validPlainFirst` | Trimming preserves first-char validity (≥2 chars) |

**Unexpected challenges:**

1. **`String` is `ByteArray`-backed in Lean 4.28.** Anonymous constructor
   `⟨s.toList ++ t.toList⟩` silently type-checks against `ByteArray`, not
   `List Char`. Must use `String.ofList`/`(s ++ t)` with `String.toList_append`
   for round-tripping.

2. **`List.getElem?_mem` does not exist.** No stdlib lemma converts
   `l[i]? = some a → a ∈ l`, so we wrote a private `mem_of_getElemQ_some`
   using induction on `l` and `List.getElem?_cons_zero` + `Option.some.injEq`.

3. **`Bool.not` vs propositional `¬` in `_iff` lemmas.** `noColonSpaceBool`
   unfolds to `!hasAdjacentChars ...`, producing hypotheses of the form
   `(!b) = true`. The simp lemma `Bool.not_eq_true` operates on
   propositional `¬(b = true)`, not `Bool.not b = true`. Fix:
   `Bool.not_inj : (!x) = (!y) → x = y` converts `(!b) = true` to
   `b = false` since `true = !false` definitionally.

4. **`validPlainFirstProp` is sensitive to the `next` argument.** Pushing a
   single character onto a 1-character string `[c]` changes the `next` argument
   from `none` to `some c`. When `c ∈ {'-', '?', ':'}`,
   `canStartPlainScalarProp c none inFlow = False`, so a 1-char string can
   never satisfy the predicate anyway. Required strengthening the push/append
   preconditions to `∃ x y rest, content.toList = x :: y :: rest`.

5. **`∨` is right-associative.** `hasAdjacentChars_append` produces a
   right-associative disjunction `A ∨ B ∨ C` (= `A ∨ (B ∨ C)`). Must use
   `rintro (h | h | h)`, not `rintro ((h | h) | h)`.

**Simplifications discovered:**

- **`hasAdjacentChars_append` as universal decomposition.** All four
  `noColonSpace`/`noSpaceHash` predicates reduce to `hasAdjacentChars`,
  so a single append `↔` theorem handles all cases uniformly.

- **`reverse_dropWhile_reverse_isPrefix` as the sole trim argument.** Once we
  proved the trimmed list is a prefix (`∃ suf, cs = trimmed ++ suf`), all four
  trim preservation theorems follow from the corresponding `_of_append` lemma.

- **Whitespace contradictions close goals directly.** For concrete characters
  like `':'`, `simp [isWhiteSpaceProp] at hws` evaluates the BEq to `False`
  and closes the goal immediately — no `rcases` needed.

**Idioms established:**

- **BEq→Prop conversion:** `simp only [isWhiteSpaceProp, beq_iff_eq]` converts
  `(c == ' ') = true` to `c = ' '`.
- **`Bool.not` conversion:** `Bool.not_inj h` where `h : (!b) = true` yields
  `b = false`.
- **Concrete char contradiction:** `simp [isWhiteSpaceProp] at hws` when `hws`
  asserts whitespace on a non-whitespace char.
- **Right-associative `∨` destruction:** `rintro (h | h | h)` for 3-way.

##### **B3.1: Refactor `collectPlainScalarLoop`** (~100 lines changed in Scanner.lean) (COMPLETE ✅)

The current `collectPlainScalarLoop` (Scanner.lean L1566–1655) has ~90
lines and 12+ branch points — beyond the ≤7 rule established in the
`scanNextToken` refactoring. Decompose into sub-functions:

```
collectPlainScalarLoop s content spaces fuel inFlow contentIndent inputEnd
  match fuel with
  | 0 => ...
  | fuel' + 1 =>
    match s.peek? with
    | none => ...
    | some c =>
      ├── collectPlainScalar_terminates?        [B3.1a: ~5 branches]
      │     # with spaces, `: `, flow indicator, doc boundary
      ├── collectPlainScalar_lineBreakBlock     [B3.1b: ~5 branches]
      │     consumeNewline, skipBlanks, skipSpaces, indent/docboundary
      └── collectPlainScalar_continueChar       [B3.1c: ~3 branches]
            whitespace accumulate, isPlainSafeBool, content append
```

**Decomposition detail:**

| Sub-function | Lines (est.) | Branches | Character coverage |
|-------------|-------------|----------|--------------------|
| `collectPlainScalar_terminates?` | ~25 | 5 | `#`, `:`, flow ind., doc boundary, general |
| `collectPlainScalar_lineBreakBlock` | ~25 | 5 | newline, blank skip, indent, doc boundary, fold |
| `collectPlainScalar_continueChar` | ~15 | 3 | whitespace, plainSafe, unsafe |
| `collectPlainScalarLoop` (simplified) | ~30 | 5 | fuel, peek, terminate?, linebreak, continue |

The flow-context line break path (L1613–1623) stays inline since it's
only ~5 lines using the existing `foldQuotedNewlines` helper.

###### B3.1 Reflections

**Delivered:**

- **Scanner.lean:** Two new helper functions extracted from `collectPlainScalarLoop`:
  - `collectPlainScalar_terminates?` (~35 lines): non-recursive, checks 4
    termination conditions (`#`+spaces, `:`+blank, flow indicator, doc boundary).
    Returns `Option PlainScalarResult`. All `some` branches preserve `state = s`.
  - `collectPlainScalar_handleBlockLineBreak` (~25 lines): non-recursive, handles
    block-context line breaks via `consumeNewline → skipBlankLinesLoop → skipSpaces`.
    Returns `Option (String × ScannerState)` — `none` = under-indented/doc-boundary
    terminate, `some (content', s')` = continue with folded whitespace.
  - `collectPlainScalarLoop` reduced from ~90 lines / 12+ branches to ~70 lines /
    ~7 top-level branches.
  - Note: the planned `collectPlainScalar_continueChar` was NOT extracted — the
    remaining continue logic (whitespace accumulate / plainSafe check / content
    append) is only ~10 lines with 3 straightforward branches, so extraction would
    over-engineer. Two sub-functions was the sweet spot.

- **ScannerCorrectness.lean:** 5 proof changes:
  - `collectPlainScalar_terminates?_state` (new, ~25 lines): universal helper in
    `ScanHelpers` namespace proving `result.state = s` for any `some` return from
    `_terminates?`. Pattern: `unfold; split` with special `:` branch needing
    `simp only []` then 2 nested splits for `match next` and `if terminates`.
  - 4 existing proofs rewritten to match new loop structure:
    `_preserves_tokens`, `_preserves_simpleKey`, `_preserves_simpleKeyStack`,
    `_offset_ge`.

- **Build:** 213/213, 0 sorry, 0 axioms, 0 warnings.

**Unexpected challenges:**

1. **Dependency ordering blocks helper lemma placement.** Initially tried adding
   `_handleBlockLineBreak_preserves_tokens/simpleKey/simpleKeyStack/offset_ge`
   helper lemmas near `_terminates?_state` in the ScanHelpers namespace. Failed
   because they need `skipBlankLinesLoop_preserves_*` lemmas that are defined
   LATER in the file (some outside ScanHelpers entirely). Could have placed each
   helper just before its consumer, but inline unfold was simpler.

2. **Inline unfold as alternative to helper lemmas.** Instead of separate lemmas,
   each proof unfolds `_handleBlockLineBreak` directly:
   ```lean
   unfold collectPlainScalar_handleBlockLineBreak at hblk
   simp only [] at hblk
   split at hblk <;> try contradiction
   split at hblk <;> try contradiction
   have := Prod.mk.inj (Option.some.inj hblk)
   rw [← this.2, skipSpaces_preserves_X, skipBlankLinesLoop_preserves_X,
       consumeNewline_preserves_X]
   ```
   This ~6-line pattern is repeated 4 times. Acceptable duplication given the
   dependency ordering constraint.

3. **`Option (A × B)` destructuring idiom.** When `split at h` decomposes
   `match f with | none | some (a, b)`, use `rename_i a b hblk` to name the
   pair components and hypothesis. Then `Prod.mk.inj (Option.some.inj hblk)`
   gives `.1 : fst = a` and `.2 : snd = b` for rewriting.

4. **Namespace qualification outside `ScanHelpers`.** `_terminates?_state` is
   defined inside `namespace ScanHelpers` (ends L2389). The `_preserves_tokens`
   proof (L870) is also inside ScanHelpers — no qualification needed. But
   `_preserves_simpleKey` (L2717), `_preserves_simpleKeyStack` (L3322), and
   `_offset_ge` (L6066) are all outside, requiring `ScanHelpers.` prefix.

5. **`_offset_ge` differs from field-equality proofs.** The first 3 proofs show
   `result.state.field = s.field` (closed by `rfl` after rewrite). `_offset_ge`
   shows `result.state.offset ≥ s.offset` — after rewriting with `_terminates?_state`,
   the goal becomes `s.offset ≥ s.offset`, which needs an explicit `Nat.le_refl _`.
   Similarly, the block linebreak continuation uses `Nat.le_trans` chains instead
   of `rw` chains.

**Simplifications vs plan:**

- Planned 3 sub-functions, delivered 2. `_continueChar` wasn't worth extracting.
- Plan estimated ~100 lines changed; actual was ~60 in Scanner.lean + ~120 in
  ScannerCorrectness.lean (underestimated proof repair cost).
- Plan said "no proof impact (behavioral equivalence)" — incorrect. All 4
  `collectPlainScalarLoop_*` proofs broke and needed full rewrites because they
  `unfold collectPlainScalarLoop` and match on the internal branch structure.

##### **B3.2: Define `PlainContentInv` loop invariant** (~30 lines, new proof file) (COMPLETE ✅)

```lean
/-- Loop invariant for `collectPlainScalarLoop` content correctness.

    Tracks that the accumulated `content` string satisfies all four
    `ScalarScannable` predicates, and that `spaces` contains only
    whitespace (ensuring it cannot introduce forbidden patterns when
    flushed into content). -/
def PlainContentInv (content : String) (spaces : String)
    (inFlow : Bool) (firstChar : Option (Char × Option Char)) : Prop :=
  -- First character validity (remembered from entry)
  (match firstChar with
   | some (c, next) => canStartPlainScalarProp c next inFlow
   | none => True) ∧
  -- Content properties
  noColonSpaceProp content ∧
  noSpaceHashProp content ∧
  (inFlow → noFlowIndicatorsProp content) ∧
  -- Spaces accumulator is pure whitespace
  (∀ c ∈ spaces.toList, isWhiteSpaceProp c) ∧
  -- Boundary safety: last char of content is not `:` when spaces is empty
  -- (needed for noColonSpace preservation at content++spaces++c boundary)
  (spaces = "" → content.length > 0 →
    content.toList.getLast? ≠ some ':' ∨ True)
    -- ^ refined during implementation; sketch shows the kind of
    --   boundary condition needed
```

This goes in a new file `Lean4Yaml/Proofs/ScannerPlainContent.lean`.

###### B3.2 Reflections

**Delivered:**

- **New file:** `Lean4Yaml/Proofs/ScannerPlainContent.lean` (~50 lines)
  - `PlainContentInv` structure with 5 fields:
    1. `content_noColonSpace` — no `: ` pattern in content
    2. `content_noSpaceHash` — no ` #` pattern in content
    3. `content_noFlowIndicators` — no flow indicators when `inFlow`
    4. `spaces_whitespace` — spaces buffer is pure whitespace
    5. `boundary_colon` — content ending with `:` implies spaces is empty
  - `PlainContentInv.empty` — base case for empty content/spaces

- **Build:** 215/215 (was 213 pre-B3.2), 0 sorry, 0 axioms, clean.

**Design decisions vs plan:**

1. **Dropped `firstChar` parameter.** The plan tracked `firstChar : Option
   (Char × Option Char)` for `canStartPlainScalarProp`. Analysis showed this is
   unnecessary: `validPlainFirst` depends only on the first character of content,
   which never changes once set (we only append). The entry condition can be
   established once in B3.4 via `scanPlainScalar`'s `canStartPlainScalarBool` check
   and carried separately — no need to thread it through the loop invariant.

2. **Added `boundary_colon` condition.** The plan's sketch had a placeholder
   `content.toList.getLast? ≠ some ':' ∨ True` (trivially true). Replaced with
   the real condition: `content.toList.getLast? = some ':' → spaces = ""`. This
   is the key boundary safety property: it prevents `: ` from appearing at the
   content–spaces junction when spaces are flushed. It is maintainable because
   the scanner's `_terminates?` ensures a non-terminating `:` is always followed
   by a non-whitespace char (which gets appended to content before any whitespace
   can accumulate in spaces).

3. **Used `structure` instead of nested `∧`.** Named fields make proof
   construction and destruction cleaner than anonymous conjunction chains.

4. **No `noSpaceHash` boundary condition needed.** Analysis showed that the
   `#` termination check in `_terminates?` (when `spaces.length > 0`) and the
   fact that spaces contains only whitespace (no `#`) fully prevent ` #` at
   all boundaries without additional invariant tracking.

5. **`List.not_mem_nil` vs `simp [String.toList]`.** Initial attempt used
   `absurd hc (List.not_mem_nil _)` for the `spaces_whitespace` of the empty
   case, but `"".toList` doesn't reduce to `[]` at the type level in Lean 4.28.
   Fixed with `simp [String.toList]` which handles the normalization.

##### **B3.3: Prove `collectPlainScalarLoop_preserves_contentInv`** (~300–500 lines) (COMPLETE ✅)

The core theorem:

```lean
theorem collectPlainScalarLoop_preserves_contentInv
    (s : ScannerState) (content spaces : String) (fuel : Nat)
    (inFlow : Bool) (contentIndent : Nat) (inputEnd : Nat)
    (firstChar : Option (Char × Option Char))
    (h_inv : PlainContentInv content spaces inFlow firstChar)
    (result : PlainScalarResult)
    (h_ok : collectPlainScalarLoop s content spaces fuel
              inFlow contentIndent inputEnd = .ok result) :
    PlainContentInv result.content "" inFlow firstChar
```

**Proof approach:** Structural induction on `fuel`. Each branch calls the
corresponding B3.0 string property lemma and B3.1 sub-function's spec.

**Estimated effort by branch (from PLAN-scanNextToken experience):**

| Branch | Risk | Proof lines (est.) | Notes |
|--------|------|-------------------|-------|
| fuel=0 | Low | 5 | Identity |
| peek=none | Low | 5 | Identity |
| `#` + spaces | Low | 10 | Terminate — invariant carries through |
| `:` terminate | Low | 10 | Terminate |
| `:` continue | **High** | 40 | Must show next char is non-blank via `peekAt?` |
| flow indicator | Low | 10 | Terminate |
| doc boundary | Low | 5 | Terminate |
| line break (flow) | **Medium** | 50 | `foldQuotedNewlines` content + boundary check |
| line break (block) | **High** | 80 | Multi-step: fold produces ` ` or `\n`s, must show no `: `/` #` at boundary |
| whitespace | Low | 15 | Spaces accumulator grows; content unchanged |
| regular char | Medium | 30 | `isPlainSafeBool` → content properties preserved |
| unsafe char | Low | 5 | Terminate |
| **Total** | | **~265** | Budget 500 for build-fix cycles |

**Highest-risk branch: block-context line break.** After folding,
`content' = content ++ " "` (single fold) or `content ++ "\n"*n`
(multi-fold). The ` ` from single-fold could create a ` #` hazard
if the continuation starts with `#`. Must prove this cannot happen:
either `#` at continuation start terminates the scalar (it terminates
when `spaces.length > 0`), or `spaces` is reset to `""` after fold
and `#` falls through to content append. The latter case produces
`content ++ " #"` — which would violate `noSpaceHash`. This may
require a scanner fix or a more refined analysis showing that `#` at
the start of a continuation line is preceded by indent spaces (which
the scanner consumes), leaving `s_after_spaces` past the `#` if it
was a comment. **Investigation needed during implementation.**

###### B3.3 Reflections

**Status:** Complete. 215/215 build, 0 sorry, 0 axioms, 0 warnings.

**Delivered:**

- **File:** `Lean4Yaml/Proofs/ScannerPlainContent.lean` expanded from ~50 to ~510 lines
  - 23 top-level theorems/definitions (including helpers)
  - Main theorem: `collectPlainScalarLoop_preserves_contentInv` — fully proven, 0 sorry
  - New definition: `BoundaryHash` — an invariant discovered during proof that was NOT anticipated in B3.2

**Unexpected change to `PlainContentInv`:** B3.2's reflections stated
"No `noSpaceHash` boundary condition needed" based on static analysis.
This turned out to be **wrong**. During the proof, the plainSafe `#`
append case revealed a gap: when `content` ends with `' '`, `spaces = ""`,
and `c = '#'`, `_terminates?` does NOT fire (the `#` check requires
`spaces.length > 0`). The scanner happily appends `'#'` to content,
producing `content ++ "#"` — violating `noSpaceHashProp` at the
boundary. This required adding `BoundaryHash` as a **separate hypothesis**
to the theorem (not a `PlainContentInv` struct field; see below for why).

Also, `boundary_colon` was strengthened from the B3.2 form
(`content.toList.getLast? = some ':' → spaces = ""`) to also couple
to the scanner state: `→ spaces = "" ∧ (∀ n, s.peek? = some n → ¬isBlankProp n)`.
This was needed because the fold cases produce `content ++ " "` or
`content ++ replicate '\n'`, and showing `noColonSpaceProp` at the
boundary requires knowing the next character after fold isn't blank.

**Resolution of open question (block linebreak + `#`):** The B3.3
plan flagged "Investigation needed during implementation" for the case
where `#` appears at the start of a continuation line after block fold.
The answer: the B3.1 scanner fix — adding
`match s'.peek? with | some '#' => terminate | _ => recurse` after
`_handleBlockLineBreak` — is exactly what makes the proof work. After
fold, if the next char is `#`, we terminate (invariant preserved trivially
via `transfer_nonblank_peek`). If not, `BoundaryHash` for the recursive
call is satisfied directly by `s'.peek? ≠ some '#'`.

**Key discovery: why `BoundaryHash` is NOT part of `PlainContentInv`:**

The `#` termination cases (after block/flow fold) output
`{content, spaces, state := s'}` where `s'.peek? = some '#'`. If
`content` ended with `' '` and `spaces = ""`, a BoundaryHash struct
field would require `'#' ≠ '#'` — impossible. Since these are terminal
results (no recursion follows), the caller needs only the content
properties (noColonSpace, noSpaceHash, etc.), not the loop-internal
boundary condition. Making BoundaryHash a separate hypothesis avoids
this impossibility while still providing the induction step.

**Helper lemma inventory:**

| Helper | Lines | Purpose |
|--------|-------|---------|
| `advance_peek_eq_peekAt_one` | ~15 | `s.advance.peek? = s.peekAt? 1` when `peek? = some _` |
| `terminates_none_colon_peekAt_nonblank` | ~15 | Non-terminating `:` implies next char is non-blank |
| `noColonSpaceProp_space` / `_replicate_newline` | ~10 ea | Content properties for fold strings |
| `noSpaceHashProp_space` / `_replicate_newline` | ~10 ea | Content properties for fold strings |
| `noFlowIndicatorsProp_space` / `_replicate_newline` | ~10 ea | Content properties for fold strings |
| `replicate_getElem?_char` | ~5 | Elements of `List.replicate` equal the replicated element |
| `getLast_append_space` / `_replicate_newline` | ~10 ea | Last char of `content ++ fold` |
| `head_space` / `head_replicate_newline` | ~5 ea | First char of fold string |
| `hash_not_blank` | ~2 | `¬isBlankProp '#'` |
| `terminates_preserves_all` | ~20 | `_terminates? = some r → r.content = content ∧ r.spaces = spaces ∧ r.state = s` |
| `PlainContentInv.transfer_nonblank_peek` | ~10 | Transfer invariant to new state with known non-blank peek |
| `handleBlockLineBreak_content_form` | ~15 | Extracts fold form from block handler result |
| `foldQuotedNewlines_result_form` | ~20 | Extracts fold form from flow handler result |
| `PlainContentInv.of_fold` | ~30 | Generic constructor for fold-appended content invariant |

**Unexpected difficulties:**

1. **`split` failure on nested `have/let/match`.** The `:` branch of
   `_terminates?` uses `have next := s.peekAt? 1; have terminates := match next with ...`
   which defeats `split at h`. The `split` tactic cannot see through
   `have` bindings to find the `match`. Solution: `simp only at h` to
   reduce bindings first, then `split at h <;> (split at h <;> ...)` for
   the nested match.

2. **`do`-notation desugaring blocks `split`.** `foldQuotedNewlines` uses
   `do`-notation which desugars to nested `bind`/`pure`. `split at h`
   cannot operate on `if` conditions buried under the desugaring.
   Solution: `dsimp only at h` reduces the desugaring, exposing the
   branching structure.

3. **`String` is `ByteArray`-backed.** Deriving `spaces = ""` from
   `spaces.toList = []` requires `String.ext_iff.mpr` — not obvious when
   string internals are opaque. Similarly, `spaces.length > 0` from
   `spaces.toList = x :: xs` needs `rw [← String.length_toList]; simp [hl]`.

4. **`List.Mem` constructor naming.** `List.Mem.head _` is the correct
   form, not `List.mem_cons_self _ _` (which takes different arguments
   in Lean 4.28). Discovered by trial.

5. **BoundaryHash maintenance through whitespace.** When `c` is whitespace
   and `spaces.push c` grows, the `spaces = ""` premise of BoundaryHash
   becomes false — but proving `spaces.push c ≠ ""` requires going through
   `String.toList_push` and `simp`, not just `nofun`.

**Simplifications vs plan:**

- **Plan estimated ~265 proof lines; actual core theorem is ~190 lines.**
  The `PlainContentInv.of_fold` generic helper eliminated massive
  duplication between block and flow linebreak cases — both use the
  identical pattern `of_fold inv c hpeek hc_lb fold hfold hpeek_ne`.

- **`terminates_preserves_all` eliminated `transfer_nonblank_peek` for
  the termination case.** Originally tried to transfer the invariant to
  a new state, but `terminates_preserves_all` proved `r.state = s`,
  allowing a direct rewrite + `exact inv`.

- **Whitespace case is 15 lines, not 15.** The plan estimated correctly
  here — content unchanged, `spaces.push c` grows, `boundary_colon`
  discharged by contradiction (whitespace `c` is blank, violating the
  `¬isBlankProp n` conclusion).

- **Block and flow linebreak cases are structurally identical.** Despite
  different fold functions (`_handleBlockLineBreak` vs `foldQuotedNewlines`),
  once the fold form is extracted (`" "` or `replicate '\n'`), the
  `of_fold` + recursive `ih` pattern is the same 15 lines in both cases.

##### **B3.4: Prove `scanPlainScalar_content_valid`** (~50–100 lines)

Per-function theorem at the `scanPlainScalar` level:

```lean
theorem scanPlainScalar_content_valid (s s' : ScannerState)
    (h : scanPlainScalar s = .ok s') :
    let idx := s.tokens.size
    ∀ (h_bound : idx < s'.tokens.size),
      match s'.tokens[idx].val with
      | .scalar content .plain =>
          ScalarScannable ⟨content, .plain⟩ s.inFlow
      | _ => True
```

**Proof structure:**
1. Unfold `scanPlainScalar` to expose `collectPlainScalarLoop` call
2. Establish base case: `canStartPlainScalarBool c (peekAt? 1) inFlow`
   gives `PlainContentInv "" "" inFlow (some (c, peekAt? 1))`
3. Apply B3.3 to get `PlainContentInv result.content "" inFlow ...`
4. Apply `trimTrailingWS_preserves_*` lemmas from B3.0
5. Combine with `canStartPlainScalar_iff` to get `validPlainFirstProp`
6. Package as `ScalarScannable`

###### B3.4 Reflections

**Status:** Complete. 217/217 build, 1 sorry (documented `validPlainFirstProp` gap), 0 axioms.

**Delivered:**

- **New file:** `Lean4Yaml/Proofs/ScannerPlainScalar.lean` (~160 lines)
  - 5 theorems: `trimTrailingWS_eq`, `trimTrailingWS_noColonSpace`,
    `trimTrailingWS_noSpaceHash`, `trimTrailingWS_noFlowIndicators`,
    `validPlainFirst_sorry`
  - Main theorem: `scanPlainScalar_content_valid` — complete proof
    modulo the 1 sorry in `validPlainFirst_sorry`
- **Updated:** `Lean4Yaml.lean` — added import
- **Stale definition cleanup** (prerequisite discovered during B3.4 analysis):
  - Deleted `canStartPlainScalar` (1-arg) and `validPlainFirst` (1-arg) from `Grammar.lean`
  - Updated `ValidNode.plainScalarBlock/Flow` to use `validPlainFirstProp content false/true`
  - Updated `NodeToValue` constructors similarly
  - Updated `ScalarScannable` to use `validPlainFirstProp s.content inFlow`
  - Fixed downstream: `Soundness.lean`, `CharClass.lean`, `ParserCorrectness.lean`

**Proof technique: `Array.getElem_push` + `dite_false`:**

The main proof difficulty was reducing `(s.tokens.push tok)[s.tokens.size].val`
inside a `match` expression. `Array.getElem_push_eq` (which states
`(xs.push x)[xs.size] = x`) could not be applied via `simp` because
the implicit bound proof term didn't unify with the goal's bound proof.

Solution: Use the conditional form `Array.getElem_push` first
(`(xs.push x)[i] = if h : i < xs.size then xs[i] else x`), which
`simp` CAN apply since it doesn't need proof-term unification. Then
prove `¬(idx < s.tokens.size)` via `Nat.lt_irrefl` and apply `dite_false`
to reduce to the `else` branch:

```lean
simp only [Array.getElem_push]
have h_not_lt : ¬(idx < s.tokens.size) := Nat.lt_irrefl _
simp only [h_not_lt, dite_false]
```

This two-step pattern (`getElem_push` → `dite_false`) is reusable for
any proof that needs to identify the last-pushed token in an array.

**Known gap: `validPlainFirstProp` for single-exception-char content:**

The scanner checks `canStartPlainScalarBool c (peekAt? 1) inFlow` against
the **input** lookahead, but the grammar's `validPlainFirstProp` checks
against the **content** lookahead. For exception chars (`-`, `?`, `:`)
where the second input char terminates the loop immediately (e.g., input
`?:` at EOF → content `"?"`), the content has no second character, so
`validPlainFirstProp "?" inFlow = canStartPlainScalarProp '?' none inFlow = False`.

This is documented in the module docstring with three resolution options
for future work. The pragmatic choice was to use `sorry` with clear
documentation rather than block the other three fully-provable properties.

**Deviation from plan:**

- Plan estimated ~50–100 lines; actual file is ~160 lines (with
  documentation and helpers)
- Plan step 2 ("establish base case from `canStartPlainScalarBool`")
  was identified as unnecessary — `PlainContentInv.empty` provides the
  base case directly (content = "")
- Plan step 5 ("combine with `canStartPlainScalar_iff`") was identified
  as unprovable for the single-exception-char edge case (see above)
- The stale definition cleanup was not anticipated in the plan but was
  essential — `ScalarScannable` used a 1-arg `validPlainFirst` that
  didn't match the scanner's 3-arg `canStartPlainScalarBool`

##### **B3.5: Prove `scan_plain_scalar_valid`** (~100–200 lines)

Thread B3.4 through the `scanFiltered → scanLoop → scanNextToken →
dispatchContent → scanPlainScalar` chain. This requires:

1. **Token provenance:** A theorem that each token in `scanFiltered`
   output was produced by exactly one `scanNextToken` call. Existing
   structural theorems (`scanPlainScalar_adds_one_token`,
   `scanPlainScalar_preserves_prefix`) provide the foundation.

2. **Flow context propagation:** Track `s.inFlow` through the dispatch
   chain to match the `inFlow` parameter of `ScalarScannable`.

This is the most infrastructure-heavy sub-phase. If the token provenance
machinery proves too complex, an alternative is to strengthen the main
`scanLoop` invariant to carry `ScalarScannable` as an additional property
(similar to how `ScanInv` was threaded through in the `scanNextToken`
refactoring).
 
###### B3.5 Reflections

#### Module Decisions

**`TokenPredicates.lean` — NOT needed.** `ScalarScannable` operates on
string content, not on token structure. The relevant predicates
(`validPlainFirst`, `noColonSpace`, `noSpaceHash`, `noFlowIndicators`)
are all string-level and already live in `CharPredicates.lean`. There is
no token-level Bool/Prop coupling needed.

**`ScannerPredicates.lean` — NOT needed.** The scanner contract
(`ScalarScannable`) is already defined in `Grammar.lean` where it belongs
(it's the specification, not a scanner-internal concept). No additional
scanner-level predicate module is required.

**New proof file: `Lean4Yaml/Proofs/ScannerPlainContent.lean`.**
Houses the `PlainContentInv` definition and the
`collectPlainScalarLoop_preserves_contentInv` theorem. Follows the
existing naming convention (`ScannerScalar.lean`, `ScannerContracts.lean`,
`ScannerWhitespace.lean`, etc.). Imports `CharPredicates` for `_iff`
theorems and `Scanner` for function definitions.

**Existing files extended:**
- `CharPredicates.lean` — append/concat preservation lemmas (~10 theorems)
- `StringProperties.lean` — `trimTrailingWS_preserves_*` lemmas (~5 theorems)

#### Function Refactoring Analysis

The user identified 11 functions for potential refactoring. Analysis by
B3 relevance:

| Function | Lines | Branches | B3 Need | Refactor? | Notes |
|----------|-------|----------|---------|-----------|-------|
| `collectPlainScalarLoop` | 90 | 12+ | **CRITICAL** | **YES** | Decompose per B3.1 |
| `scanNextToken_dispatchContent` | 40 | 8 | Threading | No | Already refactored; needs content predicate theorem |
| `skipToContentWs` | 30 | 7 | No | No | Already at ≤7 threshold |
| `skipToContentLoop` | 25 | 5 | No | No | Tractable as-is |
| `scanValueValidate` | 22 | 5 | No | No | Tractable as-is |
| `scanYamlDirective` | 19 | 5 | No | No | Tractable as-is |
| `collectDoubleQuotedLoop` | 48 | 8 | No* | Maybe | *Non-plain: ScalarScannable trivially satisfied |
| `collectSingleQuotedLoop` | 40 | 6 | No* | No | *Same: vacuously true for non-plain styles |
| `foldBlockContent` | 50 | 4 | No | No | Pure function; different proof style |
| `autoDetectBlockScalarIndentLoop` | 36 | 6 | No | No | Tractable as-is |
| `scanBlockScalarBody` | 41 | 5 | No | No | Already decomposed |

*Non-plain scalar tokens satisfy `ScalarScannable` vacuously:
`ScalarScannable s inFlow` starts with `s.style = .plain → ...`, so
any `s.style ≠ .plain` scalar is trivially scalarScannable via `nofun`.

**Conclusion:** Only `collectPlainScalarLoop` needs structural refactoring
for B3. The other 10 functions are either already tractable, irrelevant
to B3, or would be relevant only in future phases (E/F) for broader
scanner property verification.

#### Risk Assessment

| Sub-phase | Risk | Rationale |
|-----------|------|-----------|
| B3.0 | Low | Mechanical string lemmas; well-scoped |
| B3.1 | Low | Structural refactoring; no proof impact (behavioral equivalence) |
| B3.2 | Low | Definition only |
| B3.3 | **High** | 12-branch inductive proof; block line-break boundary is tricky |
| B3.4 | Medium | Composition of B3.0 + B3.3; `trimTrailingWS` interaction |
| B3.5 | **High** | Token provenance infrastructure; flow context threading |

**Total estimated new theorems:** ~25–35
**Total estimated proof lines:** ~700–1000
**Expected build-fix cycles:** ~15–25 (budget 2–3 per non-trivial theorem,
per Phase 1 experience)

#### Execution Order

1. **B3.0** — String property lemmas (unlocks everything)
2. **B3.1** — Refactor `collectPlainScalarLoop` (verify build still passes)
3. **B3.2** — Define `PlainContentInv`
4. **B3.3** — Loop invariant preservation (largest proof effort)
5. **B3.4** — `scanPlainScalar_content_valid` (composition)
6. **B3.5** — Global `scan_plain_scalar_valid` (threading)

#### Open Questions

1. **Block-context line-fold + `#` boundary:** Does the scanner correctly
   handle `#` at the start of a continuation line in a block-context plain
   scalar? If `content = "foo"`, line fold produces `"foo "`, and the next
   line starts with `#` with `spaces = ""`, then `#` enters content giving
   `"foo #"` which violates `noSpaceHash`. Need to verify whether this is
   (a) prevented by the YAML spec (§7.3.3 says `#` preceded by `ns-char`
   only), (b) caught by a termination condition we're not tracking, or
   (c) a scanner bug that needs fixing before the proof.

2. **`firstChar` tracking through line folds:** Can a plain scalar's first
   character come from a continuation line (i.e., empty first line then
   content on continuation)? The `canStartPlainScalarBool` check happens
   before `collectPlainScalarLoop` in `scanPlainScalar`, so the first
   character is always checked. But `validPlainFirst` operates on the
   *final* content string. If `trimTrailingWS` changes the content's first
   character (unlikely — it's a suffix operation), we need a lemma.

3. **`PlainContentInv` exact shape:** The invariant sketch above captures
   the main properties, but the exact boundary conditions (last character
   of content before spaces flush, interaction between empty content and
   `validPlainFirst`) will be refined during implementation. Expect 1–2
   revisions as proof obligations reveal additional constraints.

### Phase C: Discharge `h_grammable` (CRITICAL PATH)

With Phases B1–B3 established:

**C1.** Prove `compose_scannable_to_grammable` — alias resolution +
anchor stripping preserves character predicates and eliminates aliases.

**C2.** Prove `parseStream_output_scannable` — the parser propagates
scanner token properties into the `YamlValue` tree.

**C3.** Combine: `parseStream_output_grammable` = C2 + C1.

```lean
theorem parseStream_output_grammable (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h : TokenParser.parseStream tokens = .ok docs) :
    ∀ doc ∈ docs.toList, Grammable (doc.compose.value) false
```

This discharges the `h_grammable` hypothesis in `ParserCorrectness.lean`.

### Phase D: Bridge `Grammar.ValidYaml` to Parser Output (CAPSTONE)

With `h_grammable` discharged, the existing `parseStream_respects_grammar`
gives `∃ ValidNode` witnesses. Combine with `NodeToValue` (already proven
via `Soundness.lean`) to construct `Grammar.ValidYaml`:

```lean
theorem parse_produces_valid_yaml (input : String)
    (docs : Array YamlDocument)
    (h : TokenParser.parseYaml input = .ok docs) :
    ∀ i : Fin docs.size,
      ∃ vy : Grammar.ValidYaml,
        vy.input = input ∧
        stripAnnotations vy.value = stripAnnotations docs[i].compose.value
```

### Phase E: ValidTokenStream Contract (SUPPORTING)

Prove `scan_produces_valid_token_stream` so the scanner/parser boundary
has a typed contract. Architecturally important but not blocking the
critical path.

### Phase F: Dead Code & Low-Priority Gaps

1. **ValidStream / ValidDocument** — decide keep-or-remove
2. **isContentChar** — verify block scalar header proofs reference it
3. **isNamedEscapeChar** — characterization theorems
4. **validHeaderLength** — bounded extraction theorems
5. **IndentedAtLeast** — scanner indent correctness

### Phase G: Comment Preservation (ROUND-TRIP)

Currently the scanner discards comments (`skipToContentComment` consumes
`#`-to-EOL without emitting tokens). The infrastructure exists but is
incomplete:

| Component | Status |
|-----------|--------|
| `Comment` struct (text + position) | ✅ Defined in Types.lean |
| `CommentPosition` (before/inline/after) | ✅ Defined in Types.lean |
| `YamlToken.comment` variant | ✅ Defined in Token.lean |
| Scanner emits `.comment` tokens | ❌ Not implemented |
| `YamlValue` carries comments | ❌ No comment fields |
| `YamlDocument` carries comments | ❌ No comment fields |
| Parser preserves comments | ❌ Not implemented |

**Implementation plan:**

**G1. Scanner: emit `.comment` tokens.** Modify `skipToContentComment`
(Scanner.lean L458–464) to emit `YamlToken.comment text` before
consuming the comment. The scanner already identifies comment text
spans — it just needs to emit instead of discard.

**G2. AST: add comment fields.** Two options:

*Option G2a — Comments on nodes:*
```lean
structure Scalar where
  ...
  comments : Array Comment := #[]

inductive YamlValue where
  | scalar (s : Scalar)
  | sequence ... (comments : Array Comment := #[])
  | mapping ... (comments : Array Comment := #[])
  | alias (name : String) (comments : Array Comment := #[])
```

*Option G2b — Comments as side-channel:*
```lean
structure YamlDocument where
  ...
  comments : Array (YamlPos × Comment) := #[]
```

Option G2b is cleaner for proofs — comments don't pollute the value tree.
Proofs about structural equivalence work on the value tree directly;
comment preservation is a separate side-property.

**G3. Parser: collect `.comment` tokens into side-channel.**

**G4. Normalization:**

```lean
/-- Strip all comments from a document (side-channel variant). -/
def YamlDocument.stripComments (doc : YamlDocument) : YamlDocument :=
  { doc with comments := #[] }
```

**G5. Specification predicates operate modulo comments:**

All grammar validity predicates (`Scannable`, `Grammable`, `ValidNode`,
`ValidYaml`) are defined on `YamlValue` which does not contain comments
(Option G2b). Therefore they are **automatically** comment-agnostic —
no changes needed to the predicates themselves.

**G6. Round-trip theorem:**

```lean
/-- Comments are preserved through parse → emit → parse. -/
theorem comment_round_trip (input : String)
    (doc : YamlDocument)
    (h : parseYaml input = .ok #[doc]) :
    ∀ c ∈ doc.comments,
      ∃ c' ∈ (parseYaml (emit doc)).get!.comments,
        c.2.text = c'.2.text ∧ c.2.position = c'.2.position
```

This theorem states that comment text and relative position are
preserved through a round-trip. The exact byte position may shift
(due to whitespace normalization), but the logical position
(before/inline/after which node) and text content are stable.

**G7. Structural equivalence modulo comments:**

```lean
/-- Structural parse results are unchanged by comment presence.
    Parsing with or without comments yields the same YamlValue tree. -/
theorem parse_value_independent_of_comments (input : String)
    (docs : Array YamlDocument)
    (h : parseYaml input = .ok docs) :
    ∀ i : Fin docs.size,
      docs[i].stripComments.compose.value = docs[i].compose.value
```

This is trivially true when comments are in a side-channel (G2b)
since `stripComments` doesn't touch `value`. But it's worth stating
explicitly as it formalizes YAML 1.2.2 §6.6: comments have no
effect on the serialization tree.

### Phase H: JSON-is-YAML-subset (FUTURE)

Every valid JSON document is valid YAML 1.2. The scanner handles JSON
uniformly — flow collections, double-quoted strings, no block scalars.
`CharPredicates.lean` predicates apply identically to JSON input.

```lean
/-- Every valid JSON document parses as valid YAML. -/
theorem json_is_valid_yaml (input : String) (h : isValidJSON input) :
    ∃ docs, parseYaml input = .ok docs
```

The Core Schema (YAML 1.2.2 §10.3) is already implemented in
`Schema.lean`, subsuming the JSON Schema (§10.2). Schema resolution
proofs exist in `SchemaResolution.lean` and `SchemaDump.lean`. This
phase is a theorem on top of the existing architecture, not a
structural change.

---

## Dependency Graph

```
Phase A (Decidable instances)  ✅ COMPLETE
    │
    ▼
Phase B0 (CharPredicates.lean — shared Bool + Prop + iff)
    │
    ├──▸ Phase B1 (Scannable predicate)
    │        │
    │        ├──▸ Phase B2 (Grammable update — Option C, context-aware)
    │        │
    │        └──▸ Phase B3 (Scanner predicate enforcement)
    │                 │
    │                 ▼
    │            Phase C (Discharge h_grammable)
    │                 │
    │                 ├──▸ C1 (compose_scannable_to_grammable)
    │                 ├──▸ C2 (parseStream_output_scannable)
    │                 └──▸ C3 (parseStream_output_grammable = C2 + C1)
    │                          │
    │                          ▼
    │                     Phase D (Grammar.ValidYaml bridge — CAPSTONE)
    │
    ├──▸ Phase E (ValidTokenStream contract — supporting)
    │
    ├──▸ Phase F (dead code & low-priority gaps)
    │
    └──▸ Phase G (comment preservation — round-trip)
              │
              ├──▸ G1 (scanner emits comment tokens)
              ├──▸ G2 (AST side-channel for comments)
              ├──▸ G3 (parser collects comments)
              ├──▸ G4–G5 (stripComments + modulo-comments)
              ├──▸ G6 (comment round-trip theorem)
              └──▸ G7 (structural independence theorem)

Phase H (JSON-is-YAML-subset — future, no structural changes)
```

## Summary Table

| Definition | YAML Spec | Severity | Has Decidable | Has Theorems | Phase |
|---|---|---|---|---|---|
| `canStartPlainScalarProp/Bool` | §7.3.3 [123] | **BLOCKING** | Pending B0 | Pending (`_iff`) | B0 |
| `validPlainFirstProp/Bool` | §7.3.3 [123] | CRITICAL | Pending B0 | Pending (`_iff`) | B0 |
| `noColonSpaceProp/Bool` | §7.3.3 [127] | CRITICAL | ✅ (Phase A → B0) | Pending (`_iff`) | B0 |
| `noSpaceHashProp/Bool` | §7.3.3 [127] | CRITICAL | ✅ (Phase A → B0) | Pending (`_iff`) | B0 |
| `noFlowIndicatorsProp/Bool` | §7.3.3 [126] | CRITICAL | ✅ (Phase A → B0) | Pending (`_iff`) | B0 |
| `Scannable` | Scanner contract | CRITICAL | n/a | Pending | B1 |
| `Grammable` (context-aware) | Parser contract | CRITICAL | n/a | Pending update | B2 |
| `ScalarScannable` | §7.3.3 | CRITICAL | n/a | Pending | B1 |
| `ValidNode` (updated) | §3.2.1 | CRITICAL | n/a | Pending update | B2 |
| `ValidYaml` (Grammar) | §9 / top | CRITICAL | n/a | construction only | D |
| `IndentedAtLeast` | §6.1 [65] | HIGH | ✅ | `indented_weaken` only | F |
| `ValidTokenStream` | §3.1 | HIGH | n/a | ❌ | E |
| `ValidStream` | §9 [205] | LOW | n/a | ❌ dead code | F |
| Comment preservation | §6.6 | MEDIUM | n/a | ❌ | G |
| JSON-is-YAML | §1.3 | LOW | n/a | ❌ | H |

---

## Grammar.lean Salvageability Assessment

**Verdict: SALVAGEABLE with architectural refactoring.**

Grammar.lean's core architecture — `ValidNode` as a witness type,
`NodeToValue` as an extraction function, `ValidYaml` as the top-level
property — is sound. The `stripAnnotations`-modulo approach for tags and
anchors is architecturally correct (models the representation graph per
YAML 1.2.2 §3.2.1). The existing 33 proof files and 869 tests depend on
this structure.

**Required changes:**

1. **`CharPredicates.lean` extraction** — Move all character predicates
   (Bool + Prop + iff + Decidable) to a shared module. This prevents
   specification drift permanently. (Phase B0)

2. **`canStartPlainScalarProp`** — Fix the unconditional exclusion of
   `-`, `?`, `:` by adding `next : Option Char` and `inFlow : Bool`
   parameters, matching the Scanner's semantics and YAML 1.2.2 [123].
   (Part of Phase B0)

3. **`Scannable` predicate** — New pre-compose specification layer
   that allows aliases and threads flow context. (Phase B1)

4. **`Grammable` update** — Add `inFlow : Bool` parameter (Option C),
   threading context through the tree via `CollectionStyle`. (Phase B2)

5. **Comment side-channel** — Add `comments` field to `YamlDocument`
   (not `YamlValue`) so proofs are automatically comment-agnostic.
   (Phase G)

**What stays unchanged:**
- `ValidNode` constructors (except `validPlainFirstProp` parameter update)
- `NodeToValue` inductive
- `ValidYaml` structure
- All `stripAnnotations`-modulo proof architecture
- `AnchorMap` and its algebraic laws


