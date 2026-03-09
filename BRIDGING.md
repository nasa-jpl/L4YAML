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

Prove that the scanner produces tokens satisfying `ScalarScannable`:

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
