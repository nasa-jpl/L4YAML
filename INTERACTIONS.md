# INTERACTIONS.md — Detecting Proof-Breaking Code Patterns via Static Analysis

## Motivation

During the proof of `parseSinglePairMapping_wb` (see BRIDGING.md,
`parseSinglePairMapping_wb` Reflections, 2026-03-15), we identified two
code patterns that cause disproportionate proof difficulty:

1. **Struct `with`-updates before lemmatized method calls.** When a function
   does `{ ps with currentPath := ... }.tryConsume .value`, existing lemmas
   about `ps.tryConsume` don't unify — Lean 4's elaborator cannot see that
   irrelevant field updates don't affect the relevant projections.

2. **Flow-style collection constructors inside non-flow theorem signatures.**
   Functions returning `.mapping .flow` or `.sequence .flow` require
   `Scannable child true` for all children (because `inFlow || .flow == .flow`
   evaluates to `true`), but the standard `_wb` theorem signature only
   guarantees `Scannable _ true` conditionally on `flowNesting > 0`.

Both patterns are invisible to testing and code review — the functions work
correctly. The problems only manifest during proof construction. A static
analysis tool could detect these patterns **before** proof work begins,
saving significant effort.

## Proposed Tool: `#check_wb_interactions`

### Architecture

A Lean 4 metaprogramming command `#check_wb_interactions` that:
1. Collects all function definitions in a specified mutual block
2. For each function, analyzes the elaborated `Expr` to detect the two
   interaction patterns
3. Reports warnings with suggested mitigations

### Detection Algorithm

#### Pattern 1: Struct `with`-updates before method calls

**What to detect:** An expression of the form `f ({ r with field := v })` where:
- `r` is a local variable (fvar)
- `f` is a function for which a lemma exists that takes `r` directly
  (e.g., `tryConsume_tokens (ps : ParseState) ...`)
- The `field` being updated is not used by `f`

**Implementation sketch:**

```lean
/-- Check whether a struct-with-update feeds into a method call
    whose proof lemmas were stated for the original variable. -/
def checkStructWithBeforeMethod (e : Expr) : MetaM (Array Warning) := do
  let warnings := #[]
  -- Walk the expression tree
  e.forEach fun sub => do
    -- Look for applications where an argument is a struct-with-update
    if let .app f arg := sub then
      if isStructWith arg then
        let (baseVar, updatedFields) := decomposeStructWith arg
        let fnName := f.getAppFn.constName?
        -- Check if there exist lemmas about fnName applied to baseVar's type
        -- whose conclusions mention projections NOT in updatedFields
        if let some lemmas ← findLemmasFor fnName then
          for lemma in lemmas do
            let relevantFields := extractRelevantFields lemma
            if relevantFields.all (· ∉ updatedFields) then
              warnings := warnings.push {
                span := sub.getPos?
                msg := s!"Struct-with-update on '{updatedFields}' before " ++
                       s!"'{fnName}' — lemma '{lemma.name}' expects the " ++
                       s!"original variable. May need a '_with_{field}' variant."
              }
  return warnings
```

**Key sub-problems:**

1. **Recognizing struct-with-updates in elaborated `Expr`.** After
   elaboration, `{ ps with currentPath := p }` becomes a sequence of
   struct constructor applications:
   ```
   ParseState.mk ps.tokens ps.pos ps.anchors ps.tagHandles
                  ps.trackPositions p ps.nodePositions
   ```
   Detection: an application of a struct constructor where all but one
   argument is a projection of the same fvar.

2. **Finding relevant lemmas.** Use `Lean.Meta.getEqnsFor?` or search the
   environment for theorems whose type mentions the same function name.
   Alternatively, maintain a registry of "proof-relevant methods" —
   functions like `tryConsume`, `advance`, `peek?` that have associated
   property lemmas.

3. **Determining field relevance.** For a lemma about `tryConsume_tokens`,
   inspect which struct projections appear in the lemma's type (`.tokens`,
   `.pos`, `.peek?`). If the `with`-update modifies a field NOT among
   these, the lemma is applicable in principle but won't unify.

#### Pattern 2: Flow collection return type vs. theorem signature

**What to detect:** A function that:
- Returns a value constructed with `.mapping .flow` or `.sequence .flow`
- Has (or will have) a `_wb` theorem with `Scannable result.1 false` in
  the conclusion
- Contains `parseNode` calls whose `Scannable _ true` output is conditional

**Implementation sketch:**

```lean
/-- Check whether a function returns a flow-style collection, which
    requires Scannable _ true for all children regardless of context. -/
def checkFlowCollectionReturn (decl : ConstantInfo) : MetaM (Array Warning) := do
  let body ← getDefBody decl
  let warnings := #[]
  -- Find all .ok return expressions
  for retExpr in findReturnExprs body do
    if isFlowCollection retExpr then
      -- Check if any child of the collection comes from parseNode
      let children := extractCollectionChildren retExpr
      for child in children do
        if comesFromParseNode child then
          warnings := warnings.push {
            msg := s!"'{decl.name}' returns .mapping/.sequence .flow with " ++
                   s!"parseNode-derived children. The _wb theorem needs " ++
                   s!"'flowNesting > 0' as a precondition (not conditional)."
          }
  return warnings
```

**Key sub-problems:**

1. **Tracing data flow from `parseNode` to collection children.** After
   elaboration, the connection between a `← parseNode ps fuel` bind and
   the final `.mapping .flow #[(key, val)]` return is obscured by monadic
   desugaring. Need to follow let-bindings and `Except.bind` continuations.

2. **Distinguishing `emptyNode` from `parseNode` children.** `emptyNode`
   children don't need the flow hypothesis (they satisfy `Scannable _ true`
   unconditionally). Only `parseNode`-derived children create the problem.
   Detection: check whether the child variable was bound by a
   `parseNode` call in the monadic chain.

3. **Cross-referencing with theorem signatures.** If no `_wb` theorem
   exists yet, report the warning preemptively. If one exists, check
   whether it already has `flowNesting > 0` as a hypothesis.

### Integration Points

#### Option A: Command-line linter (recommended for initial version)

```lean
/-- Run interaction checks on all functions in the mutual block
    containing the given declaration. -/
syntax "#check_wb_interactions" ident : command

-- Usage:
#check_wb_interactions parseSinglePairMapping
-- Output:
-- ⚠ parseSinglePairMapping: struct-with-update on 'currentPath' before
--   'ParseState.tryConsume' at L707. Lemma 'tryConsume_tokens' expects
--   the original variable. Consider a '_with_path' variant.
-- ⚠ parseSinglePairMapping: returns .mapping .flow with parseNode-derived
--   children. The _wb theorem needs 'flowNesting > 0' as a precondition.
```

#### Option B: Elaboration hook (future)

Register as an `afterElaboration` hook that runs automatically on every
definition in files importing `ParserGrammable`. This would catch new
instances immediately when G5c-style modifications are made.

#### Option C: CI integration (future)

Run as a `lake script check-interactions` step that processes the mutual
block and fails CI if new unmitigated interactions are detected.

#### Pattern 3: WHNF expansion of compound expressions inside `split`

**What to detect:** A function whose monadic chain contains a compound
expression (method call with computed arguments, struct-with-update
followed by method call) whose internal match structure has more branches
than the outer dispatch that the proof intends to split on.

**Why it matters:** When `split at h_ok` is used to peel through monadic
branches, WHNF expands sub-expressions to find the outermost match.
If a sub-expression like `tryConsume` contains `match peek? with ... | some t =>
if t == tok then (true, advance) else (false, ps)`, this **inner** 3-way
match is found before the **outer** `if consumed then ...` dispatch.
The proof silently splits on the wrong match, producing goals where the
`consumed` flag is still unevaluated as a compound expression.

**Mitigation (proof-side):** Use `generalize` to make the compound
sub-expression opaque before splitting:
```lean
generalize hg : ParseState.tryConsume _ _ = tc at h_ok
split at h_ok  -- now finds `if tc.fst then ...` cleanly
```

**Mitigation (code-side):** Extract the compound expression into a `let`
binding so that after `unfold` and `simp only [bind, Except.bind]`, the
name is preserved and `split` finds the outer dispatch first:
```lean
let tc := { ps with currentPath := path }.tryConsume .value
let (consumed, ps) := tc
if consumed then ...
```

**Implementation sketch:**

```lean
/-- Check whether a function has compound expressions feeding into
    outer dispatch matches, creating WHNF-expansion hazards. -/
def checkWHNFExpansionHazard (e : Expr) : MetaM (Array Warning) := do
  let warnings := #[]
  -- Find `if` / `match` dispatches whose scrutinee is a projection
  -- of a method call (not a simple fvar)
  e.forEach fun sub => do
    if let .app (.app (.const ``ite _) cond) _ := sub then
      -- Check if cond involves a projection of a compound expression
      if isProjectionOfCompound cond then
        let innerMatches := countMatchBranches (getCompoundBase cond)
        let outerMatches := 2  -- if/then/else
        if innerMatches > outerMatches then
          warnings := warnings.push {
            msg := s!"WHNF hazard: '{getCompoundBase cond}' has " ++
                   s!"{innerMatches} internal branches but feeds into " ++
                   s!"a {outerMatches}-branch dispatch. " ++
                   s!"`split` may target the inner match. " ++
                   s!"Consider extracting to a let binding."
          }
  return warnings
```

### Scope and Limitations

**In scope:**
- Pattern 1 (struct-with-update → method call unification failure)
- Pattern 2 (flow collection return → Scannable polarity mismatch)
- Pattern 3 (WHNF expansion of compound sub-expressions inside `split`)
- All three are specific to the parser's `ParseState` + `Scannable`
  architecture, but the detection algorithms generalize

**Out of scope (initially):**
- Detecting `try`-based goal corruption (Lesson 6 in BRIDGING.md) —
  this is a tactic-composition problem requiring analysis of tactic
  scripts, not elaborated `Expr` trees
- General "proof difficulty prediction" — the tool only detects known
  interaction patterns, not novel ones

### Implementation Plan

| Phase | Deliverable | Effort |
|-------|-------------|--------|
| I1 | `isStructWith` / `decomposeStructWith` helpers | Small |
| I2 | Pattern 1 detector (struct-with → method call) | Medium |
| I3 | Pattern 2 detector (flow collection return check) | Medium |
| I4 | Pattern 3 detector (WHNF expansion hazard) | Medium |
| I5 | `#check_wb_interactions` command wiring | Small |
| I6 | Run on all 7 G5c-modified functions, validate results | Small |
| I7 | Document false-positive patterns and suppression mechanism | Small |

### Expected Results on Current Codebase

Running the analysis on the 7 G5c-modified functions (BRIDGING.md §G5c):

| Function | Pattern 1 (struct-with) | Pattern 2 (flow return) | Pattern 3 (WHNF hazard) |
|----------|------------------------|------------------------|-------------------------|
| `parseBlockSequenceLoop` | ✓ (currentPath before parseNode — but parseNode takes ps directly, so lemmas still apply) | ✗ (returns array, not flow collection) | ✗ (no compound scrutinee) |
| `parseImplicitBlockSequenceLoop` | ✓ (same as above) | ✗ | ✗ |
| `parseBlockMappingLoop` | ✓ (currentPath before BEV/parseNode) | ✗ (block mapping) | ✗ |
| `parseFlowSequenceLoop` | ✓ (currentPath before parseNode + parseSinglePairMapping) | ✗ (returns array) | ✗ |
| `parseFlowMappingLoop` | ✓ (currentPath before parseNode + tryConsume) | ✗ (returns array) | **✓** (tryConsume on struct-with feeds into `if consumed`) |
| `parseSinglePairMapping` | **✓ CONFIRMED** (currentPath before tryConsume) | **✓ CONFIRMED** (.mapping .flow return) | **✓ CONFIRMED** (tryConsume internal match found before consumed dispatch) |
| `parseDocument` | ✓ (currentPath before parseNode) | ✗ | ✗ |

Note: For most functions, Pattern 1 manifests as `{ ps with currentPath := ... }`
before `parseNode`, but `parseNode` takes `ps : ParseState` as a regular
argument (not a method call that needs lemma matching), so the interaction is
weaker — `parseNodeWB_apply` can still unify because its `h_tok` argument
is stated as `ps.tokens = tokens` and `{ ps with currentPath := ... }.tokens`
**does** reduce definitionally in this position (it appears as an explicit
hypothesis, not inside a lemma's implicit argument matching). The interaction
is only severe when the struct-with-update feeds into a **method** like
`tryConsume` whose lemmas bind the entire `ParseState` as a single argument.

### Generalization Beyond This Project

The three patterns generalize to any Lean 4 codebase where:

1. **Records with proof-irrelevant fields** are updated before method calls
   whose lemmas were stated for the original record. This is common in
   stateful parsers, compilers, and interpreters where a "context" or
   "environment" record has both proof-relevant fields (e.g., input, position)
   and proof-irrelevant fields (e.g., debug flags, path tracking, logging).

2. **Inductive predicates with non-trivial field dependencies** (like
   `Scannable`'s `inFlow || style == .flow`) create situations where
   constructing a witness at parameter A requires sub-witnesses at a
   different parameter B that is computed from A and additional data. When
   theorem signatures use A as conditional and B as unconditional (or vice
   versa), the signature doesn't match the constructor's actual requirements.

3. **Compound expressions used as scrutinees of outer dispatches** cause
   `split` (via WHNF) to target inner matches instead of the intended
   outer one. This applies to any codebase where a method call's result
   is immediately destructured — e.g., `let (flag, state) := record.method()
   ; if flag then ...`. The method's internal match structure becomes visible
   to WHNF and intercepts `split`. This is especially prevalent in monadic
   code where `do`-notation desugars to nested binds that `unfold`/`simp`
   must peel through, exposing intermediate computations.

A general version of this tool could be valuable for the broader Lean 4
verified-systems community.
