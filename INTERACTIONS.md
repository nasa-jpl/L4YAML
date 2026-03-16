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

#### Pattern 4: Complexity explosion in monolithic loop bodies

**What to detect:** A recursive (or tail-recursive) function whose body
contains multiple independent dispatch branches that each perform
structurally similar sub-computations (key dispatch, tryConsume, value
dispatch), leading to a combinatorial explosion in proof cases.

**Why it matters:** When a loop body has $N$ entry patterns, each with $M$
internal dispatch branches, the proof must handle $N \times M$ cases, many
of which are nearly identical. The complexity scales multiplicatively rather
than additively. This is invisible to code review — the function is clean,
well-structured, and correct — but the proof becomes unmanageable.

**Canonical example:** `parseFlowMappingLoop` (TokenParser.lean L631–690)
has two entry patterns:
- **Explicit key** (`some .key`): advance, key dispatch (3 emptyNode cases +
  parseNode catch-all), tryConsume `.value`, value dispatch (3 emptyNode cases
  + parseNode catch-all), recurse
- **Implicit key** (catch-all `_`): parseNode, tryConsume `.value`, value
  dispatch (same 4 × 2 structure), recurse

The tryConsume + value dispatch tail is **identical** between both branches.
Each proof case requires ~40 lines (key/value WB extraction, flowNesting
chain, tokens chain, Scannable pair construction). Total: ~320 lines of
largely duplicated proof for 8 cases (2 entry × 2 consumed × 2 value).

Compare `parseFlowSequenceLoop` (L575–612): only 3 content dispatch branches
(key → `parseSinglePairMapping`, `flowSequenceEnd`, parseNode catch-all), each
with a single value. The proof (`parseFlowSequenceLoop_wb`) is ~110 lines.

**Mitigation (code-side):** Factor out the shared sub-computation as a named
function, then prove a single well-behavedness lemma for it:

```lean
/-- Extract a single mapping entry (key + optional value).
    Shared logic for explicit-key and implicit-key branches. -/
def parseFlowMappingEntry (ps : ParseState) (fuel : Nat) (pairIndex : Nat)
    (key : YamlValue) : Except ScanError ((YamlValue × YamlValue) × ParseState)
```

Then the loop proof delegates to `parseFlowMappingEntry_wb` exactly as
`parseFlowSequenceLoop_wb` delegates to `parseSinglePairMapping_wb`.

**Relationship to Wadler's "theorems for free":** Before refactoring, we can
derive **behavioral specifications** from the current `parseFlowMappingLoop`
type signature and implementation that must be preserved:

1. **Monotonicity**: `result.1.size ≥ pairs.size` (the loop only appends)
2. **Token preservation**: `result.2.tokens = ps.tokens` (no token mutation)
3. **flowNesting preservation**: `flowNesting tokens result.2.pos =
   flowNesting tokens ps.pos` (in flow context)
4. **Item well-behavedness**: All items in `result.1` satisfy `Scannable` at
   the appropriate polarity

These "free theorems" serve as regression tests for the refactoring: if the
factored version satisfies the same specifications, behavior is preserved.
The Wadler approach suggests deriving what we can from the type (parametricity)
— here the key insight is that `parseFlowMappingLoop` is parametric in the
*content* of key/value parsing (it just threads state), so any factoring that
preserves the state-threading discipline preserves behavior.

**Implementation sketch:**

```lean
/-- Check whether a recursive function has multiple branches with
    structurally similar sub-computations. -/
def checkComplexityExplosion (decl : ConstantInfo) : MetaM (Array Warning) := do
  let body ← getDefBody decl
  let branches := findRecursiveCallBranches body
  -- Group branches by structural similarity (same sequence of bind operations
  -- with different initial dispatch but shared tail)
  let groups := groupBySimilarTail branches
  for group in groups do
    if group.size > 1 then
      let sharedTail := computeSharedTail group
      warnings := warnings.push {
        msg := s!"'{decl.name}' has {group.size} branches sharing a common " ++
               s!"tail of {sharedTail.bindCount} bind operations. " ++
               s!"Consider extracting to a subfunction to reduce proof cases " ++
               s!"from {totalCases group} to {reducedCases group}."
      }
  return warnings
```

#### Pattern 5: Semantic impasse from specification-level invariant gaps

**What to detect:** A proof obligation that reduces (after available rewrites)
to an arithmetic impossibility — e.g., `x + 1 = x`, `f x + c = f x` for
`c > 0` — indicating that the theorem's claim is **unprovable** in a
particular branch, not merely difficult. This signals a missing invariant at
a higher level (e.g., scanner, grammar) rather than a proof technique gap.

**Why it matters:** Without detection, these cases consume unbounded proof
effort. The prover tries increasingly sophisticated techniques on a goal
that is literally false in the current context. The root cause is that
the theorem was stated under implicit assumptions (e.g., "the closing bracket
is always consumed") that are not formalized as hypotheses.

**Canonical example:** `parseFlowSequence_wb`, else-branch (no flowSequenceEnd
consumed). After rewriting:
```
h_adv_fn_eq : flowNesting tokens ps.advance.pos = flowNesting tokens ps.pos + 1
h_loop_fn : flowNesting tokens ps_loop.pos = flowNesting tokens ps.advance.pos
⊢ flowNesting tokens ps_loop.pos = flowNesting tokens ps.pos
```
Substituting: `flowNesting tokens ps.pos + 1 = flowNesting tokens ps.pos`. This
is `x + 1 = x` — false for all `x : Nat`.

**Root cause analysis:** The theorem claims `flowNesting` is preserved through
`parseFlowSequence`. This is true when `flowSequenceEnd` is consumed (the
`+1` from `flowSequenceStart` is cancelled by `-1` from `flowSequenceEnd`).
But the implementation has an `else` branch where `flowSequenceEnd` is NOT
consumed (fuel exhaustion, or the loop exits without seeing the end token).
In this branch, the net `flowNesting` change is `+1`, not `0`.

**Resolution options:**

1. **Scanner invariant (Option 1):** Add a `FlowBracketsMatched` property to
   `FlowAwarePSV` proving that every `flowSequenceStart`/`flowMappingStart`
   has a matching `flowSequenceEnd`/`flowMappingEnd` at a later position.
   Combined with a fuel-sufficiency argument, this makes the else-branch
   unreachable (`False.elim`).

2. **Fuel-sufficiency (Option 2):** Prove that when `parseFlowSequence`
   returns `.ok`, the loop **always** consumed `flowSequenceEnd` (i.e., the
   else-branch yields `.error` or is never reached). This follows from the
   scanner guaranteeing matched brackets: with well-formed tokens, the loop
   sees `flowSequenceEnd` and exits via the `some .flowSequenceEnd` branch
   before fuel runs out.

3. **Combined approach (Options 1 + 2):** Add `FlowBracketsMatched` to
   the scanner invariant chain (Option 1), then prove a lemma that
   `parseFlowSequence` on matched-bracket tokens always takes the
   `some .flowSequenceEnd` branch (Option 2). This is the most robust
   approach: Option 1 provides the semantic foundation, Option 2 provides
   the syntactic consequence.

**Detection mechanism — automated impasse detection:**

```lean
/-- After tactic execution leaves a numeric goal, check if it's
    a trivial impossibility. -/
def checkArithmeticImpasse (goal : MVarId) : MetaM (Option Warning) := do
  let target ← goal.getType
  -- Normalize the target
  let target ← Meta.reduce target
  -- Check for patterns like `n + k = n` or `n = n + k` where k > 0
  if let some (lhs, rhs) := isEqNat target then
    -- Try to show lhs - rhs or rhs - lhs is a positive constant
    let diff ← Meta.reduce (← mkAppM ``Nat.sub #[lhs, rhs])
    if isPositiveLiteral diff then
      return some { msg := s!"Arithmetic impasse: goal reduces to " ++
        s!"'{← ppExpr target}' which requires {← ppExpr diff} = 0. " ++
        s!"This suggests a missing invariant that would make this " ++
        s!"branch unreachable." }
  return none
```

**Generalized detection — "rewrite saturation + impossibility check":**

A more general approach: after applying all available `rw` lemmas from
hypotheses to the goal, run `omega` or `norm_num`. If these **succeed
in proving `False`** from the goal + hypotheses, the branch is unreachable
given a missing invariant. If they succeed in closing the goal, no impasse.
If they fail but the goal has a simple arithmetic structure, flag as a
potential impasse.

### Scope and Limitations

**In scope:**
- Pattern 1 (struct-with-update → method call unification failure)
- Pattern 2 (flow collection return → Scannable polarity mismatch)
- Pattern 3 (WHNF expansion of compound sub-expressions inside `split`)
- Pattern 4 (complexity explosion in monolithic loop bodies)
- Pattern 5 (semantic impasse from specification-level invariant gaps)
- All five are specific to the parser's `ParseState` + `Scannable`
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
| I5 | Pattern 4 detector (complexity explosion in loop bodies) | Medium |
| I6 | Pattern 5 detector (arithmetic impasse / invariant gap) | Medium |
| I7 | `#check_wb_interactions` command wiring | Small |
| I8 | Run on all 7 G5c-modified functions, validate results | Small |
| I9 | Document false-positive patterns and suppression mechanism | Small |

### Expected Results on Current Codebase

Running the analysis on the 7 G5c-modified functions (BRIDGING.md §G5c):

| Function | P1 (struct-with) | P2 (flow return) | P3 (WHNF hazard) | P4 (loop explosion) | P5 (impasse) |
|----------|-----------------|-----------------|------------------|--------------------|--------------| 
| `parseBlockSequenceLoop` | ✓ (currentPath before parseNode — but parseNode takes ps directly, so lemmas still apply) | ✗ (returns array, not flow collection) | ✗ (no compound scrutinee) | ✗ (single branch) | ✗ |
| `parseImplicitBlockSequenceLoop` | ✓ (same as above) | ✗ | ✗ | ✗ (single branch) | ✗ |
| `parseBlockMappingLoop` | ✓ (currentPath before BEV/parseNode) | ✗ (block mapping) | ✗ | ✗ (extracted to `handleBlockMapping*Entry`) | ✗ |
| `parseFlowSequenceLoop` | ✓ (currentPath before parseNode + parseSinglePairMapping) | ✗ (returns array) | ✗ | ✗ (3 simple branches) | ✗ |
| `parseFlowMappingLoop` | ✓ (currentPath before parseNode + tryConsume) | ✗ (returns array) | **✓** (tryConsume on struct-with feeds into `if consumed`) | **✓** (2 entry × 4 key × 2 consumed × 4 value = explosion) | ✗ |
| `parseSinglePairMapping` | **✓ CONFIRMED** (currentPath before tryConsume) | **✓ CONFIRMED** (.mapping .flow return) | **✓ CONFIRMED** (tryConsume internal match found before consumed dispatch) | ✗ (single entry) | ✗ |
| `parseDocument` | ✓ (currentPath before parseNode) | ✗ | ✗ | ✗ | ✗ |
| `parseFlowSequence` (wrapper) | ✗ | ✗ | ✗ | ✗ | **✓** (`flowNesting ps.pos + 1 = flowNesting ps.pos` in else branch) |
| `parseFlowMapping` (wrapper) | ✗ | ✗ | ✗ | ✗ | **✓** (same `flowNesting` impasse as `parseFlowSequence`) |

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

The five patterns generalize to any Lean 4 codebase where:

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

4. **Monolithic recursive functions with duplicated sub-computations** in
   multiple branches. This is extremely common in parsers, interpreters, and
   state machines where different input tokens trigger structurally similar
   processing pipelines. The code is clean and correct, but the proof work
   scales multiplicatively. The fix — factoring out shared sub-computations —
   is a standard software engineering refactoring, but it's motivated here
   by proof economics rather than code clarity. This connects to Wadler's
   "theorems for free" insight: the factored function's type signature
   constrains its behavior, making the proof obligation smaller and more
   composable. **Behavioral specifications derived from the original type
   (monotonicity, state preservation, well-behavedness propagation) serve as
   regression tests ensuring the refactoring preserves semantics.**

5. **Proof obligations that reduce to arithmetic impossibilities** after
   applying available rewrites, indicating that a theorem's claim is false
   in a particular branch. This signals a missing invariant at a higher
   abstraction level (scanner, grammar, type system) rather than a proof
   technique gap. The detection generalizes beyond parsers: any system where
   a function maintains a counter-like quantity (nesting depth, reference
   count, resource balance) that is modified by paired operations (open/close,
   acquire/release, push/pop) can exhibit this pattern when the "close"
   operation is not guaranteed to execute. The resolution requires either
   (a) a liveness/matching invariant at the specification level, (b) a
   proof that the unmatched branch is unreachable, or (c) both.

A general version of this tool could be valuable for the broader Lean 4
verified-systems community.

---

## Appendix: The `parseFlowMappingLoop` Case Study

### Decomposition Analysis (2026-03-15)

`parseFlowMappingLoop` is the canonical example of Pattern 4. Its 60-line
body has two major entry branches (explicit key, implicit key) that share
an identical tryConsume + value dispatch tail. The proof complexity comes
from the Cartesian product of cases:

```
parseFlowMappingLoop (60 lines, ~320 proof lines estimated)
├── fuel match (0 → base, k+1 → ...)
├── peek? = flowMappingEnd → early return
├── separator check (pairs.size > 0)
│   ├── flowEntry → advance
│   └── other → early return
├── content dispatch (after separator)
│   ├── some .key (explicit key)
│   │   ├── advance KEY token
│   │   ├── key dispatch
│   │   │   ├── .value | .flowEntry | .flowMappingEnd → emptyNode key
│   │   │   └── _ → parseNode key
│   │   ├── tryConsume .value           ← SHARED TAIL STARTS HERE
│   │   ├── value dispatch (consumed)
│   │   │   ├── .flowEntry | .flowMappingEnd | none → emptyNode val
│   │   │   └── _ → parseNode val
│   │   ├── value dispatch (!consumed) → emptyNode val
│   │   └── recurse with (key, val)
│   └── _ (implicit key)
│       ├── parseNode key
│       ├── tryConsume .value           ← SAME SHARED TAIL
│       ├── value dispatch (consumed)   ← SAME
│       ├── value dispatch (!consumed)  ← SAME
│       └── recurse with (key, val)
```

### Proposed Factoring

Extract the shared tail into `parseFlowMappingValue`:

```lean
/-- Parse the value part of a flow mapping entry.
    After key is parsed, consume optional VALUE token and parse value.
    Returns the value and updated state. -/
def parseFlowMappingValue (ps : ParseState) (fuel : Nat)
    (savedPath : YamlPath) (keyContent : String)
    : Except ScanError (YamlValue × ParseState) := do
  let ps := { ps with currentPath := savedPath.push (.key keyContent) }
  let (consumed, ps) := ps.tryConsume .value
  let (val, ps) ← if consumed then
    match ps.peek? with
    | some .flowEntry | some .flowMappingEnd | none => .ok (emptyNode, ps)
    | _ => parseNode ps fuel
  else .ok (emptyNode, ps)
  .ok (val, { ps with currentPath := savedPath })
```

Then `parseFlowMappingLoop` becomes:

```lean
def parseFlowMappingLoop (ps : ParseState) (fuel : Nat)
    (pairs : Array (YamlValue × YamlValue)) := do
  match fuel with
  | 0 => .ok (pairs, ps)
  | fuel + 1 =>
    match ps.peek? with
    | some .flowMappingEnd => .ok (pairs, ps)
    | _ => do
      let ps ← if pairs.size > 0 then
        match ps.peek? with
        | some .flowEntry => pure ps.advance
        | _ => return (pairs, ps)
      else pure ps
      match ps.peek? with
      | some .flowMappingEnd => .ok (pairs, ps)
      | some .key => do
        let ps := ps.advance
        let (key, ps) ← match ps.peek? with
          | some .value | some .flowEntry | some .flowMappingEnd =>
            .ok (emptyNode, ps)
          | _ => parseNode ps fuel
        let keyContent := match key with | .scalar s => s.content | _ => s!"{pairs.size}"
        let (val, ps) ← parseFlowMappingValue ps fuel ps.currentPath keyContent
        parseFlowMappingLoop ps fuel (pairs.push (key, val))
      | _ => do
        let (key, ps) ← parseNode ps fuel
        let keyContent := match key with | .scalar s => s.content | _ => s!"{pairs.size}"
        let (val, ps) ← parseFlowMappingValue ps fuel ps.currentPath keyContent
        parseFlowMappingLoop ps fuel (pairs.push (key, val))
```

### Wadler-Style "Theorems for Free" as Refactoring Guards

Before performing the refactoring, we derive behavioral specifications from
the CURRENT `parseFlowMappingLoop` that must be preserved. 

#### Step 1: write the theorem properties for the current `parseFlowMappingLoop` implementation. These are properties that follow from the function's type signature and implementation structure, not from domain-specific knowledge. They are "free theorems" in the Wadler sense — they must hold for any function with the same type signature and similar accumulator structure, regardless of the specific parsing logic.

**Status: COMPLETED (2026-03-14).** Four properties identified; (1)–(3)
are pure free theorems, (4) is domain-contingent (see Pattern 5 / flowNesting
impasse).

1. **Token preservation** (from the type `ParseState → ... → Except ... (... × ParseState)`):
   ```lean
   theorem parseFlowMappingLoop_tokens_preserved (ps result) (h_ok : ... = .ok result) :
       result.2.tokens = ps.tokens
   ```

2. **Monotonicity** (from the accumulator pattern `pairs → ... pairs.push ...`):
   ```lean
   theorem parseFlowMappingLoop_pairs_grow (ps pairs result) (h_ok : ... = .ok result) :
       result.1.size ≥ pairs.size
   ```

3. **Prefix preservation** (from the push-only pattern):
   ```lean
   theorem parseFlowMappingLoop_prefix_preserved (ps pairs result) (h_ok : ... = .ok result) :
       ∀ i : Fin pairs.size, result.1[i] = pairs[i]
   ```

4. **flowNesting preservation** (contingent on flow context — the well-behavedness
   property). This becomes the loop invariant for the proof:
   ```lean
   theorem parseFlowMappingLoop_wb (tokens ps pairs result)
       (h_eq : ps.tokens = tokens) (h_flow : flowNesting tokens ps.pos > 0)
       (h_ok : ... = .ok result) :
       flowNesting tokens result.2.pos = flowNesting tokens ps.pos
   ```

The Wadler insight: properties (1)–(3) follow purely from the function's
TYPE and accumulator structure — any function with the same type signature
that only uses `push` on the accumulator must satisfy them. Property (4)
requires domain knowledge (flow nesting semantics) but its STRUCTURE
(state-property preservation through a loop) is a free theorem of the
state-threading pattern.

#### Step 2: Refactor `parseFlowMappingLoop` to extract the shared tryConsume + value dispatch logic into `parseFlowMappingValue`. This should be a purely syntactic transformation that does not change the overall structure of the loop or the way state is threaded.

**Status: COMPLETED (2026-03-14).** `parseFlowMappingValue` extracted as a
separate function in the `mutual` block (TokenParser.lean L630–644).
`parseFlowMappingLoop` (L646–676) refactored to call it. All 323 test
suite jobs pass.

#### Step 3: Prove the same properties (1)–(3) for the new `parseFlowMappingLoop` + `parseFlowMappingValue`. If all three hold, we have strong evidence that the refactoring preserved the core behavior of the loop with respect to token handling and pair accumulation.

**Status: COMPLETED (2026-03-15).** All three free-theorem properties
proved, plus a helper lemma for the extracted function:

| Theorem | Location | Status |
|---------|----------|--------|
| `parseFlowMappingValue_tokens_preserved` | ParserGrammable.lean L2259 | **Proved** |
| `parseFlowMappingLoop_tokens_preserved` | ParserGrammable.lean L2291 | **Proved** |
| `parseFlowMappingLoop_pairs_grow` | ParserGrammable.lean L2364 | **Proved** |
| `parseFlowMappingLoop_prefix_preserved` | ParserGrammable.lean L2398 | **Proved** |

Sorry count reduced from 14 → 11 (net -3: one sorry removed per loop
theorem).

**Proof technique notes:**

- **`_pairs_grow` and `_prefix_preserved`**: Automated "split-and-close"
  approach — 20× `all_goals (try (split at h_ok))` to exhaustively expand
  all monadic branches, then close all goals with `first | ... | ...`
  combining base-case, error, and IH closers. Required
  `set_option maxHeartbeats 800000` / `1600000`.

- **`_tokens_preserved`**: Fundamentally harder because it requires threading
  `ps.tokens = tokens` through intermediate `parseNode` and
  `parseFlowMappingValue` calls. The same split-and-close approach works for
  Phase 1 (errors via `contradiction`/`simp at h_ok`) and Phase 2 (base
  cases via `subst h_ok; exact h_eq`). Phase 3 (recursive cases) uses
  `rename_i` to name auto-generated hypotheses from `split`, then chains:
  1. `parseNodeWB_apply` to get `v_node.snd.tokens = tokens` from `parseNode`
  2. `parseFlowMappingValue_tokens_preserved` to get `v_pFMV.snd.tokens = tokens`
  3. `ih_fuel` with the derived token equality to close the loop

  Key Lean 4 elaboration insight: `all_goals (try (...))` closers for
  parseNode paths used `(by simp only [ParseState.advance_tokens]; exact h_eq)`
  for the token hypothesis, which worked for all goals where `parseNode` was
  called on `ps.advance` (explicit-key branch). One remaining goal called
  `parseNode ps k` directly (implicit-key branch, `¬pairs.size > 0` sub-case),
  requiring `h_eq` without the `simp` — solved by a direct (non-`try`) closer
  after the `all_goals` pass.

After refactoring, we prove the SAME four properties for the new
`parseFlowMappingLoop` + `parseFlowMappingValue`. If all four hold, the
refactoring is semantically correct for proof purposes.

Property (4) — `flowNesting` preservation — remains contingent on resolving
the `flowNesting` impasse (Pattern 5, see below).

### The `flowNesting` Impasse (Pattern 5 Instance)

The `parseFlowSequence_wb` and `parseFlowMapping_wb` wrapper theorems both
have an else-branch where the closing bracket (`flowSequenceEnd` /
`flowMappingEnd`) is not consumed. In this branch:

```
h_adv_fn_eq : flowNesting tokens ps.advance.pos = flowNesting tokens ps.pos + 1
h_loop_fn   : flowNesting tokens ps_loop.pos = flowNesting tokens ps.advance.pos
⊢ flowNesting tokens ps_loop.pos = flowNesting tokens ps.pos
```

Substituting: `flowNesting tokens ps.pos + 1 = flowNesting tokens ps.pos`,
i.e., `x + 1 = x` — literally false.

**Resolution plan (Options 1 + 2 combined):**

**Step 1 (Scanner invariant — Option 1):** Add to `FlowAwarePSV`:
```lean
def FlowBracketsMatched (tokens : Array (Positioned YamlToken)) : Prop :=
  flowNesting tokens tokens.size = 0
```
This says all flow brackets are matched globally. It follows from
`FlowNestingInv` (which says `flowNesting tokens tokens.size = flowLevel`)
combined with the scanner's guarantee that `flowLevel = 0` at the end of
scanning (the scanner errors if flow level is nonzero at stream end).

**Step 2 (Fuel sufficiency — Option 2):** Prove that for well-formed
(matched-bracket) token streams, `parseFlowSequence` with sufficient fuel
ALWAYS reaches the `some .flowSequenceEnd` branch:
```lean
theorem parseFlowSequence_consumes_end (tokens ps result)
    (h_matched : FlowBracketsMatched tokens)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseFlowSequence ps fuel = .ok result) :
    ∃ ps_loop, parseFlowSequenceLoop ps.advance (fuel - 1) #[] = .ok (_, ps_loop) ∧
    ps_loop.peek? = some .flowSequenceEnd
```

**Step 3:** With Step 2 proved, the else-branch of `parseFlowSequence_wb`
has a contradictory hypothesis (`h_peek_not_end` vs the Step 2 conclusion),
and we close it with `absurd`/`contradiction`.
