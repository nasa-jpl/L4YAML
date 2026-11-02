---
name: l4yaml-adversarial-before-proof
description: Refute-before-prove for L4YAML — check a proposed or sorry'd lemma statement against the boundary cases that have historically falsified statements (fuel 0/1/2, empty/singleton, nesting 0–3, token kinds, positions, parser states) in Tests/AdversarialInstantiation.lean before spending proof effort. Use whenever stating a new lemma, picking up a sorry'd statement, or when a proof has resisted for more than an hour.
---

# Adversarial instantiation before proof (Rule 2)

Statement first, refuter second, proof third.  Method and history:
`lake run docs-nav -- section 'adversarial inst'`.

## 1. Trace the capstone (Rule 1)

Name the `@[capstone]` in `Blueprint/04-capstones.md` that needs this lemma
and the chain to it.  No chain → no lemma (or add the capstone row first).

## 2. Red-flag the statement shape

Historically false statements had one of these:

| Shape | Why it fails | Fix |
|---|---|---|
| `∀ pos/state/index …` with no relation to the input | holds at the initial state only | quantify over reachable states (`sc = scan … ` / `h_dispatch`) |
| Precondition names a size (`toks.length ≥ n`) | structure, not size, is what the proof needs | name the token kind / nesting / frame |
| Postcondition strengthened, hypothesis not | the old refuter still applies | add the premise the producer actually has |
| Fuel bound as a function of length | depends on nesting/structure | bound by the structural measure |
| A `Prop` conclusion the caller never destructures | `Or.inr trivial` proves it — not an obligation (§8) | narrow the conclusion to the informative side |
| Statement about `String` | `String.Slice`/`drop`/`take` fight the proof | state over `List Char`, wrap once |

## 3. Instantiate

In `Tests/AdversarialInstantiation.lean`, under the capstone's priority
section, write decidable checks over the grid:

- fuel 0, 1, 2 (and the first value where the claim should start holding);
- `[]`, `[x]`, `[x, y]`; nesting depth 0–3; mixed block/flow;
- every token kind the statement quantifies over; first/middle/last position;
- parser states: initial, mid-flow, post-bracket, after `---`, after a dedent.

```lean
#guard (check inputs).all fun i => theoremInstance i   -- fast, decidable
-- diagnostics while shaping the grid:
#eval (check inputs).filter fun i => ¬ theoremInstance i
```

Use `#guard` for the permanent check, `#eval` only while exploring,
`native_decide` when the decidable check is too big for `decide`.  Report
the outcome as one of **failed-hypothesis** (vacuous — tighten the grid),
**theorem-holds**, **theorem-refuted**.  A refutation that stays in the file
is a build failure, which is the point.

## 4. Only then prove

`lemma`, not `theorem`.  If the proof resists: re-check the grid (did the
refuter cover the case the proof is stuck on?), then restate over the
weaker-but-true form and record the refutation in the item.  Never ship the
refuted statement with a `sorry`.
