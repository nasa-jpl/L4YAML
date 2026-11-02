---
name: l4yaml-closure-item
description: Carry one Row 12 (β.5) closure-log item from the previous item's NEXT mandate through predictions, pricing, build, guard re-pins, and the new DOCS.md entry with its own NEXT. Use when asked to "take the next item", do step 12.x.y, or record campaign work in DOCS.md.
---

# One closure-log item, start to finish

The campaign is recorded one `### Item N (YYYY-MM-DD)` at a time in the
`## Row 12 — β.5 closure log` section of `DOCS.md`.  The entry is written as
the work happens, not after; its predictions are the test of the reading.

## 0. Take the mandate

```bash
python3 scripts/docs_nav.py next          # the paragraph you are answering
python3 scripts/docs_nav.py item <N-1>    # read the whole previous item
python3 scripts/docs_nav.py steps         # which 12.x.y row this is
```
Quote the NEXT verbatim under **The mandate.**  Departing from it is allowed
only with the reason written there.

## 1. Read before measuring (§3, §10)

- Read the arms/declarations the mandate names, in the file, in order.  Two
  of item 265's three arm comments contradicted the line below them — found
  only by reading the arm to price it.
- Read the pins that already hold the numbers you need
  (`Tests/Guards/Proofs/*.lean`, `expected… = "…"`).  Then re-run the
  relevant instrument on *this* tree; last item's pin is a prediction.

## 2. Predict, then measure

Write P1…Pn with a number each (arm counts, application counts, which
consumer refutes, whether the build goes red at the destructuring or the
construction).  Then run the instrument (`l4yaml-price-instruments`) or the
probe build.  Score each HELD / REFUTED; a refutation is content, not
embarrassment — say what it taught.

Probe files go in `L4YAML/Scratch/` (gitignored, deleted by some scripts) or
an out-of-tree scratchpad; number them and cite the file in the item so a
reader can re-run it.  Never leave a probe importable from a library module.

## 3. Do the work

- Proof edits: `l4yaml-adversarial-before-proof` first for any new statement;
  `lemma` not `theorem`; docstrings corrected *where they live* (§5).
- Every new declaration must have a caller or be an `@[capstone]`; zero
  callers = delete it, not TODO it.
- Expect pins to move.  Rebuild; fix the pin the build names, with the
  **cause** in the guard's comment or the item (not just the new number);
  rebuild again.  Lean stops at the first red module.

## 4. Gates (all of them, every item that builds)

See `l4yaml-build-and-gates`.  The entry quotes: `lake build` job count and
warning count, `suiterunner` pass/fail/skip, serialization hygiene,
`run-all-tests`, the four text gates, `gate_vocab`, and the axiom census of
every touched declaration (no `sorryAx`; standard three + per-site
`native_decide` only).

## 5. Write the entry

Shape (keep it; `lake run check-closure-log` gates the heading):

```
### Item N (YYYY-MM-DD)

**<headline>: what moved — PRICED | PAID | landed | no build.**  Two or three
sentences with the headline numbers and the gate summary.

**The mandate.**  "<quoted NEXT>" …

**Predictions.**  P1 … P2 …

<sections: the reading, the fix, the instrument, what the build moved>

**Predictions, scored.**  | P | said | result HELD/REFUTED — why |

**Gates.**  jobs, warnings, suiterunner a/b/c, pins moved (file: old→new, cause).

**NEXT — <step number>, <one paragraph naming the next arm/instrument>.**
```

Then: `lake run check-closure-log && python3 scripts/gate_vocab.py` — every
gate or refutation name you wrote in prose must resolve in the environment.

If the item moves a step's state, update the row in the
`#### Row 12 — the six steps that finish it` table and, if the ordered
dependencies changed, `### REMAINING, in order`.  Those two tables are the
only place state is held; the item is the record of how it got there.

## 6. Commit

One item per commit per PR: `feat(row 12): step 12.3.3 — …` for code,
`docs(row 12): item N — …` for a PRICED/no-build item, `test(guards): re-pin
… after …` when only pins move.  See `l4yaml-pr-conventions`.
