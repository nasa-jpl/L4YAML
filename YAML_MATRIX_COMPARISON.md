# L4YAML vs. the YAML processor matrix

*Structural comparison of L4YAML against 20 other YAML processors on the
[yaml-test-suite](https://github.com/yaml/yaml-test-suite), scored the way
[matrix.yaml.info](https://matrix.yaml.info) scores every processor.*

Generated 2026-07-03 (first measured 2026-07-01) · suite: `yaml/yaml-test-suite`
`data` branch (402 tests) · other processors: `yamlio/alpine-runtime-all` docker
image · L4YAML v0.5.0 (`main`).

---

## TL;DR

L4YAML is the only processor that is **perfect on all three axes**:

* **Accept/reject — 402/402.** It accepts all 308 valid documents and rejects
  all 94 invalid ones. Every mainstream parser (PyYAML, libyaml, SnakeYAML, …)
  wrongly rejects dozens of valid documents and/or accepts invalid ones.
* **Event axis (full structural output) — 402/402 (100%).** Every valid test's
  event stream matches `test.event` byte-for-byte; every error test is rejected.
  The next-best processors are the generated reference parser (385) and
  libfyaml (382).
* **JSON axis — 282/282 (100%).** Every valid test with a JSON oracle matches
  `in.json` structurally; the 3 error tests that carry a (stale) `in.json` are
  correctly rejected. Next best: YAML::PP and HsYAML (272).

When first measured (2026-07-01) L4YAML scored 362/402 event and 240/282 JSON —
the two output axes had never been exercised before (the in-repo suite runner
only checked accept/reject, never L4YAML's *output*). Two new emitters
(`l4yaml-event`, `l4yaml-json`) closed that observation gap, and ten targeted
fixes (trailing newline of folded/clipped block scalars, tab handling in
scalars, empty-node-with-properties sequence entries, bare `...` document
suffixes, explicit-key splitting, tag percent-escapes, escaped trailing tabs,
position-relative alias rebinding, …) closed every remaining difference —
each with the parser's correctness proofs re-established.

---

## What was measured

The [yaml-test-suite](https://github.com/yaml/yaml-test-suite) encodes three
independent oracles per test:

| oracle       | question                                        | axis          |
| ------------ | ----------------------------------------------- | ------------- |
| `error` file | should the parser **reject** this input?        | accept/reject |
| `test.event` | does the emitted **event stream** match?        | event         |
| `in.json`    | does the emitted **JSON** match (Core Schema)?  | json          |

Two emitters produce the matrix's comparison formats directly from the
`YamlValue` representation graph:

* [`L4YAML/Output/Events.lean`](L4YAML/Output/Events.lean) → `l4yaml-event`
  (test-suite event notation; runs on the *raw* parse so anchors/aliases survive).
* [`L4YAML/Output/Json.lean`](L4YAML/Output/Json.lean) → `l4yaml-json`
  (Core-Schema JSON; runs on the composed parse so aliases resolve).

Both are pure functions over the existing AST — no parser changes were needed
to *observe* the output (the fixes above were parser/scanner changes, each
carried through the proof corpus).

Every processor — L4YAML's native binaries and all 20 docker testers — is scored
through one harness ([`scripts/matrix_score.py`](scripts/matrix_score.py)) over
the identical 402-test data form, so the numbers are apples-to-apples. On both
axes an error test counts as correct iff the processor rejects it (three error
tests ship a stale `in.json`; matching it would mean accepting invalid YAML).

---

## Results

### Event and JSON axes (402 tests; 282 carry a JSON oracle)

`correct` = output matches the oracle on valid tests **and** the parser rejects
each error test.

| Processor | Lang | Event (of 402) | JSON (of 282) |
| --- | --- | --- | --- |
| **L4YAML** | **Lean** | **402/402 (100%)** | **282/282 (100%)** |
| perl-refparser | Perl | 385/402 (96%) | – |
| c-libfyaml | C | 382/402 (95%) | 269/282 (95%) |
| perl-pp (YAML::PP) | Perl | 374/402 (93%) | 272/282 (96%) |
| py-ruamel | Python | 345/402 (86%) | 239/282 (85%) |
| hs-hsyaml | Haskell | 330/402 (82%) | 272/282 (96%) |
| perl-pplibyaml | Perl | 330/402 (82%) | 236/282 (84%) |
| c-libyaml | C | 330/402 (82%) | – |
| py-pyyaml | Python | 329/402 (82%) | 224/282 (79%) |
| java-snakeyaml | Java | 322/402 (80%) | 199/282 (71%) |
| dotnet-yamldotnet | C# | 317/402 (79%) | 175/282 (62%) |
| js-yaml | JS | 312/402 (78%) | 268/282 (95%) |
| nim-nimyaml | Nim | 312/402 (78%) | – |
| cpp-yamlcpp | C++ | 151/402 (38%) † | – |
| js-jsyaml | JS | – | 226/282 (80%) |
| perl-xs | Perl | – | 222/282 (79%) |
| ruby-psych | Ruby | – | 221/282 (78%) |
| lua-lyaml | Lua | – | 208/282 (74%) |
| perl-syck | Perl | – | 166/282 (59%) |
| raku-yamlish | Raku | – | 163/282 (58%) |
| perl-yaml (YAML.pm) | Perl | – | 101/282 (36%) |
| perl-tiny | Perl | – | 47/282 (17%) |

† cpp-yamlcpp's *tester* emits a reduced event format (no style/tag detail); the
low score reflects the tester, not necessarily the library. A reminder that the
event axis measures processor **+ tester** together.

### Accept/reject axis (event-capable processors)

This is the axis behind "passes all YAML 1.2.2 tests." L4YAML is the only
processor that is perfect on both halves.

| Processor | valid accepted | invalid rejected |  |
| --- | --- | --- | --- |
| **L4YAML** | **308/308** | **94/94** | ✓ perfect |
| perl-refparser | 307/308 | 93/94 | |
| hs-hsyaml | 299/308 | 94/94 | |
| c-libfyaml | 303/308 | 85/94 | |
| js-yaml | 303/308 | 81/94 | |
| dotnet-yamldotnet | 298/308 | 83/94 | |
| nim-nimyaml | 303/308 | 76/94 | |
| perl-pp | 292/308 | 82/94 | |
| py-ruamel | 274/308 | 77/94 | |
| c-libyaml | 257/308 | 78/94 | |
| py-pyyaml | 254/308 | 80/94 | |
| java-snakeyaml | 249/308 | 78/94 | |

L4YAML never rejects a valid document (0 false negatives) and never accepts an
invalid one (0 false positives). The mainstream C/Python/Java parsers reject
50-60 valid documents each.

---

## Reproducing

```bash
# 1. canonical test data (per-test in.yaml / test.event / in.json / error)
cd yaml-test-suite && git fetch --depth 1 origin data
git archive FETCH_HEAD | tar -x -C /path/to/suite-data

# 2. other processors (one image has them all)
docker pull yamlio/alpine-runtime-all
docker run -d --name yamlall yamlio/alpine-runtime-all tail -f /dev/null

# 3. L4YAML's own numbers, in-repo, no docker:
lake build eventscore
.lake/build/bin/eventscore --suite ../yaml-test-suite            # event + error axes

# 4. the full apples-to-apples table:
lake build l4yaml-event l4yaml-json
python3 scripts/matrix_score.py --data /path/to/suite-data --axis both \
    --l4yaml-event .lake/build/bin/l4yaml-event \
    --l4yaml-json  .lake/build/bin/l4yaml-json \
    --out results.json
```

## Matrix contribution

A `lean` runtime for [yaml-runtimes](https://github.com/yaml/yaml-runtimes) was
added (`docker/lean/`: Dockerfile, testers, build script, `list.yaml` entry).
Because Lean 4 is glibc-based it is a **standalone Debian image**, not part of
the Alpine `alpine-runtime-all` aggregate. The image builds from the published
`nasa-jpl/L4YAML` `main` branch and its in-container testers score identically
to the native binaries (event 402/402, json 282/282).
