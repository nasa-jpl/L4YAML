# L4YAML vs. the YAML processor matrix

*Structural comparison of L4YAML against 20 other YAML processors on the
[yaml-test-suite](https://github.com/yaml/yaml-test-suite), scored the way
[matrix.yaml.info](https://matrix.yaml.info) scores every processor.*

Generated 2026-07-01 · suite: `yaml/yaml-test-suite` `data` branch (402 tests) ·
other processors: `yamlio/alpine-runtime-all` docker image.

---

## TL;DR

* **Accept/reject axis — L4YAML is the only perfect processor.** It accepts all
  308 valid documents and rejects all 94 invalid ones (**402/402**). Every
  mainstream parser (PyYAML, libyaml, SnakeYAML, …) wrongly rejects dozens of
  valid documents and/or accepts invalid ones. This is what "passes all YAML
  1.2.2 tests" means, and it holds.
* **Event axis (full structural output) — 362/402 (90%), 4th of 14** event-capable
  processors, behind only the generated reference parser, libfyaml, and YAML::PP.
* **JSON axis — 240/282 (85%)**, upper-middle of the pack.
* **Yes, the event and JSON axes had *not* been exercised before this.** The
  existing suite runner only checked accept/reject (does `parseYaml` succeed);
  it never compared L4YAML's *output* against each test's expected events or
  JSON. Two new emitters (`l4yaml-event`, `l4yaml-json`) close that gap.

The 40 event / 42 JSON mismatches are **content-representation differences, not
parse failures** — over half are a single root cause: the trailing newline of
folded/clipped block scalars (see [Where the diffs come from](#where-the-diffs-come-from)).

---

## What was measured, and why it's new

The [yaml-test-suite](https://github.com/yaml/yaml-test-suite) encodes three
independent oracles per test:

| oracle       | question                                        | axis          |
| ------------ | ----------------------------------------------- | ------------- |
| `error` file | should the parser **reject** this input?        | accept/reject |
| `test.event` | does the emitted **event stream** match?        | event         |
| `in.json`    | does the emitted **JSON** match (Core Schema)?  | json          |

L4YAML's `Tests/SuiteRunner` only ever asked the first question — it ran
`parseYaml` and checked the exit status. It even parsed each test's expected
event tree into `TestCase.tree` but **never compared against it**. So the
structural correctness of L4YAML's output was untested, and L4YAML could not be
placed on the matrix, whose primary axis *is* the event stream.

Two emitters now produce the matrix's comparison formats directly from the
`YamlValue` representation graph:

* [`L4YAML/Output/Events.lean`](L4YAML/Output/Events.lean) → `l4yaml-event`
  (test-suite event notation; runs on the *raw* parse so anchors/aliases survive).
* [`L4YAML/Output/Json.lean`](L4YAML/Output/Json.lean) → `l4yaml-json`
  (Core-Schema JSON; runs on the composed parse so aliases resolve).

Both are pure functions over the existing AST — no parser changes were needed.

Every processor — L4YAML's native binaries and all 20 docker testers — is scored
through one harness ([`scripts/matrix_score.py`](scripts/matrix_score.py)) over
the identical 402-test data form, so the numbers are apples-to-apples.

---

## Results

### Event axis — full structural output (402 tests)

`correct` = event stream matches `test.event` on valid tests **and** the parser
rejects each error test.

| Processor | Lang | Event (of 402) | JSON (of 282) |
| --- | --- | --- | --- |
| perl-refparser | Perl | 385/402 (95%) | – |
| c-libfyaml | C | 382/402 (95%) | 267/282 (94%) |
| perl-pp (YAML::PP) | Perl | 374/402 (93%) | 269/282 (95%) |
| **L4YAML** | **Lean** | **362/402 (90%)** | **240/282 (85%)** |
| py-ruamel | Python | 345/402 (85%) | 237/282 (84%) |
| hs-hsyaml | Haskell | 330/402 (82%) | 269/282 (95%) |
| perl-pplibyaml | Perl | 330/402 (82%) | 234/282 (82%) |
| c-libyaml | C | 330/402 (82%) | – |
| py-pyyaml | Python | 329/402 (81%) | 222/282 (78%) |
| java-snakeyaml | Java | 322/402 (80%) | 197/282 (69%) |
| dotnet-yamldotnet | C# | 317/402 (78%) | 173/282 (61%) |
| js-yaml | JS | 312/402 (77%) | 265/282 (93%) |
| nim-nimyaml | Nim | 312/402 (77%) | – |
| cpp-yamlcpp | C++ | 151/402 (37%) † | – |
| js-jsyaml | JS | – | 224/282 (79%) |
| perl-xs | Perl | – | 220/282 (78%) |
| ruby-psych | Ruby | – | 219/282 (77%) |
| lua-lyaml | Lua | – | 206/282 (73%) |
| perl-syck | Perl | – | 166/282 (58%) |
| raku-yamlish | Raku | – | 162/282 (57%) |
| perl-yaml (YAML.pm) | Perl | – | 98/282 (34%) |
| perl-tiny | Perl | – | 44/282 (15%) |

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

## Where the diffs come from

L4YAML parses every test correctly (accept/reject is perfect); its 40 event
diffs are purely in how output is *represented*:

| root cause | count | example ids |
| --- | --- | --- |
| **block-scalar trailing newline** (folded/clipped `>`/`\|` drop the clip `\n`) | **22** | 5BVJ 735Y 96L6 FP8R HMK4 F6MC |
| tab / whitespace inside a scalar value | 6 | DE56 HS5T R4YG UV7Q |
| other single-scalar content | 6 | 6CK3 (tag `%21`→`!`), MZX3, NB6Z |
| structural (empty-doc / tagged-empty-node emission) | 6 | FH7J HWV9 PW8X QT73 |

The JSON axis fails for the same reasons: **33 of 42** JSON diffs coincide with
event diffs (the folded-newline difference changes string values too). The 9
JSON-only diffs are number-formatting / non-string-key edge cases
(2AUY 33X3 3GZX 74H7 F2C7 L94M …).

**Biggest single lever:** giving folded/clipped block scalars their trailing
clip newline would fix ~22 event diffs and most JSON diffs at once, moving
L4YAML from 362 → ~384 (≈95%), level with libfyaml and the reference parser.

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
the Alpine `alpine-runtime-all` aggregate. The runtime image was built and
verified to score identically to the native binaries (event 362/402,
json 240/282). To publish it from source, the two emitters and their lake
targets must be pushed to `nasa-jpl/L4YAML` (`feature/intrinsic-foundations`).
