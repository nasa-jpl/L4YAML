# L4YAML vs. the YAML processor matrix

*Structural comparison of L4YAML against 20 other YAML processors on the
[yaml-test-suite](https://github.com/yaml/yaml-test-suite), scored the way
[matrix.yaml.info](https://matrix.yaml.info) scores every processor.*

Generated 2026-07-03 (first measured 2026-07-01) · suite: `yaml/yaml-test-suite`
`data` branch (402 tests) · other processors: `yamlio/alpine-runtime-all` docker
image (built 2021-11-19, the latest published aggregate; per-processor versions
in the Results table, provenance in §Processor versions) · L4YAML v0.5.0 (`main`).

---

## TL;DR

L4YAML is the only processor that is **perfect on all three axes**:

* **Accept/reject — 402/402.** It accepts all 308 valid documents and rejects
  all 94 invalid ones. Every mainstream parser (PyYAML, libyaml, SnakeYAML, …)
  wrongly rejects dozens of valid documents and/or accepts invalid ones.
* **Event axis (full structural output) — 402/402 (100%).** Every valid test's
  event stream matches `test.event` byte-for-byte; every error test is rejected.
  The next-best processors *in this run* are the generated reference parser
  (385, RefParser 0.0.3) and libfyaml (382, v0.7.2). Note that the
  [matrix.yaml.info](https://matrix.yaml.info) snapshot of 2022-01-17 records
  *different builds* of both at 402/402 on the same tests — event-axis scores
  are per-build, not per-library; see §Processor versions below.
* **JSON axis — 282/282 (100%).** Every valid test with a JSON oracle matches
  `in.json` structurally; the 3 error tests that carry a (stale) `in.json` are
  correctly rejected. Next best: YAML::PP and HsYAML (272).

The all-three-axes claim also holds against the published matrix's own
(January 2022) numbers: no processor there is perfect on all three axes either —
c-libfyaml came closest (clean event and accept/reject views, one `diff` on
its JSON view).

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

| Processor | Lang | Version | Event (of 402) | JSON (of 282) |
| --- | --- | --- | --- | --- |
| **L4YAML** | **Lean** | **0.5.0** | **402/402 (100%)** | **282/282 (100%)** |
| perl-refparser | Perl | RefParser 0.0.3 | 385/402 (96%) | – |
| c-libfyaml | C | libfyaml 0.7.2 | 382/402 (95%) | 269/282 (95%) |
| perl-pp (YAML::PP) | Perl | 0.03 | 374/402 (93%) | 272/282 (96%) |
| py-ruamel | Python | ruamel.yaml 0.16.10 | 345/402 (86%) | 239/282 (85%) |
| hs-hsyaml | Haskell | HsYAML 0.2.1.0 | 330/402 (82%) † | 272/282 (96%) |
| perl-pplibyaml | Perl | YAML::PP::LibYAML 0.005 | 330/402 (82%) | 236/282 (84%) |
| c-libyaml | C | libyaml 0.2.5 | 330/402 (82%) | – |
| py-pyyaml | Python | PyYAML 5.4.1 | 329/402 (82%) | 224/282 (79%) |
| java-snakeyaml | Java | SnakeYAML 1.29 | 322/402 (80%) | 199/282 (71%) |
| dotnet-yamldotnet | C# | YamlDotNet 11.2.1 | 317/402 (79%) † | 175/282 (62%) |
| js-yaml (npm `yaml`) | JS | 2.0.0-8 | 312/402 (78%) | 268/282 (95%) |
| nim-nimyaml | Nim | NimYAML 0.16.0 | 312/402 (78%) † | – |
| cpp-yamlcpp | C++ | yaml-cpp 0.7.0 | 151/402 (38%) † | – |
| js-jsyaml (npm `js-yaml`) | JS | 4.1.0 | – | 226/282 (80%) |
| perl-xs (YAML::XS) | Perl | 0.83 | – | 222/282 (79%) |
| ruby-psych | Ruby | psych 4.0.1 | – | 221/282 (78%) |
| lua-lyaml | Lua | lyaml 6.2.7 | – | 208/282 (74%) |
| perl-syck (YAML::Syck) | Perl | 1.34 | – | 166/282 (59%) |
| raku-yamlish | Raku | YAMLish 0.0.6 | – | 163/282 (58%) |
| perl-yaml (YAML.pm) | Perl | 1.30 | – | 101/282 (36%) |
| perl-tiny (YAML::Tiny) | Perl | 1.73 | – | 47/282 (17%) |

† These *testers* emit a reduced event format (e.g. no flow indicators or
style/tag detail), which the official matrix runner compensates for by
comparing them against correspondingly reduced expected events (see
§Processor versions); the harness here compares everyone against `test.event`
verbatim, so their scores are understated relative to the matrix's
methodology. A reminder that the event axis measures processor **+ tester**
together.

### Accept/reject axis (event-capable processors)

This is the axis behind "passes all YAML 1.2.2 tests." L4YAML is the only
processor in this run that is perfect on both halves. (The published matrix's
2022 snapshot records clean accept/reject for the libfyaml and reference-parser
builds *it* tested; the builds shipping in the aggregate image do not reproduce
that — see §Processor versions.)

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

## Processor versions

The Version column above comes from the image's own manifest
(`/yaml/info/*.yaml` inside `yamlio/alpine-runtime-all`, built 2021-11-19 —
the latest aggregate published to Docker Hub). Every non-L4YAML number in this
report is a measurement of exactly those builds.

### How this relates to matrix.yaml.info (and why the numbers differ)

The published matrix is a **January 2022 snapshot**: its tables say "Generated
with yaml-test-suite/data Commit `6e6c296a` 2022-01-17" and it has not been
regenerated since. Comparing it with this report:

* **The test content is *not* stale.** The `data-2022-01-17` tag's tree is
  bit-identical to today's `data` branch head (`6ad3d2c6`; verified —
  `git diff` between the two is empty). The 402 tests scored here are exactly
  the 402 tests the matrix scored.
* **The processor scores *are* stale — a score is a property of a build, not
  of a library.** The matrix records `c-libfyaml-event` at a clean 402/402,
  but the libfyaml **0.7.2** build shipping in the aggregate image scores
  382/402 on the identical tests (6 event diffs, 5 valid documents rejected,
  9 invalid accepted). Spot-checks confirm these are genuine parser behavior,
  not harness artifacts: 0.7.2 drops an escaped trailing tab from a
  double-quoted scalar (`DE56/02`, emits `=VAL "3 trailingtab` for
  `=VAL "3 trailing\t tab`) and accepts tab-as-indentation in flow context
  (`Y79Y/003`). The matrix's run evidently used a different (fixed) libfyaml
  build. Likewise `perl-refparser-event` shows 402/402 on the matrix while
  RefParser 0.0.3 scores 385/402 here — mostly *tester*-side encoding quirks
  (8 diffs write a scalar's trailing space as the literal marker `<SPC>`,
  3 write an escaped tab as `\\␉` instead of `\t`), plus 4 genuine parse
  differences (escaped trailing tabs, `DE56/02-03`; block-literal trailing
  newlines, `JEF9/00,02`), one valid document rejected (`JEF9/01`) and one
  error test accepted (`2G84/00`).
* **Comparison strictness differs for six testers.** The matrix runner
  ([perlpunk/yaml-test-matrix](https://github.com/perlpunk/yaml-test-matrix),
  `bin/compare-framework-tests`) compares cpp-yamlcpp, cpp-rapidyaml,
  rust-yamlrust, dotnet-yamldotnet, nim-nimyaml, and hs-hsyaml against
  *reduced* expected events (flow indicators / quoting style / anchor detail
  stripped, matching what those testers can express); everyone else — libfyaml
  and the reference parser included — is compared verbatim, as all processors
  are here. So for the four of those six present in this table (marked †),
  the matrix's methodology would score them higher than this report does. For
  libfyaml and the reference parser — compared verbatim by both — the gap is
  the build (parser or tester), not the comparison rules.

Practical upshot: published matrix numbers and this report's numbers are both
real measurements of the same 402 tests, but of different builds under
(for six testers) different comparison rules. Per-library comparisons should
always cite the build, as the Results table now does. L4YAML's own numbers are
build-pinned too (v0.5.0), with the difference that its conformance is also
theorem-backed — each parser change lands with the proof corpus re-established,
so the score is a maintained invariant rather than a per-release observation.

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
