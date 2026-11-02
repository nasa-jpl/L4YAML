#!/usr/bin/env bash
# Run the CI workflow's generation pipeline on this machine.
#
#   ./scripts/generate-all.sh                 # phases 1-5: build, test, report, docs, PDF
#   ./scripts/generate-all.sh --list          # show the phases and stop
#   ./scripts/generate-all.sh 4 5             # only the named phases
#   ./scripts/generate-all.sh --with-matrix   # also the YAML Test Matrix (needs Docker)
#   ./scripts/generate-all.sh --publish       # also write the local gh-pages branch
#
# This mirrors `.github/workflows/test-coverage.yml` (job `docs-and-tests`),
# which is otherwise the ONLY thing that builds the library, runs every suite,
# generates the documentation and scores L4YAML against the other YAML
# processors in one pass.  The workflow's matrix step is gated to `v*` tags and
# `workflow_dispatch`, so a plain push never produces one; here it is `--with-matrix`.
#
# WHAT IT DOES NOT DO, and why
#   * No elan/toolchain install.  It asserts the `lean-toolchain` toolchain is
#     present instead — installing one behind your back is not a local nicety.
#   * No system package installs (graphviz, pango/cairo).  CI may `sudo dnf`;
#     this reports what is missing and which phase will be skipped.
#   * No artifact upload and no PR comment: both are GitHub-only.
#   * No `git push`.  `--publish` calls scripts/publish-pages.sh, which writes
#     the LOCAL gh-pages branch; pushing stays a separate, deliberate act
#     (`PAGES_PUSH=1 ./scripts/publish-pages.sh`).
#
# PHASE 2 AND 4 REWRITE `docs/`.  That directory is gitignored and regenerated
# on every CI run, so this is the same contract — but it means a local `docs/`
# you were holding on to is not safe here.  `docs/reports/` is carried across
# the Phase-4 site swap exactly as CI carries it.
#
# Logs land in $WORK/logs (default `.ci-local/logs`, gitignored); each phase
# prints the log path it wrote, and the run ends with a summary table of the
# numbers a reader would otherwise have to grep for.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

WORK="${L4YAML_CI_WORK:-$ROOT/.ci-local}"
LOGS="$WORK/logs"
VENV="$WORK/venv"
REPORTS="docs/reports"

ALL_PHASES=(1 2 3 4 5)
WANT=()
WITH_MATRIX=0
WITH_PUBLISH=0
SKIP_API_DOCS=0
SKIP_FGM=0
FRESH_VENV=0

usage() {
  sed -n '2,33p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
  cat <<'EOF'

Phases
  1  build        lake build (library + 23 test exes), serialization axiom gate
  2  test         Lean suites, C shared lib + tryparse_c, Rust tryparse,
                  Python FFI + package pytest, 4-backend cross-language compare
  3  report       test-result HTML, collect-stats payload, four proof-hygiene
                  gates + the kernel-accurate sorry/axiom assertion
  4  docs         doc/ build, import graph, FGM theorem graphs, Verso render,
                  SVG <object> rewrite, swap into docs/, doc-gen4 API tree
  5  pdf          single-page HTML -> docs/L4YAML.pdf + landing-page link
  6  matrix       YAML Test Matrix vs other processors   (--with-matrix only)
  7  publish      local gh-pages branch via publish-pages.sh (--publish only)

Options
  --list            print this and exit
  --with-matrix     include phase 6 (needs a reachable Docker daemon)
  --publish         include phase 7
  --skip-api-docs   skip doc-gen4 in phase 4 (its longest step by far)
  --skip-fgm        skip the L4YAML.FGM theorem-graph download in phase 4
  --fresh-venv      rebuild the hermetic Python venv from scratch
  -h, --help        print this and exit
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    --list|-h|--help) usage; exit 0 ;;
    --with-matrix)    WITH_MATRIX=1 ;;
    --publish)        WITH_PUBLISH=1 ;;
    --skip-api-docs)  SKIP_API_DOCS=1 ;;
    --skip-fgm)       SKIP_FGM=1 ;;
    --fresh-venv)     FRESH_VENV=1 ;;
    1|2|3|4|5|6|7)    WANT+=("$1") ;;
    *) echo "error: unknown argument '$1' (try --list)" >&2; exit 2 ;;
  esac
  shift
done

if [ ${#WANT[@]} -eq 0 ]; then
  WANT=("${ALL_PHASES[@]}")
  [ "$WITH_MATRIX" = 1 ] && WANT+=(6)
  [ "$WITH_PUBLISH" = 1 ] && WANT+=(7)
fi

wants() { local p; for p in "${WANT[@]}"; do [ "$p" = "$1" ] && return 0; done; return 1; }

mkdir -p "$LOGS"
STATUS_FILE="$WORK/status.tsv"
: > "$STATUS_FILE"
note() { printf '%s\t%s\t%s\n' "$1" "$2" "$3" >> "$STATUS_FILE"; }
say()  { printf '\n\033[1m==> %s\033[0m\n' "$*"; }
warn() { printf '\033[33mwarning: %s\033[0m\n' "$*" >&2; }

# ---------------------------------------------------------------- preflight
say "Preflight"

TOOLCHAIN="$(cat lean-toolchain)"
if ! elan toolchain list 2>/dev/null | grep -qF "${TOOLCHAIN#leanprover/lean4:}"; then
  echo "error: toolchain '$TOOLCHAIN' is not installed — run: elan toolchain install $TOOLCHAIN" >&2
  exit 1
fi
echo "toolchain      $TOOLCHAIN"

# yaml-test-suite is a SUBMODULE (mode 160000). A fresh worktree gets an empty
# mount point, and the failure then reads as a missing directory rather than an
# uninitialized one, so initialize it here rather than letting phase 2 die.
if [ ! -f yaml-test-suite/src/CVW2.yaml ]; then
  echo "yaml-test-suite: initializing submodule"
  git submodule update --init --recursive yaml-test-suite
fi
echo "test corpus    $(ls yaml-test-suite/src/*.yaml 2>/dev/null | wc -l) cases"

MISSING=()
for t in cmake cargo dot; do command -v "$t" >/dev/null 2>&1 || MISSING+=("$t"); done
[ "$WITH_MATRIX" = 1 ] && { docker version >/dev/null 2>&1 || MISSING+=("docker(daemon)"); }
if [ ${#MISSING[@]} -gt 0 ]; then
  warn "missing tools: ${MISSING[*]}"
  echo "  cmake/cargo  -> phase 2's C and Rust backends"
  echo "  dot          -> phase 4's import graph"
  echo "  docker       -> phase 6"
fi

# `lake exe collect-stats --emit-lean` writes the stats payload into a TRACKED
# source file, because Verso's `:::statsTable` reads it at elaboration time.  In
# CI the checkout is throwaway; here it would leave the tree dirty on a file
# whose payload carries a timestamp, one `git commit -a` away from publication.
# So phase 3 parks the payload in $WORK, phase 4 installs it for the render, and
# the EXIT trap puts the committed placeholder back even if a phase dies.
STATS_LEAN="doc/Doc/L4YAML/StatsData.lean"
STATS_SAVED="$WORK/StatsData.lean"
STATS_INSTALLED=0
STATS_MANAGED=1
if ! git rev-parse --git-dir >/dev/null 2>&1; then
  STATS_MANAGED=0
elif ! git diff --quiet -- "$STATS_LEAN" 2>/dev/null; then
  STATS_MANAGED=0
  warn "$STATS_LEAN carries local edits — not saving and not restoring it"
fi
restore_stats() {
  [ "$STATS_INSTALLED" = 1 ] || return 0
  STATS_INSTALLED=0
  git checkout -- "$STATS_LEAN" 2>/dev/null || true
}
trap restore_stats EXIT

# Hermetic Python venv, for the reason the workflow spells out: an ambient
# PYTHONPATH (ROS exports one on this box) is searched BEFORE a venv's own
# site-packages, and the plugins it registers crash pytest. Point PYTHONPATH at
# an empty directory rather than unsetting it — "" would put the cwd on sys.path.
[ "$FRESH_VENV" = 1 ] && rm -rf "$VENV"
if [ ! -x "$VENV/bin/python3" ]; then
  PYBASE=/usr/bin/python3.12
  [ -x "$PYBASE" ] || PYBASE=/usr/bin/python3
  echo "venv           creating with $PYBASE"
  "$PYBASE" -m venv "$VENV"
  "$VENV/bin/python3" -m pip install --quiet --disable-pip-version-check --upgrade pip
  "$VENV/bin/python3" -m pip install --quiet --disable-pip-version-check pytest
fi
mkdir -p "$VENV/empty-pythonpath"
export PYTHONPATH="$VENV/empty-pythonpath"
export PYTHONNOUSERSITE=1
export PATH="$VENV/bin:$PATH"
echo "python         $(python3 --version) ($(command -v python3))"

HAS_WEASYPRINT=0
if python3 -c "import weasyprint" 2>/dev/null; then
  HAS_WEASYPRINT=1
elif python3 -m pip install --quiet --disable-pip-version-check weasyprint 2>/dev/null \
     && python3 -c "import weasyprint" 2>/dev/null; then
  HAS_WEASYPRINT=1
fi
[ "$HAS_WEASYPRINT" = 1 ] || warn "weasyprint unavailable — phase 5 will be skipped (needs pango/cairo/gdk-pixbuf)"

export L4YAML_LIB="$ROOT/ffi/out/libl4yaml.so"
export LD_LIBRARY_PATH="$ROOT/ffi/out:${LD_LIBRARY_PATH:-}"

# ------------------------------------------------------------------ phase 1
if wants 1; then
  say "Phase 1 — build"
  LOG="$LOGS/01-build.log"
  # One combined build so the final "(N jobs)" line is the job count, exactly
  # as the workflow reads it for collect-stats.
  set -o pipefail
  lake build L4YAML \
    suiterunner tryparse tryroundtrip trydump \
    tests demo explicitkeytests flowtests \
    validationtests dumproundtrip rawparsetests \
    specexamples schemadump derivingconsumer scannertests scannerspecexamples \
    adversarialtests mutationtests propertytests productioncoverage \
    limittests \
    flowregressioncheck errorstagediag scalarstagediag \
    2>&1 | tee "$LOG" | tail -1
  JOBS="$(grep -oE '\([0-9]+ jobs\)' "$LOG" | tail -1 | grep -oE '[0-9]+' || echo '?')"
  note 1 build "$JOBS jobs"
  echo "log: $LOG"

  say "Phase 1 — serialization axiom gate"
  LOG="$LOGS/01-serialization-gate.log"
  lake run check-serialization-proofs > "$LOG" 2>&1
  tail -1 "$LOG"
  note 1 serialization-gate "$(tail -1 "$LOG" | grep -oE '[0-9]+ observed profiles' || echo ok)"
  echo "log: $LOG"
fi

# ------------------------------------------------------------------ phase 2
if wants 2; then
  say "Phase 2 — Lean test suites"
  mkdir -p "$REPORTS"
  LOG="$LOGS/02-lean-suites.log"
  lake run run-all-tests -- "$REPORTS" > "$LOG" 2>&1 || {
    warn "run-all-tests failed — see $LOG"; note 2 lean-suites FAILED; }
  VERIFIED="$(grep -oE 'Verified: [0-9]+/[0-9]+' "$LOG" | tail -1 || echo '?')"
  echo "${VERIFIED:-no Verified line}"
  note 2 lean-suites "${VERIFIED:-?}"
  echo "log: $LOG"

  if command -v cmake >/dev/null 2>&1; then
    say "Phase 2 — C shared library and tryparse_c"
    LOG="$LOGS/02-c-build.log"
    { cmake -B ffi/out -S ffi && cmake --build ffi/out; } > "$LOG" 2>&1
    test -f ffi/out/libl4yaml.so && test -x ffi/out/tryparse_c
    echo "ffi/out/libl4yaml.so, ffi/out/tryparse_c"
    note 2 c-build ok
  else
    warn "cmake missing — C backend unavailable"; note 2 c-build SKIPPED
  fi

  if command -v cargo >/dev/null 2>&1; then
    say "Phase 2 — Rust tryparse"
    LOG="$LOGS/02-rust-build.log"
    ( cd rust/l4yaml && cargo build --release --example tryparse ) > "$LOG" 2>&1
    note 2 rust-build ok
  else
    warn "cargo missing — Rust backend unavailable"; note 2 rust-build SKIPPED
  fi

  say "Phase 2 — Python FFI tests"
  LOG="$REPORTS/python-ffi-tests.txt"
  echo "=== Python FFI Tests ===" > "$LOG"
  set -o pipefail
  python3 -m pytest Tests/test_python_ffi.py -v --tb=short --no-header \
    --junitxml="$REPORTS/python-ffi-junit.xml" 2>&1 | tee -a "$LOG" | tail -3
  note 2 python-ffi "$(grep -oE '[0-9]+ passed' "$LOG" | tail -1 || echo ok)"

  say "Phase 2 — Python package tests"
  LOG="$REPORTS/python-package-tests.txt"
  echo "=== Python Package Tests ===" > "$LOG"
  python3 -m pytest python/tests/ -v --tb=short --no-header \
    --junitxml="$REPORTS/python-package-junit.xml" 2>&1 | tee -a "$LOG" | tail -3
  note 2 python-package "$(grep -oE '[0-9]+ passed' "$LOG" | tail -1 || echo ok)"

  say "Phase 2 — cross-language comparison (4 backends x 5 presets)"
  LOG="$REPORTS/cross-lang-comparison.txt"
  echo "=== Cross-Language yaml-test-suite Comparison ===" > "$LOG"
  python3 scripts/cross-lang-compare.py "$REPORTS" 2>&1 | tee -a "$LOG" | tail -8
  note 2 cross-language "$(grep -cE 'all 4 backends identical' "$LOG" || echo 0)/5 presets identical"
fi

# ------------------------------------------------------------------ phase 3
if wants 3; then
  say "Phase 3 — test-result HTML reports"
  python3 scripts/generate-test-reports.py "$REPORTS" > "$LOGS/03-reports.log" 2>&1
  note 3 reports ok

  say "Phase 3 — collect stats"
  LOG="$LOGS/03-collect-stats.log"
  lake exe collect-stats --emit-lean > "$LOG" 2>&1
  test -f "$REPORTS/stats.json"
  grep -q 'statsJson? : Option String := some' "$STATS_LEAN"
  if [ "$STATS_MANAGED" = 1 ]; then
    cp "$STATS_LEAN" "$STATS_SAVED"
    git checkout -- "$STATS_LEAN"
  fi
  note 3 collect-stats ok

  say "Phase 3 — proof-hygiene gates"
  LOG="$LOGS/03-gates.log"
  : > "$LOG"
  # A gate's verdict has to reach the SUMMARY, not just the log.  Printing
  # `FAILED` into $LOG and warning on stderr left the status file saying only
  # `env clean: N theorems`, so the run exited 0 with two gates red and the
  # module-system branch read as green for a day (2026-10-17).  `note` is what
  # the end-of-run `grep FAILED "$STATUS_FILE"` reads.
  GATES_FAILED=""
  for g in check-theorem-keyword check-import-closure check-reflection-index check-closure-log; do
    printf '%-26s ' "$g" | tee -a "$LOG"
    if lake run "$g" >> "$LOG" 2>&1; then echo "ok" | tee -a "$LOG"
    else
      echo "FAILED" | tee -a "$LOG"; warn "$g failed — see $LOG"
      GATES_FAILED="${GATES_FAILED:+$GATES_FAILED }$g"
    fi
  done
  if [ -n "$GATES_FAILED" ]; then note 3 hygiene-gates "FAILED: $GATES_FAILED"; fi
  # The kernel-accurate half: zero theorems with a sorry, zero custom axioms,
  # measured over the compiled environment rather than by grepping sources.
  python3 - "$REPORTS/stats.json" <<'EOF' | tee -a "$LOG"
import json, sys
env = json.load(open(sys.argv[1]))['env']
bad = {k: env[k] for k in ('theorems_with_transitive_sorry', 'theorems_with_direct_sorry',
                           'theorems_with_custom_axiom', 'axioms') if env[k] != 0}
if bad:
    sys.exit(f"proof-hygiene gate failed: {bad}")
print(f"env clean: {env['theorems']} theorems, 0 sorries, 0 custom axioms")
EOF
  note 3 hygiene-gates "$(grep -oE 'env clean: [0-9]+ theorems' "$LOG" | tail -1 || echo '?')"
  echo "log: $LOG"
fi

# ------------------------------------------------------------------ phase 4
if wants 4; then
  say "Phase 4 — doc/ sub-project build"
  if [ "$STATS_MANAGED" = 1 ]; then
    if [ -f "$STATS_SAVED" ]; then
      cp "$STATS_SAVED" "$STATS_LEAN"
      STATS_INSTALLED=1
    else
      warn "no stats payload in $WORK — statsTable cells render '?' (run phase 3 first)"
    fi
  fi
  LOG="$LOGS/04-doc-build.log"
  ( cd doc && lake update && lake build l4yaml-doc ) > "$LOG" 2>&1
  echo "$(grep -oE 'Build completed successfully \([0-9]+ jobs\)' "$LOG" | tail -1 || echo built)"
  note 4 doc-build "$(grep -oE '\([0-9]+ jobs\)' "$LOG" | tail -1 || echo '?')"

  if command -v dot >/dev/null 2>&1; then
    say "Phase 4 — import graph"
    LOG="$LOGS/04-import-graph.log"
    mkdir -p doc/Doc/L4YAML/graphs
    {
      lake build graph
      lake exe graph \
        --to=L4YAML.Scanner.Scanner,L4YAML.Parser.Composition,L4YAML.Surface.Document,L4YAML.Output.Dump,L4YAML.Output.Emitter,L4YAML.FFI.FFI,L4YAML.Schema.Api,L4YAML.Config.Config \
        doc/Doc/L4YAML/graphs/import-graph.dot
      dot -Tsvg doc/Doc/L4YAML/graphs/import-graph.dot \
        -o doc/Doc/L4YAML/graphs/import-graph.svg
    } > "$LOG" 2>&1
    note 4 import-graph ok
  else
    warn "dot missing — import graph not regenerated"; note 4 import-graph SKIPPED
  fi

  # The ~20 headline theorem-dependency SVGs the verification chapter embeds.
  # CI pulls them from a GHE release with its job token; locally that is `gh`.
  # Non-fatal: the render succeeds without them, with those figures absent.
  if [ "$SKIP_FGM" = 1 ]; then
    note 4 fgm-graphs SKIPPED
  else
    say "Phase 4 — theorem graphs from L4YAML.FGM"
    LOG="$LOGS/04-fgm-graphs.log"
    mkdir -p doc/Doc/L4YAML/graphs
    if GH_HOST=github.jpl.nasa.gov gh release download graphs-latest \
         --repo pass/L4YAML.FGM --pattern theorem-graphs-headlines.tar.gz \
         --dir doc/Doc/L4YAML/graphs --clobber > "$LOG" 2>&1; then
      tar xzf doc/Doc/L4YAML/graphs/theorem-graphs-headlines.tar.gz -C doc/Doc/L4YAML/graphs/
      rm -f doc/Doc/L4YAML/graphs/theorem-graphs-headlines.tar.gz
      # Recursive, and excluding the import graph: the tarball extracts into
      # `L4YAML/`, `group/` and `module/`, so a top-level glob would match only
      # `import-graph.svg` — the previous step's output, and none of these.
      N="$(find doc/Doc/L4YAML/graphs -name '*.svg' -not -name 'import-graph.svg' | wc -l)"
      echo "$N theorem-graph SVGs"
      note 4 fgm-graphs "$N svgs"
    else
      warn "could not download theorem graphs (see $LOG) — chapter figures will be missing"
      note 4 fgm-graphs UNAVAILABLE
    fi
  fi

  say "Phase 4 — Verso render"
  LOG="$LOGS/04-verso-render.log"
  ( cd doc && lake exe l4yaml-doc ) > "$LOG" 2>&1
  python3 scripts/svg-objects.py doc/_out/html-multi | tee -a "$LOG" | tail -1

  # Assemble beside docs/reports and swap, so Phase 2-3's reports survive.
  rm -rf docs.new
  cp -r doc/_out/html-multi docs.new
  [ -d "$REPORTS" ] && cp -r "$REPORTS" docs.new/reports
  rm -rf docs
  mv docs.new docs
  # Count the render apart from what is staged beside it.  `<base>` is Verso's
  # own marker, so it counts pages the render produced and not the HTML that
  # arrives with them: `graphs/` from the import-graph and theorem-graph steps,
  # `reports/` from phases 2-3.  A path exclusion would need editing whenever
  # `extraFilesHtml` gains an entry; this does not, and if the marker ever stops
  # matching the count reads 0 rather than quietly absorbing the staged files.
  # Each count is guarded: an empty `grep`/`find` exits 1, which `pipefail`
  # would turn into the script dying here instead of reporting a zero.
  VPAGES="$({ grep -rl '<base' doc/_out/html-multi --include='*.html' || true; } | wc -l)"
  GPAGES="$({ find docs/graphs -name '*.html' 2>/dev/null || true; } | wc -l)"
  RPAGES="$({ find docs/reports -name '*.html' 2>/dev/null || true; } | wc -l)"
  echo "docs/ rebuilt — $VPAGES rendered pages, $GPAGES staged graph pages, $RPAGES report pages"
  note 4 verso-render "$VPAGES pages +$GPAGES graphs +$RPAGES reports"
  restore_stats

  if [ "$SKIP_API_DOCS" = 1 ]; then
    note 4 api-docs SKIPPED
  else
    say "Phase 4 — doc-gen4 API documentation"
    LOG="$LOGS/04-api-docs.log"
    lake build :docs > "$LOG" 2>&1
    cp -r .lake/build/doc docs/api
    note 4 api-docs ok
  fi
fi

# ------------------------------------------------------------------ phase 5
if wants 5; then
  if [ "$HAS_WEASYPRINT" = 1 ]; then
    say "Phase 5 — PDF"
    LOG="$LOGS/05-pdf.log"
    python3 scripts/html-to-pdf.py doc/_out/html-single/index.html docs/L4YAML.pdf > "$LOG" 2>&1
    if [ -f docs/L4YAML.pdf ]; then
      sed -i 's|strategy, security model, and FFI bindings for C, Python, and Rust.</p>|strategy, security model, and FFI bindings for C, Python, and Rust.</p>\n              <p>\n                A PDF version of this manual is available for download:\n<a href="L4YAML.pdf">L4YAML.pdf</a>.</p>|' docs/index.html
      echo "docs/L4YAML.pdf ($(du -h docs/L4YAML.pdf | cut -f1))"
      note 5 pdf "$(du -h docs/L4YAML.pdf | cut -f1)"
    fi
  else
    warn "phase 5 skipped — weasyprint unavailable"; note 5 pdf SKIPPED
  fi
fi

# ------------------------------------------------------------------ phase 6
if wants 6; then
  say "Phase 6 — YAML Test Matrix"
  if ! docker version >/dev/null 2>&1; then
    warn "Docker not accessible for user '$(id -un)' — matrix skipped (add the account to the 'docker' group)"
    note 6 matrix SKIPPED
  else
    LOG="$LOGS/06-matrix.log"
    RUNTIMES_REPO=https://github.com/NicolasRouquette/yaml-runtimes.git
    RUNTIMES_REF=l4yaml
    MATRIX_REPO=https://github.com/NicolasRouquette/yaml-test-matrix.git
    MATRIX_REF=l4yaml
    # Pinned so the matrix matches matrix.yaml.info's snapshot. Bump deliberately.
    TESTSUITE_DATA_REF=data-2022-01-17
    MWORK="$WORK/yaml-matrix"
    rm -rf "$MWORK"; mkdir -p "$MWORK"
    {
      # This commit's testers go in via the prebuilt path, so the matrix scores
      # the checked-out code rather than a released tarball.
      lake build l4yaml-event l4yaml-json
      git clone --depth 1 --branch "$RUNTIMES_REF" "$RUNTIMES_REPO" "$MWORK/yaml-runtimes"
      install -D .lake/build/bin/l4yaml-event "$MWORK/yaml-runtimes/docker/lean/prebuilt/l4yaml-event"
      install -D .lake/build/bin/l4yaml-json  "$MWORK/yaml-runtimes/docker/lean/prebuilt/l4yaml-json"
      VER="$(grep -oE 'version := v!"[^"]+"' lakefile.lean | grep -oE '[0-9][0-9.]*' | head -1 || true)"
      [ -n "$VER" ] && sed -i "s/,0\\.5\\.0,/,$VER,/g" "$MWORK/yaml-runtimes/docker/lean/info/views.csv" || true
      docker build -t yamlio/alpine-runtime-lean \
        -f "$MWORK/yaml-runtimes/docker/lean/prebuilt.dockerfile" \
        "$MWORK/yaml-runtimes/docker/lean"

      git clone --depth 1 --branch "$MATRIX_REF" "$MATRIX_REPO" "$MWORK/yaml-test-matrix"
      docker build -t yaml-test-matrix:driver \
        -f "$MWORK/yaml-test-matrix/docker/Dockerfile" "$MWORK/yaml-test-matrix/docker"

      for rt in static python perl node ruby haskell dotnet lua; do
        docker pull -q "yamlio/alpine-runtime-$rt" \
          || echo "warning: could not pull yamlio/alpine-runtime-$rt — its views will be skipped"
      done

      cd "$MWORK/yaml-test-matrix"
      git clone --quiet --depth 1 --branch "$TESTSUITE_DATA_REF" \
        https://github.com/yaml/yaml-test-suite yaml-test-suite/data
      wget -qO list.yaml \
        "https://raw.githubusercontent.com/NicolasRouquette/yaml-runtimes/$RUNTIMES_REF/list.yaml"
      mkdir -p matrix/data matrix/tmp

      DOCKER_GID="$(getent group docker | cut -d: -f3 || true)"
      GROUPADD=""
      [ -n "$DOCKER_GID" ] && GROUPADD="--group-add $DOCKER_GID"
      docker run --rm \
        -v /var/run/docker.sock:/var/run/docker.sock \
        -v "$PWD":"$PWD" -w "$PWD" \
        --user "$(id -u):$(id -g)" $GROUPADD \
        yaml-test-matrix:driver \
        sh -eu -c '
          ./bin/expected
          views="$(./bin/run-framework-tests --list)"
          for v in $views; do ./bin/run-framework-tests --view "$v" || echo "warning: matrix run $v failed"; done
          for v in $views; do ./bin/compare-framework-tests --view "$v" || echo "warning: matrix compare $v failed"; done
          ./bin/create-matrix
          ./bin/highlight || true
        '
    } > "$LOG" 2>&1

    cd "$ROOT"
    mkdir -p docs
    rm -rf docs/matrix
    cp -r "$MWORK/yaml-test-matrix/matrix/html" docs/matrix
    N="$(find docs/matrix -type f | wc -l)"
    echo "docs/matrix — $N files"
    note 6 matrix "$N files"

    if [ -f docs/index.html ] && ! grep -q 'matrix/index.html' docs/index.html; then
      sed -i 's|strategy, security model, and FFI bindings for C, Python, and Rust.</p>|&\n              <p>Conformance vs other YAML processors on the <a href="https://github.com/yaml/yaml-test-suite">yaml-test-suite</a>: see the <a href="matrix/index.html">YAML Test Matrix</a>.</p>|' docs/index.html \
        && echo "matrix link injected into docs/index.html" \
        || warn "could not inject matrix link (landing anchor not found)"
    fi
  fi
fi

# ------------------------------------------------------------------ phase 7
if wants 7; then
  say "Phase 7 — local gh-pages branch"
  bash scripts/publish-pages.sh > "$LOGS/07-publish.log" 2>&1
  echo "gh-pages written locally; push with: PAGES_PUSH=1 ./scripts/publish-pages.sh"
  note 7 publish ok
fi

# ------------------------------------------------------------------- summary
say "Summary"
printf '%-6s %-22s %s\n' PHASE STEP RESULT
printf '%-6s %-22s %s\n' ----- ---- ------
while IFS=$'\t' read -r p s r; do printf '%-6s %-22s %s\n' "$p" "$s" "$r"; done < "$STATUS_FILE"
echo
echo "logs:  $LOGS"
echo "site:  $ROOT/docs"
if grep -q 'FAILED' "$STATUS_FILE"; then
  echo
  warn "at least one step FAILED — the site above was still assembled from whatever succeeded"
  exit 1
fi
