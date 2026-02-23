#!/usr/bin/env bash
set -euo pipefail

# ──────────────────────────────────────────────────────────────────────
# yaml-roundtrip-compare.sh
#
# Two-layer round-trip comparison for the Lean4-yaml-verified emitter:
#
#   Layer 1 (internal):  tryroundtrip — Lean4 parse→emit→re-parse
#                        with contentEq check (exit 0 = pass)
#
#   Layer 2 (external):  perl-refparser-event from yaml/yaml-runtimes
#                        Docker image — parse both input and canonical
#                        output to event streams, compare after
#                        normalizing style indicators.
#
# Usage:
#   ./yaml-roundtrip-compare.sh <input.yaml> <output-dir>
#   ./yaml-roundtrip-compare.sh --suite <yaml-dir> <output-dir> [--timeout N]
#
# For a single file <input.yaml>, the output directory will contain:
#   <stem>.canonical.yaml   — canonical emitter output
#   <stem>.events.input     — normalized ref-parser events for input
#   <stem>.events.canonical — normalized ref-parser events for canonical
#   <stem>.events.diff      — diff of the two event streams (if they differ)
#
# For --suite mode, the same layout is produced per test file.
#
# Requirements:
#   - .lake/build/bin/tryroundtrip  (built via `lake build tryroundtrip`)
#   - docker (for layer-2 external comparison)
#
# Environment variables:
#   SKIP_EXTERNAL=1     Skip the Docker-based external comparison
#   DOCKER_IMAGE        Override Docker image (default: yamlio/alpine-runtime-perl)
#   REFPARSER_CMD       Override the event parser command inside container
#                       (default: perl-refparser-event)
#   TRYROUNDTRIP        Path to the tryroundtrip binary
#                       (default: .lake/build/bin/tryroundtrip)
#   TIMEOUT             Timeout in seconds for each parse operation (default: 10)
# ──────────────────────────────────────────────────────────────────────

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DOCKER_IMAGE="${DOCKER_IMAGE:-yamlio/alpine-runtime-perl}"
REFPARSER_CMD="${REFPARSER_CMD:-perl-refparser-event}"
TRYROUNDTRIP="${TRYROUNDTRIP:-${SCRIPT_DIR}/.lake/build/bin/tryroundtrip}"
TIMEOUT="${TIMEOUT:-10}"
SKIP_EXTERNAL="${SKIP_EXTERNAL:-0}"

# Colors (disabled if not a terminal)
if [[ -t 1 ]]; then
  GREEN='\033[0;32m'; RED='\033[0;31m'; YELLOW='\033[0;33m'
  CYAN='\033[0;36m'; RESET='\033[0m'
else
  GREEN=''; RED=''; YELLOW=''; CYAN=''; RESET=''
fi

usage() {
  cat <<'EOF'
Usage:
  yaml-roundtrip-compare.sh <input.yaml> <output-dir>
  yaml-roundtrip-compare.sh --suite <yaml-dir> <output-dir> [--timeout N]

Options:
  --suite <dir>    Run against all .yaml files in <dir>
  --timeout N      Per-file timeout in seconds (default: 10)
  --skip-external  Skip Docker-based external comparison
  -h, --help       Show this help

Output directory layout (per input file <stem>.yaml):
  <stem>.canonical.yaml    Canonical emitter output
  <stem>.events.input      Normalized events for input
  <stem>.events.canonical  Normalized events for canonical output
  <stem>.events.diff       Diff (only when events differ)
EOF
  exit 0
}

# ──────────────── Normalize event stream ────────────────
# Strip style indicators from =VAL lines so that
#   =VAL :foo  (plain)
#   =VAL "foo  (double-quoted)
#   =VAL 'foo  (single-quoted)
# all become:
#   =VAL foo
#
# This makes the comparison style-agnostic, which is exactly
# what we need for round-trip validation.
normalize_events() {
  sed -E 's/^( *=VAL )[:"'"'"'|>]/\1/' | sed -E 's/^( *=VAL )(!![^ ]+ )[:"'"'"'|>]/\1\2/'
}

# ──────────────── Layer 1: Internal Lean4 check ────────────────
#
# Returns: 0=pass, 1=parse-fail, 2=reparse-fail, 3=contentEq-fail, 4=usage
run_internal() {
  local input="$1" output="$2"
  if ! timeout "${TIMEOUT}" "${TRYROUNDTRIP}" "${input}" "${output}" 2>/dev/null; then
    return $?
  fi
  return 0
}

# ──────────────── Layer 2: External event comparison ────────────────
#
# Runs perl-refparser-event on both files via Docker,
# normalizes the event streams, and diffs them.
# All artefacts are written to <outdir>/<stem>.events.{input,canonical,diff}.
#
# Returns: 0 if events match, 1 if they differ, 2 if refparser fails
run_external() {
  local input="$1" canonical="$2" outdir="$3" stem="$4"

  local events_in="${outdir}/${stem}.events.input"
  local events_out="${outdir}/${stem}.events.canonical"
  local events_diff="${outdir}/${stem}.events.diff"

  # Parse input through reference parser
  if ! docker run -i --rm "${DOCKER_IMAGE}" "${REFPARSER_CMD}" \
       < "${input}" 2>/dev/null | normalize_events > "${events_in}"; then
    echo "refparser-reject" > "${outdir}/${stem}.external_status"
    return 2
  fi

  # Parse canonical output through reference parser
  if ! docker run -i --rm "${DOCKER_IMAGE}" "${REFPARSER_CMD}" \
       < "${canonical}" 2>/dev/null | normalize_events > "${events_out}"; then
    echo "refparser-canonical-fail" > "${outdir}/${stem}.external_status"
    return 2
  fi

  # Compare normalized event streams
  if diff -u "${events_in}" "${events_out}" > "${events_diff}" 2>&1; then
    rm -f "${events_diff}"  # clean diff means no diff file
    return 0
  else
    return 1
  fi
}

# ──────────────── Single-file test ────────────────
run_single() {
  local input="$1"
  local outdir="$2"

  local basename
  basename="$(basename "${input}")"
  local stem="${basename%.yaml}"

  local canonical="${outdir}/${stem}.canonical.yaml"

  local result="PASS"
  local detail=""

  # Layer 1: Internal
  local rc=0
  run_internal "${input}" "${canonical}" || rc=$?
  case ${rc} in
    0) detail="internal:pass" ;;
    1) result="FAIL"; detail="internal:parse-error" ;;
    2) result="FAIL"; detail="internal:reparse-error" ;;
    3) result="FAIL"; detail="internal:contentEq-fail" ;;
    124) result="TIMEOUT"; detail="internal:timeout(${TIMEOUT}s)" ;;
    *) result="FAIL"; detail="internal:exit-${rc}" ;;
  esac

  # Layer 2: External (only if layer 1 produced output and not skipped)
  if [[ "${SKIP_EXTERNAL}" != "1" ]] && [[ -s "${canonical}" ]]; then
    local erc=0
    run_external "${input}" "${canonical}" "${outdir}" "${stem}" || erc=$?
    case ${erc} in
      0) detail="${detail} external:pass" ;;
      1)
        if [[ "${result}" == "PASS" ]]; then
          result="FAIL"
        fi
        detail="${detail} external:events-differ"
        ;;
      2)
        detail="${detail} external:$(cat "${outdir}/${stem}.external_status" 2>/dev/null || echo 'error')"
        ;;
    esac
  elif [[ "${SKIP_EXTERNAL}" == "1" ]]; then
    detail="${detail} external:skipped"
  fi

  # Report
  case "${result}" in
    PASS)    printf "${GREEN}PASS${RESET}  %s  (%s)\n" "${basename}" "${detail}" ;;
    FAIL)    printf "${RED}FAIL${RESET}  %s  (%s)\n"   "${basename}" "${detail}" ;;
    TIMEOUT) printf "${YELLOW}TMOUT${RESET} %s  (%s)\n" "${basename}" "${detail}" ;;
  esac

  [[ "${result}" == "PASS" ]]
}

# ──────────────── Suite mode ────────────────
run_suite() {
  local yaml_dir="$1"
  local outdir="$2"
  local pass=0 fail=0 timeout=0 total=0

  printf "${CYAN}=== YAML Round-Trip Suite ===${RESET}\n"
  printf "Directory: %s\n" "${yaml_dir}"
  printf "Output:    %s\n" "${outdir}"
  printf "Timeout:   %ss per file\n" "${TIMEOUT}"
  printf "External:  %s\n\n" "$( [[ "${SKIP_EXTERNAL}" == "1" ]] && echo "skipped" || echo "${DOCKER_IMAGE}" )"

  for f in "${yaml_dir}"/*.yaml; do
    [[ -f "$f" ]] || continue
    ((total++)) || true
    if run_single "$f" "${outdir}"; then
      ((pass++)) || true
    else
      case $? in
        124) ((timeout++)) || true ;;
        *)   ((fail++)) || true ;;
      esac
    fi
  done

  printf "\n${CYAN}=== Summary ===${RESET}\n"
  printf "Total: %d  ${GREEN}Pass: %d${RESET}  ${RED}Fail: %d${RESET}  ${YELLOW}Timeout: %d${RESET}\n" \
    "${total}" "${pass}" "${fail}" "${timeout}"

  [[ ${fail} -eq 0 && ${timeout} -eq 0 ]]
}

# ──────────────── CLI ────────────────
main() {
  local suite_dir=""
  local input="" outdir=""

  while [[ $# -gt 0 ]]; do
    case "$1" in
      -h|--help) usage ;;
      --suite)
        suite_dir="$2"; shift 2 ;;
      --timeout)
        TIMEOUT="$2"; shift 2 ;;
      --skip-external)
        SKIP_EXTERNAL=1; shift ;;
      -*)
        echo "Unknown option: $1" >&2; exit 1 ;;
      *)
        if [[ -z "${input}" ]]; then
          input="$1"
        elif [[ -z "${outdir}" ]]; then
          outdir="$1"
        else
          echo "Too many arguments" >&2; exit 1
        fi
        shift ;;
    esac
  done

  # Verify tryroundtrip binary exists
  if [[ ! -x "${TRYROUNDTRIP}" ]]; then
    echo "Error: tryroundtrip binary not found at ${TRYROUNDTRIP}" >&2
    echo "Build it with:  lake build tryroundtrip" >&2
    exit 1
  fi

  if [[ -n "${suite_dir}" ]]; then
    # Suite mode: first positional arg is the output directory
    if [[ -z "${input}" ]]; then
      echo "Error: --suite requires an output directory argument" >&2
      echo "Usage: $0 --suite <yaml-dir> <output-dir>" >&2
      exit 1
    fi
    outdir="${input}"
    mkdir -p "${outdir}"
    run_suite "${suite_dir}" "${outdir}"
  elif [[ -n "${input}" ]]; then
    # Single-file mode
    if [[ -z "${outdir}" ]]; then
      echo "Error: output directory is required" >&2
      echo "Usage: $0 <input.yaml> <output-dir>" >&2
      exit 1
    fi
    mkdir -p "${outdir}"
    run_single "${input}" "${outdir}"
  else
    usage
  fi
}

main "$@"
