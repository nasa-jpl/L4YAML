#!/usr/bin/env bash
# Show or bump the L4YAML package version across every file that declares it.
#
#   scripts/bump-version.sh            # print the current version
#   scripts/bump-version.sh +p         # bump patch  (X.Y.Z   -> X.Y.(Z+1))
#   scripts/bump-version.sh +m         # bump minor  (X.Y.Z   -> X.(Y+1).0)
#   scripts/bump-version.sh +M         # bump major  (X.Y.Z   -> (X+1).0.0)
#
# The version is declared in five places kept in lockstep: the Lean package
# (lakefile.lean), the Python package and its __version__, and the two Rust
# crates. The script refuses to bump when they disagree, so a divergence is
# fixed by hand rather than half-bumped. CI's YAML Test Matrix and its `v*`
# trigger key off this version, so after a bump: commit, then `git tag vX.Y.Z`
# to cut the release and fire the matrix.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Each site: <file>|<literal text just before the version>|<literal text after>.
# The `before` text (anchored to the start of the line) must uniquely identify
# the version-declaration line so dependency versions are never touched.
SITES=(
  'lakefile.lean|  version := v!"|"'
  'python/pyproject.toml|version = "|"'
  'python/l4yaml/__init__.py|__version__ = "|"'
  'rust/l4yaml/Cargo.toml|version = "|"'
  'rust/l4yaml-sys/Cargo.toml|version = "|"'
)

SEMVER='[0-9]+\.[0-9]+\.[0-9]+'

usage() {
  # Print the leading comment block (minus the shebang), stopping at the first
  # non-comment line — robust to edits of the header length.
  awk 'NR==1 {next} /^#/ {sub(/^# ?/, ""); print; next} {exit}' "$0"
}

# Escape a literal string for the left-hand side of a sed s/// (ERE metachars).
sed_lhs() { printf '%s' "$1" | sed -e 's/[].[^$*\/&]/\\&/g'; }
# Escape a literal string for the right-hand side of a sed s/// (& and \ and /).
sed_rhs() { printf '%s' "$1" | sed -e 's/[\/&\\]/\\&/g'; }

read_version() {   # <file> <before> <after>  -> first declared X.Y.Z (or empty)
  local file=$1 before=$2 after=$3 b a
  b=$(sed_lhs "$before"); a=$(sed_lhs "$after")
  sed -nE "s/^${b}(${SEMVER})${a}.*/\1/p" "$file" | head -1
}

# --- Gather the current version from every site and require agreement. --------
current=""
mismatch=0
report=()
for site in "${SITES[@]}"; do
  IFS='|' read -r file before after <<<"$site"
  [[ -f $file ]] || { echo "error: missing $file" >&2; exit 1; }
  v=$(read_version "$file" "$before" "$after")
  [[ -n $v ]] || { echo "error: no version in $file (expected '${before}X.Y.Z${after}')" >&2; exit 1; }
  report+=("  $v  $file")
  if [[ -z $current ]]; then current=$v
  elif [[ $v != "$current" ]]; then mismatch=1; fi
done

if (( mismatch )); then
  echo "error: version declarations disagree -- reconcile before bumping:" >&2
  printf '%s\n' "${report[@]}" >&2
  exit 1
fi

# --- Dispatch on the argument. ------------------------------------------------
arg=${1:-}
case $arg in
  '')        echo "$current"; exit 0 ;;
  -h|--help) usage; exit 0 ;;
  +M|+m|+p)  ;;
  *)         echo "error: unknown argument '$arg' (use +p, +m, +M, or no args)" >&2; usage >&2; exit 2 ;;
esac

IFS=. read -r MA MI PA <<<"$current"
case $arg in
  +M) MA=$((MA + 1)); MI=0; PA=0 ;;
  +m) MI=$((MI + 1)); PA=0 ;;
  +p) PA=$((PA + 1)) ;;
esac
new="$MA.$MI.$PA"

# --- Apply the bump and verify each write. ------------------------------------
oldre=${current//./\\.}
for site in "${SITES[@]}"; do
  IFS='|' read -r file before after <<<"$site"
  b=$(sed_lhs "$before"); a=$(sed_lhs "$after")
  rb=$(sed_rhs "$before"); ra=$(sed_rhs "$after")
  sed -i -E "s/^${b}${oldre}${a}/${rb}${new}${ra}/" "$file"
  got=$(read_version "$file" "$before" "$after")
  [[ $got == "$new" ]] || { echo "error: failed to update $file (still '$got')" >&2; exit 1; }
done

echo "bumped $current -> $new in:"
printf '%s\n' "${SITES[@]}" | cut -d'|' -f1 | sed 's/^/  /'
echo
echo "next:  git commit -am \"chore: bump version to $new\" && git tag v$new"
echo "       (pushing the v$new tag fires the YAML Test Matrix CI and republishes the site)"
