#!/usr/bin/env bash
# Import-closed build plus fresh observations, independent of Lake log replay.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
lake build L4YAML.Proofs.Serialization 2>&1 | tee "$work/build.log"
cat > "$work/SerializationSorryProbe.lean" <<'LEAN'
theorem serializationSorryProbe : True := by
  sorry
#print axioms serializationSorryProbe
LEAN
lake env lean "$work/SerializationSorryProbe.lean" 2>&1 | tee "$work/sorry.log"
printf 'import L4YAML.Proofs.Serialization\n' > "$work/SerializationAxiomProbe.lean"
rg --no-filename --no-ignore -g '*.lean' '^#print axioms ' \
  L4YAML/Proofs/Serialization.lean L4YAML/Proofs/Serialization/ \
  >> "$work/SerializationAxiomProbe.lean"
sed -n 's/^#print axioms //p' "$work/SerializationAxiomProbe.lean" > "$work/sites.txt"
site_count=$(wc -l < "$work/sites.txt")
test "$site_count" -ge 45 \
  || { echo "axiom-site sweep found $site_count sites, expected >= 45"; exit 1; }
lake env lean "$work/SerializationAxiomProbe.lean" 2>&1 | tee "$work/axioms.log"
cat "$work/build.log" "$work/axioms.log" > "$work/qualification.log"
python3 scripts/check-serialization-axioms.py "$work/qualification.log" "$work/sorry.log" "$work/sites.txt"
