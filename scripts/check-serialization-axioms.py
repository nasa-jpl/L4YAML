#!/usr/bin/env python3
"""Validate complete kernel axiom observations and a deliberate sorry control."""
from pathlib import Path
import re
import sys

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
EXACT = {
    'L4YAML.Proofs.Serialization.SerializationWellFormed.checkFrom_correct': {'propext'},
    'L4YAML.Proofs.Serialization.parse_iff_executable_language': ALLOWED,
}
PLACEHOLDER = re.compile(r"declaration uses [`']sorry[`']")
PROFILE = re.compile(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))", re.S)


def validate(log: str, probe: str, sites: set[str]) -> None:
    if 'sorryAx' not in probe or not PLACEHOLDER.search(probe):
        raise ValueError('Negative control must expose both Lean placeholder signals')
    if 'sorryAx' in log or PLACEHOLDER.search(log):
        raise ValueError('Proof placeholder in serialization build or axiom output')
    profiles = {}
    for name, axioms, _ in PROFILE.findall(log):
        profile = {x.strip() for x in axioms.split(',') if x.strip()}
        if profile - ALLOWED:
            raise ValueError(f'Unapproved axioms for {name}: {sorted(profile - ALLOWED)}')
        if name in profiles and profiles[name] != profile:
            raise ValueError(f'Conflicting profiles for {name}')
        profiles[name] = profile
    missing = sites - profiles.keys()
    if missing:
        raise ValueError(f'Missing axiom observations: {sorted(missing)}')
    for name, expected in EXACT.items():
        if profiles.get(name) != expected:
            raise ValueError(f'Exact axiom profile mismatch for {name}: {profiles.get(name)}')


if __name__ == '__main__':
    log, probe, site_file = map(Path, sys.argv[1:])
    sites = set(site_file.read_text().splitlines())
    try:
        validate(log.read_text(), probe.read_text(), sites)
    except ValueError as error:
        sys.exit(str(error))
    print(f'Serialization proof hygiene: {len(sites)} observed profiles; exact headline sets; no placeholders or reduction axioms')
