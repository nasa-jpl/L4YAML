#!/usr/bin/env python3
"""Unified YAML-processor scorer over the yaml-test-suite *data* form.

Runs each processor's `-event` / `-json` tester (reading YAML on stdin) over
every test and scores it exactly the way http://matrix.yaml.info does:

  * error tests (dir has an `error` file): correct iff the parser errors (rc!=0)
  * valid  tests (event axis): correct iff emitted events == test.event
  * valid  tests (json  axis): correct iff emitted JSON == in.json (structural)

All processors — L4YAML's native binary and every docker tester — go through the
identical code path, so the numbers are apples-to-apples.
"""
import os, sys, glob, json, argparse, subprocess
from concurrent.futures import ThreadPoolExecutor

def leaf_dirs(data):
    # `tags/` and `name/` are symlink index dirs in the data branch — skip them
    return sorted(os.path.dirname(p) for p in glob.glob(data + '/**/in.yaml', recursive=True)
                  if '/tags/' not in p and '/name/' not in p)

# ---- event normalization -----------------------------------------------------
def norm_events(text):
    lines = [l.rstrip('\r') for l in text.split('\n')]
    while lines and lines[-1] == '':
        lines.pop()
    return lines

# ---- json normalization (handles concatenated multi-document streams) --------
def parse_json_stream(text):
    dec = json.JSONDecoder()
    vals, i, n = [], 0, len(text)
    while i < n:
        while i < n and text[i] in ' \t\r\n':
            i += 1
        if i >= n:
            break
        obj, end = dec.raw_decode(text, i)
        vals.append(obj)
        i = end
    return vals

def run(cmd, stdin_bytes, timeout):
    try:
        p = subprocess.run(cmd, input=stdin_bytes,
                           stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                           timeout=timeout)
        return p.returncode, p.stdout
    except subprocess.TimeoutExpired:
        return 124, b''
    except Exception:
        return 125, b''

def score_one(cmd, d, axis, timeout):
    """Return (category, testid). category in the axis vocabulary."""
    parts = d.rstrip('/').split(os.sep)
    tid = '/'.join(parts[-2:]) if parts[-1].isdigit() else parts[-1]
    inp = open(d + '/in.yaml', 'rb').read()
    is_err = os.path.exists(d + '/error')
    if axis == 'event':
        rc, out = run(cmd, inp, timeout)
        if is_err:
            return ('err-ok' if rc != 0 else 'err-miss', tid)
        if rc == 124:
            return ('timeout', tid)
        if rc != 0:
            return ('reject', tid)
        exp = open(d + '/test.event', encoding='utf-8').read()
        got = out.decode('utf-8', 'replace')
        return ('pass' if norm_events(got) == norm_events(exp) else 'diff', tid)
    else:  # json
        if not os.path.exists(d + '/in.json'):
            return ('skip', tid)   # no json oracle for this test
        rc, out = run(cmd, inp, timeout)
        if is_err:
            # a few error tests carry a stale in.json (9MQT/01, DK95/01,
            # DK95/06); correct behavior is still to reject the input
            return ('err-ok' if rc != 0 else 'err-miss', tid)
        if rc == 124:
            return ('timeout', tid)
        if rc != 0:
            return ('reject', tid)
        try:
            exp = parse_json_stream(open(d + '/in.json', encoding='utf-8').read())
            got = parse_json_stream(out.decode('utf-8', 'replace'))
        except Exception:
            return ('diff', tid)
        return ('pass' if got == exp else 'diff', tid)

def score(cmd, dirs, axis, timeout, workers):
    cats = {}
    fails = []
    def work(d):
        return score_one(cmd, d, axis, timeout)
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for cat, tid in ex.map(work, dirs):
            cats[cat] = cats.get(cat, 0) + 1
            if cat in ('diff', 'reject', 'err-miss', 'timeout'):
                fails.append((cat, tid))
    return cats, fails

# processor -> (event tester name or None, json tester name or None)
DOCKER = {
    'c-libfyaml':        ('c-libfyaml-event',        'c-libfyaml-json'),
    'c-libyaml':         ('c-libyaml-event',          None),
    'cpp-yamlcpp':       ('cpp-yamlcpp-event',        None),
    'dotnet-yamldotnet': ('dotnet-yamldotnet-event', 'dotnet-yamldotnet-json'),
    'hs-hsyaml':         ('hs-hsyaml-event',         'hs-hsyaml-json'),
    'java-snakeyaml':    ('java-snakeyaml-event',    'java-snakeyaml-json'),
    'js-jsyaml':         (None,                      'js-jsyaml-json'),
    'js-yaml':           ('js-yaml-event',           'js-yaml-json'),
    'lua-lyaml':         (None,                      'lua-lyaml-json'),
    'nim-nimyaml':       ('nim-nimyaml-event',        None),
    'perl-pp':           ('perl-pp-event',           'perl-pp-json'),
    'perl-pplibyaml':    ('perl-pplibyaml-event',    'perl-pplibyaml-json'),
    'perl-refparser':    ('perl-refparser-event',     None),
    'perl-syck':         (None,                      'perl-syck-json'),
    'perl-tiny':         (None,                      'perl-tiny-json'),
    'perl-xs':           (None,                      'perl-xs-json'),
    'perl-yaml':         (None,                      'perl-yaml-json'),
    'py-pyyaml':         ('py-pyyaml-event',         'py-pyyaml-json'),
    'py-ruamel':         ('py-ruamel-event',         'py-ruamel-json'),
    'ruby-psych':        (None,                      'ruby-psych-json'),
    'raku-yamlish':      (None,                      'raku-yamlish-json'),
}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--data', required=True)
    ap.add_argument('--container', default='yamlall')
    ap.add_argument('--axis', choices=['event', 'json', 'both'], default='both')
    ap.add_argument('--timeout', type=float, default=5.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--l4yaml-event', default=None)
    ap.add_argument('--l4yaml-json', default=None)
    ap.add_argument('--only', default=None, help='comma-separated processor ids')
    ap.add_argument('--out', default=None)
    args = ap.parse_args()

    dirs = leaf_dirs(args.data)
    print(f"# {len(dirs)} leaf tests in data form", file=sys.stderr)

    # Build processor -> {axis: cmd}
    procs = {}
    for pid, (ev, js) in DOCKER.items():
        procs[pid] = {}
        if ev: procs[pid]['event'] = ['docker', 'exec', '-i', args.container, ev]
        if js: procs[pid]['json']  = ['docker', 'exec', '-i', args.container, js]
    procs['L4YAML'] = {}
    if args.l4yaml_event: procs['L4YAML']['event'] = [args.l4yaml_event]
    if args.l4yaml_json:  procs['L4YAML']['json']  = [args.l4yaml_json]

    only = set(args.only.split(',')) if args.only else None
    axes = ['event', 'json'] if args.axis == 'both' else [args.axis]

    results = {}
    for pid in sorted(procs):
        if only and pid not in only:
            continue
        results[pid] = {}
        for axis in axes:
            if axis not in procs[pid]:
                continue
            cats, fails = score(procs[pid][axis], dirs, axis, args.timeout, args.workers)
            results[pid][axis] = {'cats': cats, 'fails': fails}
            correct = cats.get('pass', 0) + cats.get('err-ok', 0)
            total = sum(v for k, v in cats.items() if k != 'skip')
            print(f"{pid:20s} {axis:5s}  correct={correct:3d}/{total:3d}  "
                  f"{dict(sorted(cats.items()))}", file=sys.stderr)

    if args.out:
        json.dump(results, open(args.out, 'w'), indent=1)
        print(f"# wrote {args.out}", file=sys.stderr)

if __name__ == '__main__':
    main()
