#!/usr/bin/env python3
"""Benchmark one verifier against frozen source AST/claims; no SKJS export or build is timed."""
import argparse
import hashlib
import json
import pathlib
import platform
import statistics
import subprocess
import time

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--binary', required=True)
p.add_argument('--name', required=True)
p.add_argument('--ast', required=True)
p.add_argument('--claims', required=True)
p.add_argument('--file-key', required=True)
p.add_argument('--output-dir', required=True)
p.add_argument('--runs', type=int, default=5)
p.add_argument('--warmups', type=int, default=1)
p.add_argument('--timeout', type=float, default=60)
p.add_argument('--cases', nargs='+', default=['capturedRead', 'writingBody', 'callingBody',
                                            'blockReader', 'localBlock', 'all', 'bad-local-annotation'])
a = p.parse_args()
if a.runs < 1 or a.warmups < 0:
    p.error('runs must be positive and warmups nonnegative')
root = pathlib.Path(a.output_dir)
root.mkdir(parents=True, exist_ok=True)
binary = str(pathlib.Path(a.binary).resolve())
ast = json.loads(pathlib.Path(a.ast).read_text())
claims = json.loads(pathlib.Path(a.claims).read_text())
rows = []

def invoke(args, expected):
    start = time.perf_counter()
    r = subprocess.run([binary, *args], capture_output=True, timeout=a.timeout)
    elapsed = time.perf_counter() - start
    if r.returncode != expected:
        raise RuntimeError(f'{args[0]} exited {r.returncode}: {r.stdout!r} {r.stderr!r}')
    return elapsed

for case in a.cases:
    source = json.loads(json.dumps(ast))
    supplied = json.loads(json.dumps(claims))
    reject = case == 'bad-local-annotation'
    wanted = 'localBlock' if reject else case
    if case != 'all':
        source['functions'] = [f for f in source['functions'] if f['name'] == wanted]
        if len(source['functions']) != 1:
            raise ValueError(f'expected one source function named {wanted}')
        for file in supplied:
            file['functions'] = ([f for f in file['functions'] if f['name'] == wanted]
                                 if file['file'] == a.file_key else [])
    if reject:
        source['functions'][0]['body'][0]['init']['body']['body']['annot'] = {
            'top': False, 'atoms': [{'a': 'booleanlit', 'v': 'true'}]}
    ap, cp = root / f'{case}.ast', root / f'{case}.claims'
    ep = root / f'{a.name}-{case}.evidence'
    ap.write_text(json.dumps(source))
    cp.write_text(json.dumps(supplied))
    times, checks = [], []
    for i in range(a.warmups + a.runs):
        dt = invoke(['--produce-stateful-source', str(ap), str(cp), a.file_key, str(ep), '10'],
                    1 if reject else 0)
        if i >= a.warmups:
            times.append(dt)
        if not reject:
            dt = invoke(['--check-stateful-source', str(ap), str(cp), a.file_key, str(ep)], 0)
            if i >= a.warmups:
                checks.append(dt)
    row = {'case': case, 'produce_s': times, 'median_produce_s': statistics.median(times),
           'check_s': checks, 'median_check_s': statistics.median(checks) if checks else None,
           'evidence_bytes': ep.stat().st_size if not reject else None}
    rows.append(row)
    print(f'{case}: {row["median_produce_s"]:.6f}s', flush=True)

result = {'binary_sha256': hashlib.sha256(pathlib.Path(binary).read_bytes()).hexdigest(),
          'ast_sha256': hashlib.sha256(pathlib.Path(a.ast).read_bytes()).hexdigest(),
          'claims_sha256': hashlib.sha256(pathlib.Path(a.claims).read_bytes()).hexdigest(),
          'platform': platform.platform(), 'warmups': a.warmups, 'runs': a.runs, 'results': rows}
(root / f'{a.name}.json').write_text(json.dumps(result, indent=2) + '\n')
