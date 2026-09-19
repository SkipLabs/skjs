"""Deliberately remove protocol defenses; the reference tests must detect each.

Runs isolated copies. No repository files are edited by this command.
"""
from __future__ import annotations
import json
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parent
MUTATIONS = (
    ("lost_failed_materialization", "model.py",
     '        self.require(Query("defined", source, BOTTOM))\n', ""),
    ("no_publication_replay", "model.py",
     '        for identity in self._obligations:\n            self._check(identity)\n', ""),
    ("rewound_snapshot_identity", "model.py",
     '        self._snapshot = replace(saved.snapshot, revision=next(_ids))\n',
     '        self._snapshot = saved.snapshot\n'),
    ("cache_drops_incoming_provenance", "projection.py",
     '                merged = tuple(dict.fromkeys(previous.prerequisites + entry.prerequisites))\n',
     '                merged = previous.prerequisites\n'),
    ("projection_forgets_equality", "projection.py",
     '        receipt = self.owner.require(q)\n',
     '        if op in ("projection", "indexed"):\n            q = request\n        receipt = self.owner.require(q)\n'),
)


def run() -> dict:
    results = []
    for name, filename, before, after in MUTATIONS:
        with TemporaryDirectory(prefix="skjs-lifetime-mutant-") as temp:
            work = Path(temp)
            for source in ROOT.glob("*.py"):
                shutil.copy2(source, work / source.name)
            path = work / filename
            text = path.read_text()
            if text.count(before) != 1:
                raise RuntimeError(f"{name}: mutation anchor is not unique")
            path.write_text(text.replace(before, after))
            proc = subprocess.run(
                [sys.executable, "-m", "unittest", "discover", "-v"],
                cwd=work, capture_output=True, text=True, timeout=30,
            )
            failures = [line for line in proc.stderr.splitlines()
                        if line.startswith(("FAIL:", "ERROR:"))]
            if proc.returncode == 0 or not failures or any(s.startswith("ERROR:") for s in failures):
                raise RuntimeError(f"{name}: expected assertion failure, got:\n{proc.stderr}")
            results.append({"mutation": name, "detected": True, "failures": failures})
    return {"mutants": results, "scope": "Python reference path, not native SKJS"}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
