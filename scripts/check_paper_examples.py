#!/usr/bin/env python3
"""Extract TypeScript examples from docs/skjs_type_system.tex and type-check them with skjs.

Examples can mark expected failures by adding `// EXPECT-ERROR: <diagnostic substring>`
comment lines inside the listing. Each listed substring must appear in skjs's output.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import List, Optional, Sequence

SUPPORTED_LANGS = {
    "TypeScript": ".ts",
    "JavaScript": ".ts",
}

EXPECT_PREFIX = "// EXPECT-ERROR:"

LISTING_RE = re.compile(
    r"\\begin\{lstlisting\}(?:\[language=(?P<lang>[^\]]+)\])?\s*(?P<body>.*?)\\end\{lstlisting\}",
    re.DOTALL,
)


@dataclass
class Example:
    index: int
    language: str
    code: str
    expected_errors: List[str]

def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--tex",
        default="docs/skjs_type_system.tex",
        type=Path,
        help="Path to the LaTeX source containing examples (default: %(default)s)",
    )
    parser.add_argument(
        "--skjs",
        type=Path,
        default=None,
        help="Path to the skjs binary; if omitted we try common locations and PATH",
    )
    parser.add_argument(
        "--import-stubs",
        type=Path,
        default=Path("import-stubs"),
        help="Path to the import stubs directory passed to skjs (default: %(default)s)",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print commands as they are executed",
    )
    return parser.parse_args(argv)


def load_examples(tex_path: Path) -> List[Example]:
    text = tex_path.read_text()
    examples: List[Example] = []
    for idx, match in enumerate(LISTING_RE.finditer(text), start=1):
        language = (match.group("lang") or "").strip()
        body = match.group("body")
        if language not in SUPPORTED_LANGS:
            continue
        lines = body.splitlines()
        expected_errors: List[str] = []
        kept_lines: List[str] = []
        for line in lines:
            stripped = line.lstrip()
            if stripped.startswith(EXPECT_PREFIX):
                expected_errors.append(stripped[len(EXPECT_PREFIX) :].strip())
                continue
            kept_lines.append(line)
        code = "\n".join(kept_lines).strip("\n")
        if code:
            code += "\n"
        examples.append(
            Example(index=idx, language=language, code=code, expected_errors=expected_errors)
        )
    return examples


def resolve_skjs(path_arg: Optional[Path]) -> Path:
    candidates: List[Path] = []
    if path_arg is not None:
        candidates.append(path_arg)
    else:
        repo_root = Path(__file__).resolve().parents[1]
        candidates.extend(
            [
                repo_root / "skjs",
                repo_root / "target" / "host" / "dev" / "skjs",
                repo_root / "target" / "host" / "release" / "skjs",
            ]
        )
        from shutil import which

        system_path = which("skjs")
        if system_path:
            candidates.append(Path(system_path))
    for candidate in candidates:
        if candidate and candidate.exists() and candidate.is_file():
            return candidate
    raise FileNotFoundError(
        "Could not find skjs binary. Pass --skjs or build with `skargo build`."
    )


def run_example(
    skjs: Path,
    example: Example,
    directory: Path,
    cwd: Path,
    import_stubs: Path,
    verbose: bool,
) -> subprocess.CompletedProcess:
    suffix = SUPPORTED_LANGS[example.language]
    file_path = directory / f"example_{example.index:02d}{suffix}"
    file_path.write_text(example.code)
    cmd = [
        str(skjs),
        "check",
        "--import-stubs",
        str(import_stubs),
        str(file_path),
    ]
    if verbose:
        print("+", " ".join(cmd))
    proc = subprocess.run(cmd, capture_output=True, text=True, cwd=cwd)
    return proc


def evaluate_result(example: Example, proc: subprocess.CompletedProcess) -> List[str]:
    combined = (proc.stdout or "") + (proc.stderr or "")
    failure_msgs: List[str] = []
    if example.expected_errors:
        if proc.returncode == 0:
            failure_msgs.append("Expected failure but command succeeded")
        for msg in example.expected_errors:
            if msg and msg not in combined:
                failure_msgs.append(f"Missing expected diagnostic: {msg}")
    else:
        if proc.returncode != 0:
            failure_msgs.append("Unexpected failure")
    return failure_msgs


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    tex_path: Path = args.tex
    if not tex_path.exists():
        print(f"error: {tex_path} does not exist", file=sys.stderr)
        return 1
    examples = load_examples(tex_path)
    if not examples:
        print("No supported examples found.")
        return 0
    try:
        skjs = resolve_skjs(args.skjs)
    except FileNotFoundError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    repo_root = Path(__file__).resolve().parents[1]
    import_stubs_path = args.import_stubs
    if not import_stubs_path.is_absolute():
        import_stubs_path = (repo_root / import_stubs_path).resolve()
    if not import_stubs_path.exists():
        print(f"error: import stubs directory {import_stubs_path} not found", file=sys.stderr)
        return 1
    failures = []
    with TemporaryDirectory() as tmpdir_str:
        tmpdir = Path(tmpdir_str)
        # We run skjs from repo root but store files in tmpdir.
        for example in examples:
            proc = run_example(
                skjs,
                example,
                tmpdir,
                repo_root,
                import_stubs_path,
                args.verbose,
            )
            failure_msgs = evaluate_result(example, proc)
            if failure_msgs:
                failures.append((example, failure_msgs, proc))
                combined = (proc.stdout or "") + (proc.stderr or "")
                print(
                    f"Example #{example.index} ({example.language}) issues:\n"
                    + "\n".join(f"  - {msg}" for msg in failure_msgs)
                    + "\n"
                    + combined,
                    file=sys.stderr,
                )
    total = len(examples)
    passed = total - len(failures)
    print(f"Checked {total} example(s): {passed} passed, {len(failures)} failed.")
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
