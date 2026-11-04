#!/usr/bin/env python3
import argparse
import re
from pathlib import Path

DEFINE_RE = re.compile(r'^define\b')
DECLARE_RE = re.compile(r'^declare\b')


def split_toplevel_entries(lines):
    entries = []
    cur = []
    in_func = False
    i = 0
    while i < len(lines):
        line = lines[i]
        if not in_func:
            if DEFINE_RE.match(line):
                if cur:
                    entries.append(("other", cur))
                    cur = []
                in_func = True
                func_lines = [line]
                cur = func_lines
            else:
                cur.append(line)
        else:
            cur.append(line)
            # In LLVM IR, function definitions end with a top-level line `}`.
            if line.strip() == "}":
                entries.append(("func", cur))
                cur = []
                in_func = False
        i += 1
    if cur:
        entries.append(("other", cur))
    return entries


def func_name(func_lines):
    header = "".join(func_lines[:4])  # name should be near the start
    m = re.search(r'@([^(\s]+)\(', header)
    if not m:
        raise RuntimeError("Could not parse function name from header start")
    return m.group(1)


def func_declare(func_lines):
    # Convert define header to declare by copying lines up to the opening '{'.
    header = []
    for line in func_lines:
        header.append(line)
        if '{' in line:
            break
    text = ''.join(header)
    text = re.sub(r'^define\b', 'declare', text, count=1)
    # Remove the function body opener (the last '{' in the gathered header),
    # not any '{' that may appear in a struct return type.
    if '{' in text:
      before, after = text.rsplit('{', 1)
      text = before + after
    # Function declarations cannot carry function-level debug attachments.
    text = re.sub(r'(?:, )?!dbg ![0-9]+', '', text)
    # Some clauses valid on function definitions are rejected on declarations.
    text = re.sub(r'\s+personality\s+[^!\n]+', '', text)
    text = re.sub(r'\s+gc\s+"[^"]+"', '', text)
    # Normalize trailing whitespace before newline.
    text = re.sub(r'[ \t]+\n', '\n', text)
    if not text.endswith('\n'):
        text += '\n'
    return text


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('input')
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--shards', type=int, default=8)
    args = ap.parse_args()

    src = Path(args.input)
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    lines = src.read_text(encoding='utf-8', errors='surrogateescape').splitlines(True)
    entries = split_toplevel_entries(lines)
    funcs = []
    others = []
    for kind, ent in entries:
        if kind == 'func':
            funcs.append(ent)
        else:
            others.append(ent)

    decls = {}
    for f in funcs:
        decls[func_name(f)] = func_declare(f)

    # Deterministic partition by function order in file (round-robin).
    buckets = [[] for _ in range(args.shards)]
    for idx, f in enumerate(funcs):
        buckets[idx % args.shards].append(f)

    # Flatten 'other' entries once; this includes target triple, declarations, globals,
    # attributes, metadata, etc. We keep it in every shard for compile-only benchmarking.
    other_text = ''.join(''.join(ent) for ent in others)

    for i, bucket in enumerate(buckets):
        bucket_names = {func_name(f) for f in bucket}
        p = out_dir / f'shard_{i:02d}.ll'
        with p.open('w', encoding='utf-8', errors='surrogateescape') as g:
            g.write(other_text)
            g.write('\n; --- synthesized declarations for omitted function definitions ---\n')
            for name in decls:
                if name not in bucket_names:
                    g.write(decls[name])
            g.write('\n; --- function definitions for this shard ---\n')
            for f in bucket:
                g.write(''.join(f))
        print(f'{p} functions={len(bucket)}')

    print(f'total_functions={len(funcs)} shards={args.shards}')

if __name__ == '__main__':
    main()
