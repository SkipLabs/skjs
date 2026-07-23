#!/usr/bin/env bash
#
# try-project.sh — run SKJS over one external TypeScript project and report how
# much of it type-checks.
#
# Usage:
#   scripts/try-project.sh <name> <git-url> [ref] [src-subdir]
#
#   <name>        short id for the project (used for the clone + report paths)
#   <git-url>     repository to clone
#   [ref]         tag / branch / commit to pin (default: the repo default branch)
#   [src-subdir]  directory within the repo to scan (default: the whole repo)
#
# Environment:
#   SKJS_BIN    path to the skjs binary   (default: <repo>/target/host/dev/skjs)
#   STUBS       import-stubs directory    (default: <repo>/import-stubs)
#   WORKDIR     scratch dir for clones + reports (default: <repo>/.project-survey)
#   KEEP_CLONE  if non-empty, reuse an existing clone instead of re-cloning
#
# It writes a machine-readable summary to $WORKDIR/reports/<name>.json and prints
# a human report. A project that fails to type-check is a *result*, not a script
# error, so this exits 0 in that case; it exits non-zero only on bad usage or a
# clone/setup failure.

set -u -o pipefail

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SKJS_BIN="${SKJS_BIN:-${PROJECT_ROOT}/target/host/dev/skjs}"
STUBS="${STUBS:-${PROJECT_ROOT}/import-stubs}"
WORKDIR="${WORKDIR:-${PROJECT_ROOT}/.project-survey}"

die() {
  echo "try-project: $*" >&2
  exit 2
}

[[ $# -ge 2 ]] || die "usage: try-project.sh <name> <git-url> [ref] [src-subdir]"
name="$1"
url="$2"
ref="${3:-}"
src="${4:-.}"

[[ -x "$SKJS_BIN" ]] || die "skjs binary not found or not executable: $SKJS_BIN (build it, or set SKJS_BIN)"
[[ -d "$STUBS" ]] || die "import-stubs dir not found: $STUBS (set STUBS)"

repo="${WORKDIR}/repos/${name}"
reports="${WORKDIR}/reports"
mkdir -p "$reports"

# --- clone (or reuse) -------------------------------------------------------
if [[ -n "${KEEP_CLONE:-}" && -d "${repo}/.git" ]]; then
  echo "try-project: reusing existing clone at ${repo}" >&2
else
  rm -rf "$repo"
  mkdir -p "$(dirname "$repo")"
  if [[ -n "$ref" ]]; then
    # Try a shallow clone of the exact ref (tag or branch) first; fall back to a
    # full clone + checkout for a bare commit SHA.
    if ! git clone --quiet --depth 1 --branch "$ref" "$url" "$repo" 2>/dev/null; then
      git clone --quiet "$url" "$repo" || die "clone failed: $url"
      git -C "$repo" checkout --quiet "$ref" || die "ref not found: $ref"
    fi
  else
    git clone --quiet --depth 1 "$url" "$repo" || die "clone failed: $url"
  fi
fi
sha="$(git -C "$repo" rev-parse --short HEAD 2>/dev/null || echo unknown)"

# --- collect source files ---------------------------------------------------
[[ -d "${repo}/${src}" ]] || die "src-subdir does not exist in the repo: ${src}"
mapfile -t files < <(
  cd "$repo" && find "$src" -type f -name '*.ts' \
    ! -name '*.d.ts' ! -name '*.test.ts' ! -name '*.spec.ts' \
    -not -path '*/node_modules/*' -not -path '*/dist/*' -not -path '*/build/*' \
    -not -path '*/out/*' -not -path '*/coverage/*' -not -path '*/.git/*' \
    | sort
)
nfiles="${#files[@]}"

if [[ "$nfiles" -eq 0 ]]; then
  echo "try-project: no .ts source files found under ${name}/${src}" >&2
fi

loc=0
if [[ "$nfiles" -gt 0 ]]; then
  loc="$( (cd "$repo" && cat "${files[@]}") 2>/dev/null | wc -l | tr -d ' ')"
fi

# --- run skjs ---------------------------------------------------------------
errjson="${reports}/${name}.err.json"
skjs_exit=0
if [[ "$nfiles" -gt 0 ]]; then
  ( cd "$repo" && "$SKJS_BIN" check --import-stubs "$STUBS" --error-format json \
      --keep-going "${files[@]}" ) >/dev/null 2>"$errjson" || skjs_exit=$?
else
  : >"$errjson"
fi

# --- aggregate + report -----------------------------------------------------
summary="${reports}/${name}.json"
NAME="$name" URL="$url" REF="${ref:-<default>}" SHA="$sha" \
NFILES="$nfiles" LOC="$loc" SKJS_EXIT="$skjs_exit" SUMMARY="$summary" \
python3 - "$errjson" <<'PY'
import json, os, sys, collections

errjson = sys.argv[1]
name = os.environ["NAME"]
nfiles = int(os.environ["NFILES"])
loc = int(os.environ["LOC"])
skjs_exit = int(os.environ["SKJS_EXIT"])

raw = ""
try:
    with open(errjson) as fh:
        raw = fh.read().strip()
except FileNotFoundError:
    pass

# stderr mixes plain-text warnings, then a JSON array of error groups, then (on
# an abort) a trailing invariant-violation message. Pull the array out of it.
groups = []
leftover = raw
start = raw.find("[")
if start >= 0:
    try:
        data, end = json.JSONDecoder().raw_decode(raw[start:])
        if isinstance(data, list):
            groups = [g for g in data if isinstance(g, list) and g]
        leftover = (raw[:start] + raw[start + end:]).strip()
    except ValueError:
        leftover = raw
warnings = sum(1 for ln in leftover.splitlines() if " warning:" in ln)

def categorize(msg):
    m = msg.lower()
    if ("cannot find module" in m or "could not find module" in m
            or "cannot find file" in m or "type declarations" in m
            or "cannot find type" in m or "cannot find name" in m):
        return "resolution"  # missing stub / path alias / declaration — often not a language gap
    if "not supported" in m or "not yet supported" in m or "not implemented" in m:
        return "feature"     # a genuine SKJS subset gap
    return "type"            # a type-level rejection

by_file = collections.Counter()
by_msg = collections.Counter()
by_cat = collections.Counter()
for g in groups:
    primary = g[0]
    msg = primary.get("message", "?")
    by_file[primary.get("pos", {}).get("file", "?")] += 1
    by_msg[msg] += 1
    by_cat[categorize(msg)] += 1

errors = len(groups)
error_files = len(by_file)
clean_files = max(0, nfiles - error_files)
clean_pct = (100.0 * clean_files / nfiles) if nfiles else 0.0
err_per_kloc = (1000.0 * errors / loc) if loc else 0.0

# An invariant-violation / internal-error in the leftover text, or an unexpected
# exit code, means skjs aborted rather than reporting diagnostics.
low = leftover.lower()
crashed = any(mk in low for mk in
              ("invariant violation", "no value for keys", "internal error")) \
    or (skjs_exit not in (0, 2))
crash_reason = ""
if crashed:
    crash_reason = next((ln for ln in leftover.splitlines()
                         if ln.strip() and " warning:" not in ln), "")[:200]
    clean_files = error_files = errors = 0
    clean_pct = err_per_kloc = 0.0

# Status label from the share of files that check clean.
if crashed:
    status = "crash"
elif nfiles == 0:
    status = "no-ts"
elif clean_pct >= 90:
    status = "good"
elif clean_pct >= 60:
    status = "partial"
elif clean_pct >= 20:
    status = "weak"
else:
    status = "unsupported"

top = by_msg.most_common(8)
summary = {
    "name": name,
    "url": os.environ["URL"],
    "ref": os.environ["REF"],
    "sha": os.environ["SHA"],
    "files": nfiles,
    "loc": loc,
    "clean_files": clean_files,
    "error_files": error_files,
    "clean_pct": round(clean_pct, 1),
    "errors": errors,
    "err_per_kloc": round(err_per_kloc, 2),
    "by_category": {"feature": by_cat["feature"], "type": by_cat["type"],
                    "resolution": by_cat["resolution"]},
    "skjs_exit": skjs_exit,
    "warnings": warnings,
    "crashed": crashed,
    "crash_reason": crash_reason,
    "status": status,
    "top_errors": [[m, c] for m, c in top],
}
with open(os.environ["SUMMARY"], "w") as fh:
    json.dump(summary, fh, indent=2)

# Human report.
print(f"\n=== {name} ({os.environ['REF']} @ {os.environ['SHA']}) — {status} ===")
if crashed:
    print(f"  files: {nfiles} ({loc} loc)")
    print(f"  CRASHED: {crash_reason}")
    raise SystemExit
print(f"  files: {nfiles}   clean: {clean_files} ({clean_pct:.0f}%)   "
      f"errors: {errors} ({err_per_kloc:.1f}/kloc, {loc} loc)")
print(f"  by category: {by_cat['feature']} feature-gap, {by_cat['type']} type, "
      f"{by_cat['resolution']} resolution (resolution = missing stub/path alias, often fixable)")
if top:
    print("  top errors:")
    for m, c in top:
        m1 = (m[:90] + "…") if len(m) > 90 else m
        print(f"    {c:>4}x  {m1}")
PY
