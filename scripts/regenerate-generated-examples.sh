#!/usr/bin/env bash
#
# regenerate-generated-examples.sh
#
# Autonomously regenerate skjs's generated-examples/ corpus from the skipper
# code generator, so the committed examples are *exactly what the generator
# emits* (no hand-edits — that was the whole point of the corpus).
#
# The set of services is DISCOVERED from the skipper repo (its tracked
# benchs/<slug>/prompt.md files); nothing is hardcoded here. Each regenerated
# example is keyed by its skipper bench slug (e.g. `counter`, `blog-post`).
#
# What it does, per selected bench:
#   1. reads the prompt at $SKIPPER_DIR/benchs/<slug>/prompt.md,
#   2. runs the skipper generator on it (`bun run generate`),
#   3. syncs the generated output into generated-examples/<slug>/ VERBATIM
#      (it never edits file contents — it only selects which generated files to
#      keep; see SYNC_MODE below),
#   4. optionally type-checks the result with skjs and prints a summary.
#
# It is idempotent and safe to re-run. The full untouched generator output for
# every bench is kept under the staging dir for inspection.
#
# ---------------------------------------------------------------------------
# REQUIREMENTS (you provide these in the environment / on disk):
#   - SKIPPER_API_KEY   : required. The generator routes all model calls through
#                         the skipper backend, which needs this key. Obtain one
#                         at https://www.skipper.skiplabs.io. (Generation is
#                         AI-driven and BILLED — each run costs credits.)
#   - bun               : on PATH (to run the generator from source).
#   - a skipper checkout at $SKIPPER_DIR on the json-index-sig branch (the
#     generator CODE must be that revision; the published skiplabs/skipper image
#     is built from main and lacks it).
#   - for verification only: a built skjs binary at target/host/dev/skjs. If your
#     build/run must happen inside a container, set RUNNER to your wrapper (below).
#
# NOTE ON DETERMINISM: generation is AI-driven, so a run produces a *fresh*
# corpus — it will NOT byte-match the previous examples, and re-running yields
# different code. That is expected. The contract is "genuine generator output
# that skjs accepts", not reproduction of specific files.
# ---------------------------------------------------------------------------
#
# USAGE:
#   scripts/regenerate-generated-examples.sh [slug ...]
#
#   With no args, regenerates skipper's canonical ORIGINAL_EXPERIMENTS set (the
#   same list benchs/run-evals.sh --original uses). With args, only
#   those slugs (each must exist as benchs/<slug>/prompt.md in skipper), e.g.
#   `... counter todo-list blog-post`. List what would run with DRY_RUN=1.
#
# KNOBS (environment variables; defaults in []):
#   SKIPPER_DIR    [~/work/skipper]      skipper checkout
#   SKIPPER_BRANCH [json-index-sig]      branch the generator must be on
#   SKIPPER_MODE   [staging]             AI backend: prod|staging|local
#   INCLUDE_ALL    [0]                   regenerate EVERY discovered bench,
#                                        including -simple/-inmemory/-eventsourced
#                                        variants, nested groups (externals/*),
#                                        and bad-prompt. By default the selection
#                                        is skipper's canonical ORIGINAL_EXPERIMENTS
#                                        set, read from benchs/run-evals.sh (the
#                                        same list its --original uses); if that
#                                        file is unreadable it falls back to the
#                                        discovered top-level base benches.
#   EVAL_ENV_FILE  [$SKIPPER_DIR/.env.$SKIPPER_MODE]
#                                        per-backend env file sourced for
#                                        SKIPPER_API_KEY (matches run-evals.sh).
#                                        Sourced if present; shell SKIPPER_API_KEY
#                                        still works when the file is absent.
#   SYNC_MODE      [service]             which generated files to commit:
#                    service : the import-closure of src/service.ts only
#                              (service.ts, ServiceGraph.ts, resources/*,
#                              mappers/*, reducers/*, types.ts, and the runtime-
#                              helper declarations they import, helpers/*.d.ts)
#                              + package.json + tsconfig.json. This is the
#                              type-surface the generator itself skjs-checks; it
#                              imports only @skipruntime/core (+ subpaths) and
#                              relative files, which skjs resolves via
#                              --import-stubs. Recommended. (Checking the helper-
#                              importing mappers also needs @skipruntime/core/json
#                              and /std stubs in import-stubs/ — see plan.)
#                    full    : the entire generated project minus build/dep
#                              artifacts (node_modules, packs, .cache, dist).
#                              Faithful but includes index.ts/api.ts/etc. which
#                              import @skipruntime/wasm and ../helpers — these
#                              will NOT type-check under skjs unless you add a
#                              @skipruntime/wasm stub to import-stubs/.
#                    none    : generate into staging only; do not touch the repo.
#   STAGING_DIR    [$SKJS_DIR/.regen-staging]  full generator output per bench
#   PRUNE          [0]                   on a FULL run (no slug args), delete any
#                                        generated-examples/<dir> not in the
#                                        selection (except skipruntime/), so the
#                                        corpus exactly mirrors skipper's benches.
#                                        Removes both the one-time verbose->slug
#                                        rename leftovers and orphans from benches
#                                        deleted/renamed upstream. Never prunes on
#                                        a partial (explicit-slug) run. With PRUNE=0
#                                        the stale dirs are only reported.
#   VERIFY         [1]                   run skjs check after syncing (needs a
#                                        built skjs; see RUNNER)
#   RUNNER         []                    command prefix for the skjs build/check
#                                        steps, e.g. a wrapper that runs them in
#                                        your build container. Empty = run
#                                        target/host/dev/skjs and `make` directly.
#   GEN_SKJS       [0]                   pass --skjs to the generator (needs the
#                                        skjs binary on PATH during generation)
#   JOBS           [1]                   size of the rolling generation pool —
#                                        up to JOBS benches generate concurrently,
#                                        and a finished one is immediately
#                                        replaced by the next queued bench (raise
#                                        with care: each costs credits and hits
#                                        the backend)
#   DRY_RUN        [0]                   print actions, change nothing
#
set -euo pipefail

# Requires bash 4.3+ (mapfile / associative arrays / `wait -n` for the rolling
# job pool). macOS ships 3.2 as /bin/bash; install a newer one (`brew install
# bash`) and run via that, e.g.
# `/opt/homebrew/bin/bash scripts/regenerate-generated-examples.sh`.
if [ "${BASH_VERSINFO[0]:-0}" -lt 4 ] ||
  { [ "${BASH_VERSINFO[0]:-0}" -eq 4 ] && [ "${BASH_VERSINFO[1]:-0}" -lt 3 ]; }; then
  echo "ERROR: this script needs bash >= 4.3 (you have ${BASH_VERSION:-unknown})." >&2
  echo "       Install one (brew install bash) and re-run with it." >&2
  exit 1
fi

# ---------------------------------------------------------------------------
# Resolve paths / config
# ---------------------------------------------------------------------------
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SKJS_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

SKIPPER_DIR="${SKIPPER_DIR:-$HOME/work/skipper}"
SKIPPER_BIN_DIR="$SKIPPER_DIR/skipper-bin"
SKIPPER_BRANCH="${SKIPPER_BRANCH:-json-index-sig}"
SKIPPER_MODE="${SKIPPER_MODE:-staging}"
INCLUDE_ALL="${INCLUDE_ALL:-0}"
SYNC_MODE="${SYNC_MODE:-service}"
PRUNE="${PRUNE:-0}"
STAGING_DIR="${STAGING_DIR:-$SKJS_DIR/.regen-staging}"
VERIFY="${VERIFY:-1}"
RUNNER="${RUNNER:-}"
GEN_SKJS="${GEN_SKJS:-0}"
JOBS="${JOBS:-1}"
DRY_RUN="${DRY_RUN:-0}"

EXAMPLES_DIR="$SKJS_DIR/generated-examples"
BENCHS_DIR="$SKIPPER_DIR/benchs"
RUN_EVALS="$BENCHS_DIR/run-evals.sh"

# Source skipper's per-backend env file (default tracks SKIPPER_MODE), the same
# way benchs/run-evals.sh does, so SKIPPER_API_KEY can live there rather than in
# the shell. Sourced unconditionally if present (file values win), matching
# run-evals.sh; harmless when absent.
EVAL_ENV_FILE="${EVAL_ENV_FILE:-$SKIPPER_DIR/.env.$SKIPPER_MODE}"
if [ -f "$EVAL_ENV_FILE" ]; then
  set -a
  # shellcheck disable=SC1090
  . "$EVAL_ENV_FILE"
  set +a
fi

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
log()  { printf '\033[1;34m[regen]\033[0m %s\n' "$*" >&2; }
warn() { printf '\033[1;33m[regen] WARN:\033[0m %s\n' "$*" >&2; }
err()  { printf '\033[1;31m[regen] ERROR:\033[0m %s\n' "$*" >&2; }

# Map a (possibly nested) bench slug to a filesystem-safe example dir name.
dirname_of() { printf '%s' "${1//\//-}"; }

# Collapse . and .. segments in a slash path (pure shell; path need not exist).
normalize_rel() {
  local p="$1" seg out=()
  local IFS='/'
  read -ra _segs <<< "$p"
  for seg in "${_segs[@]}"; do
    case "$seg" in
      ''|.) ;;
      ..) [ ${#out[@]} -gt 0 ] && unset 'out[${#out[@]}-1]' ;;
      *) out+=("$seg") ;;
    esac
  done
  printf '%s' "${out[*]}"
}

# Print, one per line, the project-relative files reachable from src/service.ts
# via relative imports (./ ../). This is the skjs type-surface: it stays within
# @skipruntime/core (+ subpaths, resolved via --import-stubs) and relative files.
# It DOES reach the runtime-helper type declarations (../helpers/index.d.ts) that
# generated mappers/reducers import, but never the @skipruntime/wasm runtime
# wiring (index.ts, api.ts, routes.ts, …). A `.js` import resolves to its `.ts`
# source, or — when no `.ts` exists — its `.d.ts` declaration (the helpers ship
# as `.d.ts` + `.js`, with no `.ts`).
service_closure() {
  local root="$1"
  [ -f "$root/src/service.ts" ] || return 1
  declare -A seen=()
  local queue=("src/service.ts") rel abs dir imp resolved base
  while [ ${#queue[@]} -gt 0 ]; do
    rel="${queue[0]}"; queue=("${queue[@]:1}")
    [ -n "${seen[$rel]:-}" ] && continue
    abs="$root/$rel"
    [ -f "$abs" ] || continue
    seen[$rel]=1
    printf '%s\n' "$rel"
    dir="$(dirname "$rel")"
    while IFS= read -r imp; do
      case "$imp" in
        ./*|../*) ;;
        *) continue ;;
      esac
      resolved="$(normalize_rel "$dir/$imp")"
      base="${resolved%.js}"
      # Prefer the .ts source; fall back to a .d.ts declaration (helpers).
      # A path with neither is enqueued as .ts and skipped at dequeue.
      if [ -f "$root/$base.ts" ]; then
        queue+=("$base.ts")
      elif [ -f "$root/$base.d.ts" ]; then
        queue+=("$base.d.ts")
      else
        queue+=("$base.ts")
      fi
    done < <(grep -hoE 'from "[^"]+"' "$abs" 2>/dev/null | sed -E 's/from "([^"]+)"/\1/')
  done
}

# Discover every bench slug from the skipper repo (tracked prompt.md files).
discover_slugs() {
  if [ -d "$SKIPPER_DIR/.git" ]; then
    git -C "$SKIPPER_DIR" ls-files 'benchs/**/prompt.md'
  else
    ( cd "$SKIPPER_DIR" && find benchs -name prompt.md )
  fi | sed -E 's#^benchs/##; s#/prompt\.md$##' | sort -u
}

# skipper's canonical corpus list, parsed from the ORIGINAL_EXPERIMENTS="..."
# heredoc-style assignment in benchs/run-evals.sh (single source of truth — not
# duplicated here).
original_slugs() {
  [ -f "$RUN_EVALS" ] || return 1
  awk '/^ORIGINAL_EXPERIMENTS="/{f=1;next} f && /^"/{f=0} f && NF {print $1}' "$RUN_EVALS"
}

# The selected slugs: all discovered (INCLUDE_ALL=1), else skipper's canonical
# ORIGINAL_EXPERIMENTS set, else (if that list is unreadable) the discovered
# top-level base benches (drop variant suffixes, nested groups, bad-prompt).
select_slugs() {
  if [ "$INCLUDE_ALL" = 1 ]; then
    discover_slugs
    return
  fi
  local orig; orig="$(original_slugs || true)"
  if [ -n "$orig" ]; then
    printf '%s\n' "$orig"
  else
    warn "could not read ORIGINAL_EXPERIMENTS from $RUN_EVALS; using discovered base benches."
    discover_slugs \
      | grep -vE -- '-(simple|inmemory|eventsourced)$' \
      | grep -v '/' \
      | grep -vx 'bad-prompt'
  fi
}

# ---------------------------------------------------------------------------
# Preflight
# ---------------------------------------------------------------------------
preflight() {
  local fatal=0
  if [ -z "${SKIPPER_API_KEY:-}" ]; then
    err "SKIPPER_API_KEY is not set. Get a key at https://www.skipper.skiplabs.io and export it."
    fatal=1
  fi
  command -v bun >/dev/null || { err "bun not found on PATH."; fatal=1; }
  [ -d "$SKIPPER_BIN_DIR" ] || { err "skipper-bin not found at $SKIPPER_BIN_DIR (set SKIPPER_DIR)."; fatal=1; }
  [ -d "$BENCHS_DIR" ]      || { err "benchs/ not found at $BENCHS_DIR."; fatal=1; }
  [ -d "$EXAMPLES_DIR" ]    || { err "generated-examples/ not found at $EXAMPLES_DIR."; fatal=1; }

  if [ -d "$SKIPPER_DIR/.git" ]; then
    local branch
    branch="$(git -C "$SKIPPER_DIR" rev-parse --abbrev-ref HEAD 2>/dev/null || echo '?')"
    if [ "$branch" != "$SKIPPER_BRANCH" ]; then
      err "skipper is on '$branch', expected '$SKIPPER_BRANCH'. Run: git -C $SKIPPER_DIR switch $SKIPPER_BRANCH"
      fatal=1
    fi
  else
    warn "$SKIPPER_DIR is not a git checkout; cannot verify it is on $SKIPPER_BRANCH (slug discovery falls back to find)."
  fi

  case "$SYNC_MODE" in service|full|none) ;; *) err "SYNC_MODE must be service|full|none (got '$SYNC_MODE')."; fatal=1 ;; esac

  [ "$fatal" = 0 ] || { err "Preflight failed; aborting."; exit 1; }
}

# ---------------------------------------------------------------------------
# Generate one bench into its staging dir
# ---------------------------------------------------------------------------
generate_one() {
  local slug="$1" name
  name="$(dirname_of "$slug")"
  local prompt="$BENCHS_DIR/$slug/prompt.md"
  local stage="$STAGING_DIR/$name"

  if [ ! -f "$prompt" ]; then
    warn "$slug: no prompt at $prompt; skipping."
    return 2
  fi

  log "$slug: generating from benchs/$slug/prompt.md"
  if [ "$DRY_RUN" = 1 ]; then
    printf '   would generate %s -> %s\n' "$slug" "$stage" >&2
    return 0
  fi

  rm -rf "$stage"; mkdir -p "$stage"
  cp "$prompt" "$stage/prompt.md"

  local flags=()
  [ "$GEN_SKJS" = 1 ] && command -v skjs >/dev/null && flags+=(--skjs)

  if ( cd "$SKIPPER_BIN_DIR" \
        && SKIPPER_API_KEY="$SKIPPER_API_KEY" SKIPPER_MODE="$SKIPPER_MODE" \
           bun run generate --to "$stage" "${flags[@]}" ) >"$stage/.regen.log" 2>&1
  then
    [ -f "$stage/src/service.ts" ] || { err "$slug: generation produced no src/service.ts (see $stage/.regen.log)"; return 1; }
    return 0
  else
    err "$slug: generation failed (see $stage/.regen.log)"
    return 1
  fi
}

# ---------------------------------------------------------------------------
# Sync staged output into generated-examples/<name>/ (verbatim file contents)
# ---------------------------------------------------------------------------
sync_one() {
  local slug="$1" name
  name="$(dirname_of "$slug")"
  local stage="$STAGING_DIR/$name"
  local dest="$EXAMPLES_DIR/$name"

  [ "$SYNC_MODE" = none ] && { log "$slug: SYNC_MODE=none, left in staging only"; return 0; }
  [ -d "$stage" ] || { err "$slug: nothing staged to sync"; return 1; }

  if [ "$DRY_RUN" = 1 ]; then printf '   would sync (%s) %s -> %s\n' "$SYNC_MODE" "$stage" "$dest" >&2; return 0; fi

  rm -rf "$dest"; mkdir -p "$dest/src"

  if [ "$SYNC_MODE" = service ]; then
    # Copy only the import-closure of src/service.ts, preserving layout.
    local rel
    while IFS= read -r rel; do
      mkdir -p "$dest/$(dirname "$rel")"
      cp "$stage/$rel" "$dest/$rel"
    done < <(service_closure "$stage")
    # Project scaffolding the skjs check expects.
    [ -f "$stage/package.json" ] && cp "$stage/package.json" "$dest/"
    [ -f "$stage/tsconfig.json" ] && cp "$stage/tsconfig.json" "$dest/"
  else # full
    if command -v rsync >/dev/null; then
      rsync -a --delete \
        --exclude node_modules --exclude packs --exclude .cache \
        --exclude dist --exclude '.regen.log' \
        "$stage"/ "$dest"/
    else
      ( cd "$stage" && find . -type f \
          -not -path './node_modules/*' -not -path './packs/*' \
          -not -path './.cache/*' -not -path './dist/*' -not -name '.regen.log' \
          -print0 | while IFS= read -r -d '' f; do
            mkdir -p "$dest/$(dirname "$f")"; cp "$f" "$dest/$f"
          done )
    fi
  fi
  log "$slug: synced ($SYNC_MODE) -> generated-examples/$name"
}

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
preflight

# Work list: explicit slugs from args, else the discovered selection.
declare -a TARGETS=()
FULL_RUN=0
if [ "$#" -gt 0 ]; then
  for s in "$@"; do
    [ -f "$BENCHS_DIR/$s/prompt.md" ] || { err "no such bench: benchs/$s/prompt.md (under $SKIPPER_DIR)."; exit 1; }
    TARGETS+=("$s")
  done
else
  FULL_RUN=1
  mapfile -t TARGETS < <(select_slugs)
fi
[ "${#TARGETS[@]}" -gt 0 ] || { err "no benches selected (discovered $(discover_slugs | wc -l | tr -d ' ') total)."; exit 1; }

log "skipper:   $SKIPPER_DIR ($SKIPPER_BRANCH), mode=$SKIPPER_MODE"
log "staging:   $STAGING_DIR"
log "discovered $(discover_slugs | wc -l | tr -d ' ') benches; selected ${#TARGETS[@]} (INCLUDE_ALL=$INCLUDE_ALL)"
log "sync mode: $SYNC_MODE   |   jobs: $JOBS   |   dry-run: $DRY_RUN"

# Install generator deps once.
if [ "$DRY_RUN" != 1 ]; then
  log "installing skipper-bin deps (bun install --frozen-lockfile)"
  ( cd "$SKIPPER_BIN_DIR" && bun install --frozen-lockfile ) >/dev/null
fi

mkdir -p "$STAGING_DIR"

# Phase 1 — generate. Generation is the slow, billed part; run a rolling pool
# of up to JOBS concurrent generations — a finished job's slot is backfilled
# immediately (via `wait -n`) rather than draining a fixed-size batch, so a
# slow straggler doesn't idle the other JOBS-1 workers. Syncing happens
# afterwards, serially, for clean logging.
declare -A GEN_RC=()

if [ "$DRY_RUN" = 1 ]; then
  for slug in "${TARGETS[@]}"; do generate_one "$slug" && GEN_RC[$slug]=0 || GEN_RC[$slug]=$?; done
else
  : >"$STAGING_DIR/.gen-status"
  gen_worker() {
    local slug="$1" rc
    set +e; generate_one "$slug"; rc=$?; set -e
    printf '%s\t%s\n' "$slug" "$rc" >>"$STAGING_DIR/.gen-status"
  }
  running=0
  for slug in "${TARGETS[@]}"; do
    gen_worker "$slug" &
    running=$((running + 1))
    if [ "$running" -ge "$JOBS" ]; then
      wait -n
      running=$((running - 1))
    fi
  done
  wait
  while IFS=$'\t' read -r s rc; do GEN_RC[$s]=$rc; done < "$STAGING_DIR/.gen-status"
fi

# Phase 2 — sync (serial).
if [ "$DRY_RUN" != 1 ]; then
  for slug in "${TARGETS[@]}"; do
    [ "${GEN_RC[$slug]:-1}" = 0 ] && sync_one "$slug"
  done
fi

# Phase 2b — prune orphans so the corpus mirrors the selection. Only on a full
# run (a partial run intentionally leaves the rest in place). Deletes (PRUNE=1)
# or just reports (PRUNE=0); never touches the shared skipruntime/ stub dir.
if [ "$FULL_RUN" = 1 ] && [ "$SYNC_MODE" != none ] && [ "$DRY_RUN" != 1 ]; then
  declare -A KEEP=()
  for slug in "${TARGETS[@]}"; do KEEP["$(dirname_of "$slug")"]=1; done
  KEEP[skipruntime]=1
  stale=()
  while IFS= read -r d; do
    b="$(basename "$d")"
    [ -n "${KEEP[$b]:-}" ] || stale+=("$b")
  done < <(find "$EXAMPLES_DIR" -mindepth 1 -maxdepth 1 -type d | sort)
  if [ "${#stale[@]}" -gt 0 ]; then
    if [ "$PRUNE" = 1 ]; then
      for b in "${stale[@]}"; do rm -rf "${EXAMPLES_DIR:?}/$b"; done
      log "pruned ${#stale[@]} stale dir(s): ${stale[*]}"
    else
      warn "${#stale[@]} dir(s) not in selection (set PRUNE=1 to delete): ${stale[*]}"
    fi
  fi
fi

# ---------------------------------------------------------------------------
# Verify with skjs
# ---------------------------------------------------------------------------
declare -A CHK_RC=()
if [ "$VERIFY" = 1 ] && [ "$DRY_RUN" != 1 ] && [ "$SYNC_MODE" != none ]; then
  if [ ! -x "$SKJS_DIR/target/host/dev/skjs" ]; then
    ( cd "$SKJS_DIR" && $RUNNER make build >/dev/null 2>&1 ) || true
  fi
  if [ -x "$SKJS_DIR/target/host/dev/skjs" ]; then
    log "type-checking regenerated examples with skjs"
    for slug in "${TARGETS[@]}"; do
      [ "${GEN_RC[$slug]:-1}" = 0 ] || continue
      name="$(dirname_of "$slug")"
      if ( cd "$SKJS_DIR" && $RUNNER target/host/dev/skjs check --import-stubs import-stubs \
             --project "generated-examples/$name" ) >"$STAGING_DIR/$name/.skjs-check.log" 2>&1; then
        CHK_RC[$slug]=0
      else
        CHK_RC[$slug]=1
      fi
    done
  else
    warn "skjs binary not found at target/host/dev/skjs and could not be built; skipping verification (set RUNNER to your build wrapper, or VERIFY=0)."
  fi
fi

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo >&2
log "================ summary ================"
fail=0
for slug in "${TARGETS[@]}"; do
  g="${GEN_RC[$slug]:-?}"
  case "$g" in
    0) gtxt="gen:ok " ;;
    2) gtxt="gen:skip" ;;
    *) gtxt="gen:FAIL"; fail=1 ;;
  esac
  ctxt=""
  if [ "${CHK_RC[$slug]+set}" = set ]; then
    name="$(dirname_of "$slug")"
    if [ "${CHK_RC[$slug]}" = 0 ]; then ctxt="  skjs:ok"; else ctxt="  skjs:FAIL ($STAGING_DIR/$name/.skjs-check.log)"; fail=1; fi
  fi
  printf '  %-42s %s%s\n' "$slug" "$gtxt" "$ctxt" >&2
done
log "========================================"
if [ "$fail" = 0 ]; then log "all good."; else warn "some steps failed — see logs under $STAGING_DIR/<name>/."; fi

echo >&2
log "Next: review with 'git -C $SKJS_DIR status generated-examples/' and 'git diff', then commit."
exit "$fail"
