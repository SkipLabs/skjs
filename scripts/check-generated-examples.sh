#!/usr/bin/env bash
#
# Reproducible checker for generated examples.
# Runs BOTH:
# - TypeScript compiler (tsc --noEmit) with pinned TypeScript version
# - SKJS checker (skjs check)
#
# Intended usage (inside Skip Docker image):
#   ./scripts/check-generated-examples.sh
#
# Optional environment variables:
# - TS_VERSION: TypeScript version for npx (default: 5.7.3)
# - OUT_DIR: output directory for reports (default: ./.generated-examples-check)
# - PROJECT_ROOT: repo root (default: current working directory)
# - CLEAN: if set to 1, remove OUT_DIR before running (same as --clean)
#
set -u -o pipefail

usage() {
  cat <<'EOF'
Usage:
  ./scripts/check-generated-examples.sh [--clean]

Options:
  --clean   Remove the output directory (OUT_DIR) before running.

Environment:
  TS_VERSION   TypeScript version for npx (default: 5.7.3)
  OUT_DIR      Output directory for reports (default: ./.generated-examples-check)
  PROJECT_ROOT Repo root (default: current working directory)
  CLEAN        If set to 1, same as --clean
  ONLY_PROJECT If set, check only that project directory (e.g. generated-examples/search-index-service)
EOF
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi

CLEAN="${CLEAN:-0}"
if [[ "${1:-}" == "--clean" ]]; then
  CLEAN=1
  shift
fi

TS_VERSION="${TS_VERSION:-5.7.3}"
OUT_DIR="${OUT_DIR:-.generated-examples-check}"
PROJECT_ROOT="${PROJECT_ROOT:-$(pwd)}"

SKJS_BIN="${PROJECT_ROOT}/target/host/dev/skjs"
IMPORT_STUBS_DIR="${PROJECT_ROOT}/import-stubs"
GENERATED_DIR="${PROJECT_ROOT}/generated-examples"

if [[ ! -d "${GENERATED_DIR}" ]]; then
  echo "ERROR: ${GENERATED_DIR} does not exist"
  exit 2
fi

if [[ ! -d "${IMPORT_STUBS_DIR}" ]]; then
  echo "ERROR: ${IMPORT_STUBS_DIR} does not exist"
  exit 2
fi

summary_tsv="${OUT_DIR}/summary.tsv"
summary_json="${OUT_DIR}/summary.json"
if [[ "${CLEAN}" == "1" ]]; then
  # Safety: only allow cleaning paths inside PROJECT_ROOT, and refuse root-ish values.
  resolved_out="$(node -e "const p=require('path'); console.log(p.resolve(process.argv[1]));" "${OUT_DIR}")"
  resolved_root="$(node -e "const p=require('path'); console.log(p.resolve(process.argv[1]));" "${PROJECT_ROOT}")"
  if [[ -z "${resolved_out}" || "${resolved_out}" == "/" || "${resolved_out}" == "${resolved_root}" ]]; then
    echo "ERROR: refusing to --clean unsafe OUT_DIR=${OUT_DIR}"
    exit 2
  fi
  case "${resolved_out}" in
    "${resolved_root}"/*) ;;
    *)
      echo "ERROR: refusing to --clean OUT_DIR outside PROJECT_ROOT"
      echo "  OUT_DIR=${OUT_DIR}"
      echo "  PROJECT_ROOT=${PROJECT_ROOT}"
      exit 2
      ;;
  esac
  rm -rf "${resolved_out}"
fi
mkdir -p "${OUT_DIR}"
echo -e "project\ttsc_ms\ttsc_error_count\tskjs_ms\tskjs_error_count" > "${summary_tsv}"

tsc_version_file="${OUT_DIR}/tsc-version.txt"
mkdir -p "${OUT_DIR}"

if command -v npx >/dev/null 2>&1; then
  # Suppress npm update notifier noise for reproducible outputs.
  tsc_ver="$(
    NPM_CONFIG_UPDATE_NOTIFIER=false \
      npx -y -p "typescript@${TS_VERSION}" tsc --version 2>/dev/null | head -n 1
  )"
  if [[ -n "${tsc_ver}" ]]; then
    mkdir -p "${OUT_DIR}"
    echo "${tsc_ver}" > "${tsc_version_file}"
  else
    mkdir -p "${OUT_DIR}"
    echo "UNKNOWN" > "${tsc_version_file}"
  fi
  echo "tsc version:"
  cat "${tsc_version_file}"
else
  mkdir -p "${OUT_DIR}"
  echo "npx not found" > "${tsc_version_file}"
  echo "tsc version:"
  cat "${tsc_version_file}"
fi

if [[ ! -x "${SKJS_BIN}" ]]; then
  # Common case inside the Docker image: build outputs are not present yet.
  if command -v skargo >/dev/null 2>&1; then
    echo "SKJS binary missing; attempting build with skargo build..."
    skargo build || true
  fi
fi

tmpdir="$(mktemp -d)"
cleanup() { rm -rf "${tmpdir}"; }
trap cleanup EXIT

now_ms() {
  # Prefer node for portability; date formatting differs across distros.
  node -e "process.stdout.write(String(Date.now()))"
}

ONLY_PROJECT="${ONLY_PROJECT:-}"

# Map known stub modules explicitly (Node16 module resolution requires the file).
mk_tsc_overlay() {
  project_dir="$1"
  project_tsconfig="${project_dir}/tsconfig.json"
  overlay="${tmpdir}/tsconfig-overlay-$(echo "${project_dir}" | tr '/:' '__').json"

  cat > "${overlay}" <<EOF
{
  "extends": "${project_tsconfig}",
  "compilerOptions": {
    "baseUrl": "${PROJECT_ROOT}",
    "paths": {
      "@skipruntime/core": ["import-stubs/@skipruntime/core/index.d.ts"],
      "@skipruntime/helpers": ["import-stubs/@skipruntime/helpers/index.d.ts"],
      "@skipruntime/server": ["import-stubs/@skipruntime/server/index.d.ts"],
      "@skip-adapter/fastify": ["import-stubs/@skip-adapter/fastify/index.d.ts"],
      "@fastify/*": ["import-stubs/@fastify/*/index.d.ts"],
      "fastify": ["import-stubs/fastify/index.d.ts"],
      "pino": ["import-stubs/pino/index.d.ts"]
    }
  }
}
EOF
  echo "${overlay}"
}

list_projects() {
  # Print project directories containing a tsconfig.json, sorted.
  # Use LC_ALL=C for stable ordering.
  if [[ -n "${ONLY_PROJECT}" ]]; then
    echo "${ONLY_PROJECT}"
    return 0
  fi
  (cd "${PROJECT_ROOT}" && find "generated-examples" -name tsconfig.json -print) | \
    sed 's#/tsconfig.json$##' | LC_ALL=C sort -u
}

run_tsc() {
  project_rel="$1"
  out_dir="${OUT_DIR}/${project_rel}"
  mkdir -p "${out_dir}"

  overlay="$(mk_tsc_overlay "${PROJECT_ROOT}/${project_rel}")"
  out_file="${out_dir}/tsc.txt"
  counts_file="${out_dir}/tsc.errors.json"

  if ! command -v npx >/dev/null 2>&1; then
    echo "npx not found" > "${out_file}"
    echo "{}" > "${counts_file}"
    echo "RESULT" 0 -1
    return 0
  fi

  start_ms="$(now_ms)"
  NPM_CONFIG_UPDATE_NOTIFIER=false \
    npx -y -p "typescript@${TS_VERSION}" tsc --noEmit -p "${overlay}" > "${out_file}" 2>&1
  ec=$?
  end_ms="$(now_ms)"
  dur_ms="$((end_ms - start_ms))"

  # Count errors by TS code + message (stable across file/line changes),
  # and keep a few sample locations for each signature.
  node - <<'NODE' "${out_file}" "${counts_file}"
const fs = require('fs');
const [,, inFile, countsOutFile] = process.argv;
const text = fs.existsSync(inFile) ? fs.readFileSync(inFile, 'utf8') : '';
const lines = text.split(/\r?\n/);
const counts = Object.create(null);

// Example:
// path/to/file.ts(12,34): error TS1234: Message
const re = /^(.*)\((\d+),(\d+)\):\s*error\s+TS(\d+):\s*(.*)$/;
const signatureSamples = Object.create(null);

function takeSample(arr, sample, limit) {
  if (arr.length < limit) arr.push(sample);
}

for (const ln of lines) {
  const m = ln.match(re);
  if (!m) continue;
  const file = m[1];
  const line = Number(m[2]);
  const col = Number(m[3]);
  const code = m[4];
  const msg = m[5];
  const signature = `TS${code}: ${msg}`;

  counts[signature] = (counts[signature] || 0) + 1;
  if (!signatureSamples[signature]) signatureSamples[signature] = [];
  takeSample(signatureSamples[signature], { file, line, col }, 5);
}

// Derive block counts + keep signature-level samples
const total = Object.values(counts).reduce((a, b) => a + b, 0);
fs.writeFileSync(countsOutFile, JSON.stringify({ total, counts, signatureSamples }, null, 2));
NODE

  err_total="$(
    node -e "const fs=require('fs'); const p=process.argv[1]; const j=JSON.parse(fs.readFileSync(p,'utf8')); process.stdout.write(String(j.total||0));" \
      "${counts_file}" 2>/dev/null
  )"
  if [[ -z "${err_total}" ]]; then err_total=0; fi

  if [[ $ec -eq 0 ]]; then
    echo "ok ${project_rel} (tsc)"
    echo "RESULT" "${dur_ms}" "${err_total}"
  else
    echo "fail ${project_rel} (tsc) exit=${ec}"
    # Print a short preview to stdout for interactive use
    head -n 20 "${out_file}" | sed 's/^/  /'
    # If tsc failed but produced 0 parsed errors, treat as a tool failure.
    if [[ "${err_total}" == "0" ]]; then err_total=-1; fi
    echo "RESULT" "${dur_ms}" "${err_total}"
  fi
}

run_skjs() {
  project_rel="$1"
  out_dir="${OUT_DIR}/${project_rel}"
  mkdir -p "${out_dir}"

  out_file="${out_dir}/skjs.txt"
  counts_file="${out_dir}/skjs.errors.json"

  if [[ ! -x "${SKJS_BIN}" ]]; then
    echo "SKJS binary missing or not executable: ${SKJS_BIN}" > "${out_file}"
    echo "{}" > "${counts_file}"
    echo "RESULT" 0 -1
    return 0
  fi

  start_ms="$(now_ms)"
  "${SKJS_BIN}" check --import-stubs "${IMPORT_STUBS_DIR}" "${PROJECT_ROOT}/${project_rel}" > "${out_file}" 2>&1
  ec=$?
  end_ms="$(now_ms)"
  dur_ms="$((end_ms - start_ms))"

  # Parse SKJS error blocks separated by blank lines.
  # For each block, compute a signature and keep a few sample locations.
  node - <<'NODE' "${out_file}" "${counts_file}"
const fs = require('fs');
const [,, inFile, countsOutFile] = process.argv;
const text = fs.existsSync(inFile) ? fs.readFileSync(inFile, 'utf8') : '';
const lines = text.split(/\r?\n/);

function normalizeTypeyMessage(msg) {
  // Normalize common type-bearing messages so variants cluster.
  // Examples:
  // - "This is of type: MetricData" -> "This is of type: <TYPE>"
  // - "It is incompatible with: string" -> "It is incompatible with: <TYPE>"
  // - "It does not implement: Json" -> keep
  return msg
    .replace(/This is of type:\s*.+$/, 'This is of type: <TYPE>')
    .replace(/It is incompatible with:\s*.+$/, 'It is incompatible with: <TYPE>')
    .replace(/Please add a type annotation.*$/, 'Please add a type annotation')
    .replace(/Missing type annotation.*$/, 'Missing type annotation');
}

// Parse (File line, message) pairs.
const fileRe = /^File \"([^\"]+)\", line (\d+), character (\d+-\d+):$/;
const dockerPrefix = '/work/skjs/';

const blocks = [];
let cur = [];
for (const ln of lines) {
  if (ln.trim() === '') {
    if (cur.length > 0) {
      blocks.push(cur);
      cur = [];
    }
  } else {
    cur.push(ln);
  }
}
if (cur.length > 0) blocks.push(cur);

function takeSample(arr, sample, limit) {
  if (arr.length < limit) arr.push(sample);
}

const counts = Object.create(null);
const signatureSamples = Object.create(null);

for (const bLines of blocks) {
  // Extract pairs
  const pairs = [];
  for (let i = 0; i < bLines.length - 1; i++) {
    const m = bLines[i].match(fileRe);
    if (!m) continue;
    let file = m[1];
    if (file.startsWith(dockerPrefix)) file = file.slice(dockerPrefix.length);
    const line = Number(m[2]);
    const chr = m[3];
    const msg = (bLines[i + 1] || '').trim();
    if (!msg) continue;
    pairs.push({ file, line, chr, msg });
  }
  if (pairs.length === 0) continue;

  // Prefer a sample location in generated-examples over import-stubs.
  let samplePair = pairs[0];
  for (const p of pairs) {
    if (p.file.startsWith('generated-examples/')) {
      samplePair = p;
      break;
    }
  }

  const primary = pairs[0].msg;
  const normPrimary = normalizeTypeyMessage(primary);

  // Add a small amount of normalized context for better clustering, but avoid overfitting.
  // Keep up to 2 distinct "secondary" messages from within the block.
  const secondary = [];
  for (let i = 1; i < pairs.length; i++) {
    const nm = normalizeTypeyMessage(pairs[i].msg);
    if (nm === normPrimary) continue;
    if (secondary.includes(nm)) continue;
    secondary.push(nm);
    if (secondary.length >= 2) break;
  }

  const signature = secondary.length > 0 ? `${normPrimary} :: ${secondary.join(' | ')}` : normPrimary;

  counts[signature] = (counts[signature] || 0) + 1;
  if (!signatureSamples[signature]) signatureSamples[signature] = [];
  takeSample(signatureSamples[signature], { file: samplePair.file, line: samplePair.line, chr: samplePair.chr }, 5);

}

const total = Object.values(counts).reduce((a, b) => a + b, 0);
fs.writeFileSync(countsOutFile, JSON.stringify({ total, counts, signatureSamples }, null, 2));
NODE

  err_total="$(
    node -e "const fs=require('fs'); const p=process.argv[1]; const j=JSON.parse(fs.readFileSync(p,'utf8')); process.stdout.write(String(j.total||0));" \
      "${counts_file}" 2>/dev/null
  )"
  if [[ -z "${err_total}" ]]; then err_total=0; fi

  if [[ $ec -eq 0 ]]; then
    echo "ok ${project_rel} (skjs)"
    echo "RESULT" "${dur_ms}" "${err_total}"
  else
    echo "fail ${project_rel} (skjs) exit=${ec}"
    head -n 20 "${out_file}" | sed 's/^/  /'
    # If skjs failed but produced 0 parsed errors, treat as a tool failure.
    if [[ "${err_total}" == "0" ]]; then err_total=-1; fi
    echo "RESULT" "${dur_ms}" "${err_total}"
  fi
}

projects="$(list_projects)"
if [[ -z "${projects}" ]]; then
  echo "No projects found under generated-examples/"
  exit 0
fi

while IFS= read -r project_rel; do
  # Each project must have a tsconfig.json
  if [[ ! -f "${PROJECT_ROOT}/${project_rel}/tsconfig.json" ]]; then
    continue
  fi

  tsc_res="$(run_tsc "${project_rel}")"
  tsc_ms="$(echo "${tsc_res}" | tail -n 1 | awk '{print $2}')"
  tsc_errs="$(echo "${tsc_res}" | tail -n 1 | awk '{print $3}')"

  skjs_res="$(run_skjs "${project_rel}")"
  skjs_ms="$(echo "${skjs_res}" | tail -n 1 | awk '{print $2}')"
  skjs_errs="$(echo "${skjs_res}" | tail -n 1 | awk '{print $3}')"

  echo -e "${project_rel}\t${tsc_ms}\t${tsc_errs}\t${skjs_ms}\t${skjs_errs}" >> "${summary_tsv}"
done <<< "${projects}"

# Produce a JSON summary (requires node, which is available in skiplabs/skip image).
node - <<'NODE'
const fs = require('fs');
const path = require('path');

const outDir = process.env.OUT_DIR || '.generated-examples-check';
const summaryTsv = path.join(outDir, 'summary.tsv');
const tsv = fs.readFileSync(summaryTsv, 'utf8').trimEnd().split('\n');
const header = tsv[0].split('\t');
const rows = tsv.slice(1).filter(Boolean).map(line => {
  const cols = line.split('\t');
  const row = {};
  for (let i = 0; i < header.length; i++) row[header[i]] = cols[i];
  row.tsc_ms = Number(row.tsc_ms);
  row.tsc_error_count = Number(row.tsc_error_count);
  row.skjs_ms = Number(row.skjs_ms);
  row.skjs_error_count = Number(row.skjs_error_count);
  return row;
});

function runCmd(cmd) {
  try {
    const { execSync } = require('child_process');
    return execSync(cmd, { stdio: ['ignore', 'pipe', 'ignore'] }).toString('utf8').trim();
  } catch {
    return null;
  }
}

const counts = {
  projects: rows.length,
  tsc_ok: rows.filter(r => r.tsc_error_count === 0).length,
  tsc_fail: rows.filter(r => r.tsc_error_count !== 0).length,
  skjs_ok: rows.filter(r => r.skjs_error_count === 0).length,
  skjs_fail: rows.filter(r => r.skjs_error_count !== 0).length,
  tsc_total_ms: rows.reduce((a, r) => a + (r.tsc_ms || 0), 0),
  skjs_total_ms: rows.reduce((a, r) => a + (r.skjs_ms || 0), 0),
  tsc_total_errors: rows.reduce((a, r) => a + (r.tsc_error_count > 0 ? r.tsc_error_count : 0), 0),
  skjs_total_errors: rows.reduce((a, r) => a + (r.skjs_error_count > 0 ? r.skjs_error_count : 0), 0),
  tsc_tool_failures: rows.filter(r => r.tsc_error_count < 0).length,
  skjs_tool_failures: rows.filter(r => r.skjs_error_count < 0).length,
};

function readJsonIfExists(p) {
  try {
    if (!fs.existsSync(p)) return null;
    return JSON.parse(fs.readFileSync(p, 'utf8'));
  } catch {
    return null;
  }
}

function mergeCounts(into, countsObj) {
  if (!countsObj) return;
  for (const [k, v] of Object.entries(countsObj)) {
    into[k] = (into[k] || 0) + Number(v || 0);
  }
}

function mergeProjectSets(into, sigToProjects, project, countsObj) {
  if (!countsObj) return;
  for (const k of Object.keys(countsObj)) {
    if (!sigToProjects[k]) sigToProjects[k] = new Set();
    sigToProjects[k].add(project);
    into[k] = (into[k] || 0) + Number(countsObj[k] || 0);
  }
}

function mergeSamples(into, samplesObj) {
  if (!samplesObj) return;
  for (const [sig, samples] of Object.entries(samplesObj)) {
    if (!into[sig]) into[sig] = [];
    for (const s of samples) {
      if (into[sig].length >= 5) break;
      // dedupe by file:line
      const key = `${s.file}:${s.line}:${s.chr || s.col || ''}`;
      if (into[sig].some(x => `${x.file}:${x.line}:${x.chr || x.col || ''}` === key)) continue;
      into[sig].push(s);
    }
  }
}

// Aggregate error cardinalities across all projects.
const tsc_counts_all = {};
const skjs_counts_all = {};
const tsc_projects_by_sig = Object.create(null);
const skjs_projects_by_sig = Object.create(null);
const tsc_samples_by_sig = Object.create(null);
const skjs_samples_by_sig = Object.create(null);
for (const r of rows) {
  const projDir = path.join(outDir, r.project);
  const tscErr = readJsonIfExists(path.join(projDir, 'tsc.errors.json'));
  const skjsErr = readJsonIfExists(path.join(projDir, 'skjs.errors.json'));
  mergeProjectSets(tsc_counts_all, tsc_projects_by_sig, r.project, tscErr && tscErr.counts);
  mergeProjectSets(skjs_counts_all, skjs_projects_by_sig, r.project, skjsErr && skjsErr.counts);
  mergeSamples(tsc_samples_by_sig, tscErr && tscErr.signatureSamples);
  mergeSamples(skjs_samples_by_sig, skjsErr && skjsErr.signatureSamples);
}

function topN(countsObj, n) {
  return Object.entries(countsObj)
    .sort((a, b) => (b[1] - a[1]) || a[0].localeCompare(b[0]))
    .slice(0, n)
    .map(([signature, count]) => ({ signature, count }));
}

function enrich(top, projectsBySig, samplesBySig) {
  return top.map(({ signature, count }) => ({
    signature,
    count,
    projects_affected: projectsBySig[signature] ? projectsBySig[signature].size : 0,
    samples: (samplesBySig[signature] || []).slice().sort((a, b) => {
      const aGen = (a.file || '').startsWith('generated-examples/') ? 0 : 1;
      const bGen = (b.file || '').startsWith('generated-examples/') ? 0 : 1;
      if (aGen !== bGen) return aGen - bGen;
      return `${a.file}:${a.line}`.localeCompare(`${b.file}:${b.line}`);
    }),
  }));
}

const summary = {
  generated_at: new Date().toISOString(),
  ts_version: fs.existsSync(path.join(outDir, 'tsc-version.txt'))
    ? fs.readFileSync(path.join(outDir, 'tsc-version.txt'), 'utf8').split('\n')[0].trim()
    : null,
  metadata: {
    node: process.version,
    npm: runCmd('npm --version'),
    git_skjs_sha: runCmd('git -C . rev-parse HEAD'),
    git_skip_sha: runCmd('git -C ../skip rev-parse HEAD'),
    skjs_version: runCmd('./target/host/dev/skjs --version'),
  },
  counts,
  error_cardinality: {
    tsc_top: enrich(topN(tsc_counts_all, 50), tsc_projects_by_sig, tsc_samples_by_sig),
    skjs_top: enrich(topN(skjs_counts_all, 50), skjs_projects_by_sig, skjs_samples_by_sig),
  },
  rows,
};

fs.writeFileSync(path.join(outDir, 'summary.json'), JSON.stringify(summary, null, 2));
NODE

echo "Wrote:"
echo "  - ${summary_tsv}"
echo "  - ${summary_json}"
echo "  - ${OUT_DIR}/<project>/tsc.txt"
echo "  - ${OUT_DIR}/<project>/skjs.txt"


