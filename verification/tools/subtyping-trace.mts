// Measures the subtyping algorithm's work (RECURSIVE-EQUATIONS §4) on the
// pipeline cases: runs the cases whose file names contain a pattern (every
// case without one) with the verifier's `--trace-subtyping`, then reports,
// per subtyping question the checker asked, its work against the size of the
// types compared, and the variance computations and fallback searches.
//   node verification/tools/subtyping-trace.mts [pattern ...]
// The trace format is in REQUEST-PROTOCOL ("Subtyping traces").
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { cases } from "../pipeline/cases.mts";
import { pooled, runCase } from "../pipeline/run-cases.mts";

/** One checker question: `subset` (the premise judgment on a pair, `Var`)
 * or `family` (the fallback's pairs checked as a family entry). */
interface Question {
  question: "subset" | "family";
  source: number;
  target: number;
  holds: boolean;
  instances: number;
  varSteps: number;
  varDepth: number;
  events: unknown[];
}
/** A component's variances, computed while answering a question or apart. */
interface Variances {
  variances: number[];
  generic: number;
  polarityRounds: number;
  checkRounds: number;
  memberChecks: number;
  weakened: number;
  kept: number;
}
/** One fallback search (search phase). */
interface Fallback {
  search: "fallback";
  source: number;
  target: number;
  rows: number;
  rounds: number;
  visited: number;
  refused: string | null;
  proved: boolean;
}
type Line = Question | Variances | Fallback;

const isNat = (x: unknown): x is number => typeof x === "number" && Number.isInteger(x) && x >= 0;
const record = (x: unknown): Record<string, unknown> | undefined =>
  typeof x === "object" && x !== null && !Array.isArray(x) ? Object.fromEntries(Object.entries(x)) : undefined;
const exactly = (o: Record<string, unknown>, keys: string[]) =>
  Object.keys(o).length === keys.length && keys.every((k) => k in o);

/** The decoder: one spelling per line kind, every field required. */
function decode(text: string): Line {
  const o = record(JSON.parse(text));
  if (o === undefined) throw new Error(`not an object: ${text}`);
  const nat = (key: string): number => {
    const value = o[key];
    if (!isNat(value)) throw new Error(`${key} is not a count: ${text}`);
    return value;
  };
  const { question, holds, events, variances, search, refused, proved } = o;
  if ((question === "subset" || question === "family") &&
      exactly(o, ["question", "source", "target", "holds", "instances", "varSteps", "varDepth", "events"]) &&
      typeof holds === "boolean" && Array.isArray(events))
    return { question, source: nat("source"), target: nat("target"), holds, instances: nat("instances"),
      varSteps: nat("varSteps"), varDepth: nat("varDepth"), events };
  if (exactly(o, ["variances", "generic", "polarityRounds", "checkRounds", "memberChecks", "weakened", "kept"]) &&
      Array.isArray(variances) && variances.every(isNat))
    return { variances, generic: nat("generic"), polarityRounds: nat("polarityRounds"), checkRounds: nat("checkRounds"),
      memberChecks: nat("memberChecks"), weakened: nat("weakened"), kept: nat("kept") };
  if (search === "fallback" &&
      exactly(o, ["search", "source", "target", "rows", "rounds", "visited", "refused", "proved"]) &&
      (refused === null || refused === "growth" || refused === "exhausted") && typeof proved === "boolean")
    return { search, source: nat("source"), target: nat("target"), rows: nat("rows"), rounds: nat("rounds"),
      visited: nat("visited"), refused, proved };
  throw new Error(`unknown trace line: ${text}`);
}

const lines = (file: string): Line[] =>
  existsSync(file) ? readFileSync(file, "utf8").split("\n").filter((l) => l !== "").map(decode) : [];

/** Variance lines, whether apart or inside a question's events. */
function variancesOf(ls: Line[]): Variances[] {
  const out: Variances[] = [];
  for (const l of ls) {
    if ("variances" in l) out.push(l);
    if ("question" in l) for (const e of l.events) {
      const d = decode(JSON.stringify(e));
      if ("variances" in d) out.push(d);
    }
  }
  return out;
}

const patterns = process.argv.slice(2);
const selected = cases.filter((c) => !patterns.length || patterns.some((p) => c.file.includes(p)));
process.env.SUBTYPING_TRACE = "1";
const results = await pooled(selected, runCase);

const questions: (Question & { file: string })[] = [];
const components: Variances[] = [];
const fallbacks: Fallback[] = [];
results.forEach((r, i) => {
  if (r.status !== "fulfilled") return;
  const file = selected[i]?.file ?? "";
  for (const phase of ["search", "check"]) {
    const ls = lines(join(r.value.artifacts, `${phase}-subtyping.jsonl`));
    if (phase === "check") for (const l of ls) if ("question" in l) questions.push({ ...l, file });
    components.push(...variancesOf(ls));
    for (const l of ls) if ("search" in l) fallbacks.push(l);
  }
});

const quantile = (xs: number[], q: number) => {
  if (!xs.length) return 0;
  const s = [...xs].sort((a, b) => a - b);
  return s[Math.min(s.length - 1, Math.floor(q * s.length))] ?? 0;
};
const work = (q: Question) => q.instances + 1;
const size = (q: Question) => q.source + q.target;
const ratios = questions.map((q) => work(q) / Math.max(1, size(q)));
const worst = [...questions].sort((a, b) => work(b) / Math.max(1, size(b)) - work(a) / Math.max(1, size(a)))[0];

console.log(`cases: ${selected.length}, questions checked: ${questions.length} ` +
  `(subset ${questions.filter((q) => q.question === "subset").length}, family ${questions.filter((q) => q.question === "family").length})`);
console.log(`work per question (Inst steps tried + 1) over size (source + target): ` +
  `median ${quantile(ratios, 0.5).toFixed(3)}, p90 ${quantile(ratios, 0.9).toFixed(3)}, ` +
  `p99 ${quantile(ratios, 0.99).toFixed(3)}, max ${Math.max(0, ...ratios).toFixed(3)}`);
if (worst) console.log(`largest ratio: ${worst.file}: ${worst.question} of sizes ${worst.source}+${worst.target}, ` +
  `${worst.instances} Inst steps, ${worst.varSteps} by Var, depth ${worst.varDepth}`);
console.log(`Var: ${questions.reduce((n, q) => n + q.varSteps, 0)} steps, max depth ${Math.max(0, ...questions.map((q) => q.varDepth))}, ` +
  `max size compared ${Math.max(0, ...questions.map(size))}`);
console.log(`variance components computed: ${components.length}, members ${components.reduce((n, c) => n + c.variances.length, 0)}, ` +
  `polarity rounds max ${Math.max(0, ...components.map((c) => c.polarityRounds))}, ` +
  `member checks ${components.reduce((n, c) => n + c.memberChecks, 0)}, weakened to inv ${components.reduce((n, c) => n + c.weakened, 0)}, ` +
  `kept ${components.reduce((n, c) => n + c.kept, 0)}`);
console.log(`fallback searches: ${fallbacks.length}, proved ${fallbacks.filter((f) => f.proved).length}, ` +
  `refused at growth ${fallbacks.filter((f) => f.refused === "growth").length}, at the limit ${fallbacks.filter((f) => f.refused === "exhausted").length}, ` +
  `max rows ${Math.max(0, ...fallbacks.map((f) => f.rows))}, max pairs visited ${Math.max(0, ...fallbacks.map((f) => f.visited))}`);
