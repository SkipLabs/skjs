import fs from "node:fs";
import path from "node:path";
import { createRequire } from "node:module";
import surface from "../tools/claim-text.mts";
import type { Span } from "../tools/span.mts";
import type {
  SkjsClaims,
  SkjsFunction,
  SkjsNamedPoint,
} from "../tools/skjs-claims.mts";
import { record } from "./edits.mts";
// Plain JavaScript modules; the reader loads these in a browser too.
const require = createRequire(import.meta.url);
// Export snapshots. SKJS's claims for each probe source, printed in the syntax
// the viewer shows, with every unavailable type carrying the exporter's
// reason. The expected text sits beside the probe; a diff is a change in what
// the exporter says about that program, to be read and either fixed or
// accepted with UPDATE_EXPECT=1. Nothing here is verified.



const [claimsPath, dir] = process.argv.slice(2);
if (!claimsPath || !dir)
  throw Error("usage: export-snapshots.js <claims.json> <probe-dir>");
const claims: SkjsClaims = JSON.parse(fs.readFileSync(claimsPath, "utf8"));
const probes = fs
  .readdirSync(dir)
  .filter((name) => name.endsWith(".ts"))
  .sort();
const update = process.env.UPDATE_EXPECT === "1";

const span = (pos: Span) => `${pos[0]}-${pos[1]}`;
// The expression's own text, so a line reads without the source open.
function excerpt(source: string, pos: Span) {
  const text = source.slice(pos[0], pos[1]).replace(/\s+/g, " ").trim();
  return text.length > 40 ? text.slice(0, 37) + "..." : text;
}
/** What the producer says it could not decode, which it states as advice
 * rather than as claims: read as it is written, checked as it is read. */
const omissionKey = (u: unknown) => {
  const o = record(u, "an omission");
  const pos = o.pos;
  return [
    o.kind,
    Array.isArray(pos) ? span([Number(pos[0]), Number(pos[1])]) : "",
    o.binding || "",
  ].join("|");
};
function render(source: string, fn: SkjsFunction) {
  const reasons = new Map<string, unknown>();
  for (const u of fn.unavailableTypes || [])
    reasons.set(omissionKey(u), record(u, "an omission").reason);
  const type = (t: unknown, kind: string, pos: Span | null, binding: string) => {
    const reason = reasons.get([kind, pos ? span(pos) : "", binding || ""].join("|"));
    const text = surface.printFull(t);
    return text === "(unavailable)" && reason
      ? `(unavailable: ${reason})`
      : reason
        ? `${text} (reason: ${reason})`
        : text;
  };
  const c = fn.collection;
  const lines = [`## ${fn.name} [${c?.completion} ${c?.quality} ${c?.mode}]`];
  lines.push(
    "params: " +
      (fn.params.length
        ? fn.params
            .map((p) => `${p.name}: ${type(p.type, "parameter", null, p.name)}`)
            .join("; ")
        : "none"),
  );
  lines.push(`result: ${type(fn.retType, "result", null, "")}`);
  // `x!: T` marks a mutable binding; `(declared U)` follows only when the
  // declared type is present and differs from the current narrowed one.
  const binding = (v: SkjsNamedPoint, envPos: Span) => {
    const name = v.name + (v.mutable ? "!" : "");
    const declared =
      "declared" in v
        ? ` (declared ${type(v.declared, "declared", envPos, v.name)})`
        : "";
    return `${name}: ${type(v.type, "entry", envPos, v.name)}${declared}`;
  };
  for (const e of fn.envs)
    lines.push(
      `entry ${span(e.pos)}: ` +
        (e.vars.length
          ? e.vars.map((v) => binding(v, e.pos)).join("; ")
          : "empty"),
    );
  for (const x of fn.exprs)
    lines.push(
      `expr ${span(x.pos)} \`${excerpt(source, x.pos)}\`: ${type(x.type, "expression", x.pos, "")}`,
    );
  for (const x of fn.lvalues || [])
    lines.push(
      `lvalue ${span(x.pos)} \`${excerpt(source, x.pos)}\`: ${type(x.type, "lvalue", x.pos, "")}`,
    );
  for (const op of fn.operations || []) {
    const relation = op.kind === "expand" ? "→" : "≤";
    lines.push(
      `${op.kind} ${type(op.source, "expression", null, "")} ${relation} ${type(op.target, "expression", null, "")}`,
    );
  }
  return lines.join("\n");
}

let failed = 0;
for (const name of probes) {
  const file = path.posix.join(dir, name);
  const source = fs.readFileSync(file, "utf8");
  const entry = claims.find((c) => c.file === file);
  const body = entry
    ? entry.functions.map((fn) => render(source, fn)).join("\n\n")
    : "(no claims exported for this file)";
  const actual = `# ${name}\n\n${body}\n`;
  const expectedPath = path.join(dir, name.replace(/\.ts$/, ".snap"));
  const expected = fs.existsSync(expectedPath)
    ? fs.readFileSync(expectedPath, "utf8")
    : null;
  if (actual === expected) {
    console.log(`  ${name}: OK`);
    continue;
  }
  if (update) {
    fs.writeFileSync(expectedPath, actual);
    console.log(`  ${name}: ${expected === null ? "written" : "updated"}`);
    continue;
  }
  failed++;
  console.log(`  ${name}: ${expected === null ? "MISSING expected file" : "DIFFERS"}`);
  const a = (expected || "").split("\n"), b = actual.split("\n");
  for (let i = 0; i < Math.max(a.length, b.length); i++)
    if (a[i] !== b[i]) {
      if (a[i] !== undefined) console.log(`    - ${a[i]}`);
      if (b[i] !== undefined) console.log(`    + ${b[i]}`);
    }
}
console.log(
  `Export snapshots: ${probes.length - failed} passed, ${failed} failed` +
    (failed ? " (UPDATE_EXPECT=1 rewrites the expected files)" : ""),
);
process.exit(failed ? 1 : 0);
