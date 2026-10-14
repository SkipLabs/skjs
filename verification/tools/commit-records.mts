/* Renders commit records as a review page: one card per commit, and for
 * branch ranges a summary of what each branch changes and where branches
 * overlap. A record is a commit message (or a note on refs/notes/records,
 * which takes precedence) in the format the `review` skill states: a subject,
 * prose sections ("Example:", "Rule:", indented blocks) and git trailers.
 *
 *   node verification/tools/commit-records.mts --out review.html bb180be19
 *   node verification/tools/commit-records.mts --out review.html cf3fbb3c1..branch-a cf3fbb3c1..branch-b
 *   --fragment omits the document skeleton (for an Artifact publish).
 */
import { execFileSync } from "node:child_process";
import { writeFileSync } from "node:fs";

const git = (args: string[], input?: string): string =>
  execFileSync("git", args, { input, encoding: "utf8", maxBuffer: 64 << 20, stdio: ["pipe", "pipe", "ignore"] });

const esc = (s: string): string =>
  s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

const inline = (s: string): string => esc(s).replace(/`([^`]+)`/g, "<code>$1</code>");

type Section = { name: string; text: string[]; block: string[] };
type CommitRecord = {
  sha: string; author: string; subject: string; sections: Section[];
  trailers: Map<string, string>; coauthors: string[]; stat: string[];
};

const OUTCOMES: { [k: string]: string } = {
  verified: "ok", refused: "principled", gap: "gap", "no-behaviour-change": "neutral",
};
const FACTS = ["Parts", "Lean", "Wire", "Trust", "Depends", "Measured", "Tests"];

/** The record of one commit: its note if it has one, else its message. */
function readRecord(rev: string): CommitRecord {
  let text = "";
  try { text = git(["notes", "--ref=records", "show", rev]); } catch { /* no note */ }
  const message = git(["show", "-s", "--format=%B", rev]);
  if (!text.trim()) text = message;
  const trailers = new Map<string, string>();
  for (const line of git(["interpret-trailers", "--parse"], text).split("\n")) {
    const i = line.indexOf(":");
    if (i <= 0) continue;
    const key = line.slice(0, i).trim(), value = line.slice(i + 1).trim();
    trailers.set(key, trailers.has(key) ? `${trailers.get(key)} ${value}` : value);
  }
  const lines = text.trimEnd().split("\n");
  let end = lines.length;
  while (end > 1 && (/^[A-Za-z-]+: /.test(lines[end - 1]) || lines[end - 1].startsWith(" "))) end--;
  const sections: Section[] = [];
  let current: Section | undefined;
  for (const line of lines.slice(1, end)) {
    const head = /^([A-Z][A-Za-z ]+):\s*(.*)$/.exec(line);
    if (head) {
      current = { name: head[1], text: head[2] ? [head[2]] : [], block: [] };
      sections.push(current);
    } else if (line.startsWith("    ")) {
      (current ??= pushProse(sections)).block.push(line.slice(4));
    } else if (line.trim()) {
      if (!current || current.block.length) current = pushProse(sections);
      current.text.push(line.trim());
    } else if (current?.block.length) current.block.push("");
    else if (current && !current.name) current = undefined;
  }
  return {
    sha: git(["rev-parse", "--short=9", rev]).trim(),
    author: git(["show", "-s", "--format=%an · %ad", "--date=format:%b %d, %H:%M", rev]).trim(),
    subject: lines[0],
    sections,
    trailers,
    coauthors: message.split("\n").filter(l => l.startsWith("Co-Authored-By:"))
      .map(l => l.replace("Co-Authored-By:", "with").replace(/<[^>]*>/, "").trim()),
    stat: git(["show", "--stat", "--format=", rev]).trimEnd().split("\n").filter(Boolean),
  };
}

function pushProse(sections: Section[]): Section {
  const s = { name: "", text: [], block: [] };
  sections.push(s);
  return s;
}

const words = (r: CommitRecord, key: string): string[] => (r.trailers.get(key) ?? "").split(/\s+/).filter(Boolean);

function tests(value: string): string {
  return value.split(/\s+(?=[+-]|forged:)/).map(t => {
    const kind = t.startsWith("+") ? "pos" : t.startsWith("-") ? "neg" : t.startsWith("forged:") ? "forged" : "plain";
    return `<span class="test ${kind}">${esc(t.replace(/^[+-]|^forged:/, ""))}</span>`;
  }).join(" ");
}

/** Mathematics in a rule: sub- and superscripts set as such, on escaped text. */
function math(text: string): string {
  return esc(text)
    .replace(/_\{([^{}]*)\}/g, "<sub>$1</sub>")
    .replace(/\^\{([^{}]*)\}/g, "<sup>$1</sup>")
    .replace(/_([A-Za-z0-9\u0370-\u03ff\u2200-\u22ff]+(?:\u20d7)?)/g, "<sub>$1</sub>");
}

/** A line's parts: runs of three or more spaces separate side-by-side formulas. */
const parts = (line: string): string[] => line.trim().split(/\s{3,}/).filter(Boolean);

/** Formulas, one row per line, an indented line continuing the one above. */
const formulas = (lines: string[]): string =>
  `<div class="formulas">${lines.map(l => `<div class="row${/^\s{2,}/.test(l) ? " cont" : ""}">${parts(l).map(p => `<span>${math(p)}</span>`).join("")}</div>`).join("")}</div>`;

/** A `Rule:` block: groups separated by blank lines; a group with a line of
 * `─` is an inference rule (premises above, conclusion below, the name after
 * the bar); any other group is a list of formulas. The text is the record's. */
function rules(block: string[]): string {
  const groups: string[][] = [[]];
  for (const line of block) {
    if (line.trim()) groups[groups.length - 1].push(line);
    else if (groups[groups.length - 1].length) groups.push([]);
  }
  return `<div class="rules">${groups.filter(g => g.length).map(g => {
    const bar = g.findIndex(l => /^\s*─{3,}/.test(l));
    if (bar < 0) return formulas(g);
    const name = /\(([^()]+)\)\s*$/.exec(g[bar])?.[1] ?? "";
    // A definition ending in `=`, with its continuation, stays a formula above the rule.
    let first = 0;
    for (let i = 0; i < bar; i++) if (/=\s*$/.test(g[i])) first = i + 2;
    first = Math.min(first, bar);
    const above = g.slice(0, first);
    const premises = g.slice(first, bar).flatMap(parts);
    const conclusion = g.slice(bar + 1);
    return (above.length ? formulas(above) : "") +
      `<div class="infer"><div class="frac"><div class="premises">${premises.map(p => `<span>${math(p)}</span>`).join("")}</div>` +
      `<div class="bar"></div><div class="conclusion">${conclusion.map(l => `<div>${math(l.trim())}</div>`).join("")}</div></div>` +
      (name ? `<span class="rule-name">${esc(name)}</span>` : "") + `</div>`;
  }).join("")}</div>`;
}

function card(r: CommitRecord): string {
  const outcome = r.trailers.get("Outcome") ?? "";
  const out: string[] = [
    `<article class="card" id="c-${r.sha}"><header><div><div class="sha">${r.sha} · ${esc(r.author)}</div>` +
    `<h3>${inline(r.subject)}</h3></div>` +
    (outcome ? `<span class="pill ${OUTCOMES[outcome] ?? "neutral"}">${esc(outcome)}</span>` : "") + `</header>`,
  ];
  const units = words(r, "Units");
  if (units.length) out.push(`<div class="units">${units.map(u => `<span>${esc(u)}</span>`).join("")}</div>`);
  for (const s of r.sections) {
    if (s.name) out.push(`<h4>${esc(s.name)}</h4>`);
    if (s.text.length) out.push(`<p>${inline(s.text.join(" "))}</p>`);
    if (s.block.length) out.push(s.name === "Rule" ? rules(s.block) : `<pre class="code">${esc(s.block.join("\n").trimEnd())}</pre>`);
  }
  const facts = FACTS.flatMap(k => {
    const v = r.trailers.get(k);
    if (v === undefined) return [];
    const shown =
      k === "Parts" ? v.split(/\s+/).map(p => `<span class="chip${/semantics|trust|wire/.test(p) ? " strong" : ""}">${esc(p)}</span>`).join(" ")
      : k === "Tests" && /(^|\s)([+-]|forged:)/.test(v) ? tests(v)
      : k === "Trust" ? `<span class="${v === "none" ? "none" : "trust"}">${esc(v)}</span>`
      : inline(v.replace(/; /g, " · "));
    return `<dt>${k}</dt><dd>${shown}</dd>`;
  });
  if (facts.length) out.push(`<dl class="facts">${facts.join("")}</dl>`);
  const total = r.stat.at(-1);
  if (total !== undefined) {
    out.push(`<details><summary>${esc(total.trim())}</summary><pre class="code">${esc(r.stat.slice(0, -1).join("\n"))}</pre></details>`);
  }
  if (r.coauthors.length) out.push(`<div class="sha">${esc(r.coauthors.join(" · "))}</div>`);
  out.push("</article>");
  return out.join("\n");
}

type Group = { name: string; range?: string; records: CommitRecord[]; files: string[] };

function group(arg: string): Group {
  if (!arg.includes("..")) return { name: arg, records: [readRecord(arg)], files: [] };
  const [base, tip] = arg.split("..");
  const revs = git(["rev-list", "--reverse", "--no-merges", arg]).split("\n").filter(Boolean);
  return {
    name: tip, range: arg, records: revs.map(readRecord),
    files: git(["diff", "--name-only", `${base}...${tip}`]).split("\n").filter(Boolean),
  };
}

function summary(groups: Group[]): string {
  const ranges = groups.filter(g => g.range);
  if (!ranges.length) return "";
  const rows = ranges.map(g => {
    const count = (o: string) => g.records.filter(r => r.trailers.get("Outcome") === o).flatMap(r => words(r, "Units")).length;
    const units = ["verified", "refused", "gap"].map(o => [o, count(o)] as const).filter(([, n]) => n).map(([o, n]) => `${n} ${o}`).join(", ") || "—";
    const list = (key: string, skip = "") => [...new Set(g.records.map(r => r.trailers.get(key) ?? "").filter(v => v && v !== skip))];
    const parts = [...new Set(g.records.flatMap(r => words(r, "Parts")))];
    const trust = list("Trust", "none");
    return `<tr><td><a href="#g-${esc(g.name)}"><code>${esc(g.name)}</code></a></td><td class="num">${g.records.length}</td><td>${units}</td>` +
      `<td>${parts.map(p => `<span class="chip${/semantics|trust|wire/.test(p) ? " strong" : ""}">${esc(p)}</span>`).join(" ")}</td>` +
      `<td>${trust.length ? trust.map(t => `<span class="trust">${esc(t)}</span>`).join(" ") : '<span class="none">none</span>'}</td>` +
      `<td>${list("Wire").map(inline).join("<br>") || '<span class="none">none</span>'}</td>` +
      `<td>${list("Depends").map(inline).join("<br>") || '<span class="none">—</span>'}</td></tr>`;
  });
  const owners = new Map<string, string[]>();
  for (const g of ranges) for (const f of g.files) owners.set(f, [...(owners.get(f) ?? []), g.name]);
  const shared = [...owners].filter(([, gs]) => gs.length > 1).sort();
  return `<section><h2>Branches</h2><div class="table-wrap"><table><thead><tr><th>Branch</th><th>Commits</th><th>Units</th><th>Parts</th><th>New trust</th><th>Wire</th><th>Depends</th></tr></thead><tbody>${rows.join("")}</tbody></table></div>` +
    (shared.length ? `<h4>Files changed by more than one branch</h4><div class="table-wrap"><table><tbody>${shared.map(([f, gs]) => `<tr><td><code>${esc(f)}</code></td><td>${gs.map(esc).join(", ")}</td></tr>`).join("")}</tbody></table></div>` : "") +
    `</section>`;
}

const CSS = `
:root { --bg:#f6f7f5; --surface:#fff; --ink:#1d2422; --muted:#5b6662; --rule:#d9dedb; --accent:#1f6f66; --code-bg:#eef1ef; --math-bg:#f3f1ea;
  --ok:#2e7d4f; --ok-bg:#e3f2e8; --principled:#8a5a12; --principled-bg:#f6ecd9; --gap:#5e6870; --gap-bg:#e8ebed; --neutral:#2b5b9c; --neutral-bg:#e2eaf6;
  --trust:#8b2f4b; --trust-bg:#f6e3ea; --neg:#9a3a2a; --neg-bg:#f7e4df;
  --display:"IBM Plex Serif",Georgia,serif; --body:"IBM Plex Sans","Helvetica Neue",Arial,sans-serif; --mono:"IBM Plex Mono",Menlo,Consolas,monospace; --math:"STIX Two Text","STIX Two Math","STIXGeneral","Cambria Math","Apple Symbols",Georgia,serif; }
@media (prefers-color-scheme: dark) { :root:not([data-theme="light"]) { --bg:#131816; --surface:#1b2220; --ink:#e3e9e6; --muted:#9aa6a1; --rule:#2f3936; --accent:#6cc3b6; --code-bg:#222b28; --math-bg:#24231d;
  --ok:#7fd3a0; --ok-bg:#1f3428; --principled:#e3b46a; --principled-bg:#382c17; --gap:#aab4bb; --gap-bg:#2a3135; --neutral:#8fb3e8; --neutral-bg:#1e2a3d; --trust:#ec97b1; --trust-bg:#3a2029; --neg:#f0a493; --neg-bg:#3a221d; color-scheme:dark } }
:root[data-theme="dark"] { --bg:#131816; --surface:#1b2220; --ink:#e3e9e6; --muted:#9aa6a1; --rule:#2f3936; --accent:#6cc3b6; --code-bg:#222b28; --math-bg:#24231d;
  --ok:#7fd3a0; --ok-bg:#1f3428; --principled:#e3b46a; --principled-bg:#382c17; --gap:#aab4bb; --gap-bg:#2a3135; --neutral:#8fb3e8; --neutral-bg:#1e2a3d; --trust:#ec97b1; --trust-bg:#3a2029; --neg:#f0a493; --neg-bg:#3a221d; color-scheme:dark }
* { box-sizing:border-box } body { margin:0; background:var(--bg); color:var(--ink); font:15px/1.6 var(--body) }
main { max-width:900px; margin:0 auto; padding-inline:20px; padding-block:32px 64px; display:flex; flex-direction:column; gap:22px }
h1 { font:600 32px/1.15 var(--display); margin:0 } h2 { font:600 22px/1.2 var(--display); margin:12px 0 8px; padding-top:12px; border-top:2px solid var(--ink) }
h3 { font:600 19px/1.3 var(--display); margin:2px 0 0; text-wrap:balance }
h4 { font:600 11px/1 var(--body); letter-spacing:.08em; text-transform:uppercase; color:var(--muted); margin:12px 0 4px }
p { margin:2px 0; max-width:72ch } .lede { color:var(--muted) }
code { font:13px/1.5 var(--mono); background:var(--code-bg); padding:1px 4px; border-radius:3px }
pre { margin:4px 0; padding:12px 14px; border-radius:6px; overflow-x:auto }
pre.code { font:13px/1.55 var(--mono); background:var(--code-bg) }
.rules { display:flex; flex-direction:column; gap:14px; background:var(--math-bg); border-left:3px solid var(--accent); border-radius:6px; padding:14px 18px; overflow-x:auto; font:16px/1.6 var(--math) }
.rules sub, .rules sup { font-size:.72em; line-height:0 }
.formulas { display:flex; flex-direction:column; gap:4px }
.formulas .row { display:flex; flex-wrap:wrap; gap:4px 28px } .formulas .row.cont { padding-left:2em }
.infer { display:flex; align-items:center; gap:12px; flex-wrap:wrap }
.frac { display:inline-flex; flex-direction:column; align-items:center; min-width:0 }
.premises { display:flex; flex-wrap:wrap; justify-content:center; gap:4px 26px; padding:0 6px 3px }
.bar { align-self:stretch; border-top:1.5px solid var(--ink) }
.conclusion { padding:3px 6px 0; text-align:center }
.rule-name { font:600 12px/1 var(--body); letter-spacing:.04em; color:var(--accent); white-space:nowrap }
.card { background:var(--surface); border:1px solid var(--rule); border-radius:8px; padding:20px 22px; display:flex; flex-direction:column; gap:6px; min-width:0 }
.card > header { display:flex; justify-content:space-between; gap:12px; align-items:flex-start }
.sha { font:12px/1.4 var(--mono); color:var(--muted) }
.pill { font:600 11px/1 var(--body); letter-spacing:.06em; text-transform:uppercase; padding:6px 9px; border-radius:99px; white-space:nowrap }
.pill.ok { color:var(--ok); background:var(--ok-bg) } .pill.principled { color:var(--principled); background:var(--principled-bg) }
.pill.gap { color:var(--gap); background:var(--gap-bg) } .pill.neutral { color:var(--neutral); background:var(--neutral-bg) }
.units { display:flex; flex-wrap:wrap; gap:6px } .units span { font:12px/1 var(--mono); border:1px solid var(--rule); border-radius:4px; padding:5px 7px }
dl.facts { display:grid; grid-template-columns:max-content minmax(0,1fr); gap:6px 16px; margin:12px 0 0; padding-top:12px; border-top:1px solid var(--rule); font-size:13.5px }
dt { font:600 11px/1.9 var(--body); letter-spacing:.06em; text-transform:uppercase; color:var(--muted) }
dd { margin:0; min-width:0; display:flex; flex-wrap:wrap; gap:5px; align-items:baseline }
.chip { font:500 12px/1 var(--body); border:1px solid var(--rule); border-radius:4px; padding:4px 7px } .chip.strong { color:var(--accent); border-color:var(--accent) }
.trust { color:var(--trust); background:var(--trust-bg); padding:2px 6px; border-radius:4px } .none { color:var(--muted) }
.test { font:12px/1 var(--mono); padding:4px 7px; border-radius:4px }
.test.pos { color:var(--ok); background:var(--ok-bg) } .test.pos::before { content:"✓ " }
.test.neg { color:var(--neg); background:var(--neg-bg) } .test.neg::before { content:"✗ " }
.test.forged { color:var(--principled); background:var(--principled-bg) } .test.forged::before { content:"forged " }
details { margin-top:8px; font-size:13px; color:var(--muted) } summary { cursor:pointer }
.table-wrap { overflow-x:auto; border:1px solid var(--rule); border-radius:8px; background:var(--surface) }
table { border-collapse:collapse; width:100%; font-size:13px } th, td { text-align:left; vertical-align:top; padding:8px 10px; border-bottom:1px solid var(--rule) }
th { font:600 11px/1.2 var(--body); letter-spacing:.06em; text-transform:uppercase; color:var(--muted); white-space:nowrap } td.num { font-variant-numeric:tabular-nums }
a { color:var(--accent) } :focus-visible { outline:2px solid var(--accent); outline-offset:2px }
@media (max-width:520px) { dl.facts { grid-template-columns:minmax(0,1fr) } .card > header { flex-direction:column } }`;

const args = process.argv.slice(2);
const outAt = args.indexOf("--out");
if (outAt < 0 || outAt + 1 >= args.length) throw new Error("usage: commit-records.mts --out <file.html> [--fragment] <rev | base..branch>...");
const outFile = args[outAt + 1];
const fragment = args.includes("--fragment");
const targets = args.filter((a, i) => i !== outAt && i !== outAt + 1 && a !== "--fragment");
const groups = targets.map(group);
const commits = groups.reduce((n, g) => n + g.records.length, 0);
const body = `<main><header><h1>Commit Records</h1><p class="lede">${commits} commit${commits === 1 ? "" : "s"}, rendered from their records.</p></header>
${summary(groups)}
${groups.map(g => (g.range ? `<h2 id="g-${esc(g.name)}"><code>${esc(g.range)}</code></h2>` : "") + g.records.map(card).join("\n")).join("\n")}
</main>`;
const head = `<title>Commit Records</title>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Sans:wght@400;500;600&family=IBM+Plex+Serif:ital,wght@0,500;0,600;1,400&family=IBM+Plex+Mono:wght@400;500&family=STIX+Two+Text:ital,wght@0,400;0,500;1,400&display=swap">
<style>${CSS}</style>`;
writeFileSync(outFile, fragment ? `${head}\n${body}\n`
  : `<!doctype html>\n<html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">\n${head}</head><body>${body}</body></html>\n`);
console.log(outFile);
