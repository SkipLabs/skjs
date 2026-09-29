// Checks the Markdown documents under verification/: that every relative link
// and anchor resolves, that a link naming a section number names the section
// its anchor points at, that math renders with KaTeX and avoids the forms
// GitHub cannot render.
//   node verification/tests/docs.mts
import { readdirSync, readFileSync, existsSync, realpathSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join, relative, resolve } from "node:path";

const root = resolve(import.meta.dirname, "..");
const katex = createRequire(join(root, "tools", "package.json"))("katex") as {
  renderToString(tex: string, options: { displayMode: boolean; throwOnError: boolean; strict: string }): string;
};

/** Directories holding no maintained documents: dependencies, build output and
 * the vendored upstream sources the producer's cases import. */
const excluded = new Set(["node_modules", ".lake", "_build", "upstream", "upstream-sound"]);

/** A symbolic link to a document is that document under another name: it is
 * checked only as a link, whose target must be a document checked here. */
const links: string[] = [];
function markdownFiles(dir: string): string[] {
  return readdirSync(dir, { withFileTypes: true }).flatMap((entry) => {
    if (excluded.has(entry.name)) return [];
    const path = join(dir, entry.name);
    if (entry.isSymbolicLink()) { if (entry.name.endsWith(".md")) links.push(path); return []; }
    if (entry.isDirectory()) return markdownFiles(path);
    return entry.name.endsWith(".md") ? [path] : [];
  });
}

/** The document with code fences removed, math fences kept. */
function withoutCode(text: string): string {
  const out: string[] = [];
  let fence: string | undefined;
  for (const line of text.split("\n")) {
    const opening = /^\s*(```+)(.*)$/.exec(line);
    if (fence === undefined) {
      if (opening) fence = (opening[2] ?? "").trim();
      if (!opening || fence === "math") out.push(line);
    } else if (opening && (opening[2] ?? "").trim() === "") {
      if (fence === "math") out.push(line);
      fence = undefined;
    } else if (fence === "math") out.push(line);
  }
  return out.join("\n");
}

const inlineMath = /\$`([^`]*)`\$/g;
/** Prose: no math, and no inline code. */
function prose(text: string): string {
  return text.replace(/```math\n[\s\S]*?```/g, "").replace(inlineMath, " ").replace(/`[^`\n]*`/g, " ");
}

/** GitHub's heading slug. */
function slug(heading: string): string {
  return heading.trim().toLowerCase().replace(/<[^>]+>/g, "").replace(inlineMath, "$1").replace(/[`*_]/g, "")
    .replace(/\[([^\]]*)\]\([^)]*\)/g, "$1").replace(/[^\p{L}\p{N}\s-]/gu, "").replace(/\s/g, "-");
}

const anchors = new Map<string, Map<string, string>>();
function anchorsOf(file: string): Map<string, string> {
  const known = anchors.get(file);
  if (known) return known;
  const found = new Map<string, string>();
  const seen = new Map<string, number>();
  const text = withoutCode(readFileSync(file, "utf8"));
  for (const m of text.matchAll(/^#{1,6}\s+(.*)$/gm)) {
    const heading = m[1] ?? "";
    const s = slug(heading);
    const n = seen.get(s) ?? 0;
    seen.set(s, n + 1);
    found.set(n ? `${s}-${n}` : s, heading);
  }
  for (const m of text.matchAll(/<a\s+id="([^"]+)"/g)) found.set(m[1] ?? "", "");
  anchors.set(file, found);
  return found;
}

const sectionNumber = (s: string) => s.split(".").map(Number);
function compare(a: number[], b: number[]): number {
  for (let i = 0; i < Math.max(a.length, b.length); i++) {
    const d = (a[i] ?? 0) - (b[i] ?? 0);
    if (d) return d;
  }
  return 0;
}
/** Whether heading number `h` lies in `§n` or `§n–m`, a prefix counting as its section. */
function numbered(text: string, heading: string): boolean {
  const cited = /§\s*([0-9]+(?:\.[0-9]+)*)(?:\s*[–-]\s*([0-9]+(?:\.[0-9]+)*))?/.exec(text);
  const own = /^([0-9]+(?:\.[0-9]+)*)\.?\s/.exec(heading);
  if (!cited || !own) return true;
  const h = sectionNumber(own[1] ?? "");
  const from = sectionNumber(cited[1] ?? "");
  const to = cited[2] ? sectionNumber(cited[2]) : from;
  const within = (n: number[]) => h.length >= n.length ? compare(h.slice(0, n.length), n) : compare(h, n.slice(0, h.length));
  return within(from) >= 0 && within(to) <= 0;
}

/** Forms GitHub's math renderer refuses or garbles (see the global agent notes). */
const unrenderable: [RegExp, string][] = [
  [/\$\$/g, "`$$` display math: use a ```math fence"],
  [/\\operatorname/g, "`\\operatorname`: use `\\mathrm`"],
  [/\\llbracket|\\rrbracket/g, "`\\llbracket`: use ⟦ ⟧"],
  [/\\\(|\\\[/g, "`\\(` or `\\[`: use $`…`$ or a ```math fence"],
];

const files = markdownFiles(root);
const problems: string[] = [];
for (const link of links) {
  const target = existsSync(link) ? realpathSync(link) : undefined;
  if (!target || !files.includes(target))
    problems.push(`${relative(root, link)}: symbolic link to a document this check does not cover`);
}
const fail = (file: string, message: string) => problems.push(`${relative(root, file)}: ${message}`);

for (const file of files) {
  const raw = readFileSync(file, "utf8");
  const text = withoutCode(raw);

  for (const m of prose(text).matchAll(/\[([^\]]*)\]\(([^)\s]+)\)/g)) {
    const [, label = "", url = ""] = m;
    if (/^[a-z]+:/i.test(url)) continue;
    const [path = "", anchor] = url.split("#");
    const target = path ? resolve(dirname(file), decodeURI(path)) : file;
    if (path && !existsSync(target)) { fail(file, `link to missing file ${url}`); continue; }
    if (anchor === undefined || !target.endsWith(".md")) continue;
    const heading = anchorsOf(target).get(decodeURIComponent(anchor));
    if (heading === undefined) fail(file, `link to missing anchor ${url}`);
    else if (!numbered(label, heading)) fail(file, `[${label}] points at "${heading}"`);
  }

  const maths = [...text.matchAll(/```math\n([\s\S]*?)```/g)].map((m): [string, boolean] => [m[1] ?? "", true])
    .concat([...text.matchAll(inlineMath)].map((m): [string, boolean] => [m[1] ?? "", false]));
  for (const [tex, displayMode] of maths) {
    try { katex.renderToString(tex, { displayMode, throwOnError: true, strict: "ignore" }); }
    catch (error) { fail(file, `KaTeX: ${String(error instanceof Error ? error.message : error).split("\n")[0]} in ${tex.replace(/\s+/g, " ").slice(0, 60)}`); }
  }
  const words = prose(text);
  for (const [pattern, remedy] of unrenderable) {
    const count = words.match(pattern)?.length ?? 0;
    if (count) fail(file, `${count}× ${remedy}`);
  }
}

for (const p of problems) process.stdout.write(`${p}\n`);
process.stdout.write(`docs: ${files.length} documents, ${problems.length} problems\n`);
process.exitCode = problems.length ? 1 : 0;
