#!/usr/bin/env node
/*
 * SKJS coverage: how much of what SKJS accepts in its own test suite this
 * pipeline (parser → OCaml producer → Lean) verifies, and what stops the rest.
 *
 *   node verification/ocaml-producer/skjs-coverage.mts [--skjs] [--only <substr>]
 *        [--out <dir>] [--result <json>] [--width <n>] [--keep]
 *
 * An assessment, never a test: nothing here is asserted, every outcome is a
 * row. `verification/run.sh` does not run it.
 *
 * Corpus. The TypeScript programs SKJS's harness type-checks and states a
 * verdict for (tests/Main.sk and siblings):
 *   - tests/expect-error/*.ts — errors are exactly the `@ts-expect-error` /
 *     `@skjs-expect-error` annotations, each naming the next non-annotation
 *     line (tests/Helpers.sk findExpectErrors); `@skjs-expect-warning` is not
 *     an error.
 *   - tests/ts-conformance/cases/**.ts — errors are the lines the reference
 *     `.errors.txt` lists. `not-supported/` is excluded: it asserts only that
 *     SKJS reports something.
 *   - tests/{callgraph,constprop,deadcode,cfg}/*.ts — their harnesses require
 *     no error at all. `callgraph-unsupported/` asserts errors and is excluded.
 *   - tests/projects/**.ts — expect-error annotations, but under the project's
 *     own tsconfig; a project whose options change what SKJS accepts (strict
 *     off, a truthiness mode, disabled checks) or whose files import each other
 *     is listed and not run (see `projectExcluded`).
 *
 * Units. The pipeline verifies a whole file and reports its first blocker, so a
 * file is split: every top-level value-level statement (a function with a body,
 * a class, a variable statement, top-level code) is a unit, and its derived
 * file holds it and, in source order, every top-level statement it reaches by
 * name, transitively (types, ambient declarations, other functions). A unit is
 * SKJS-accepted when no statement of that closure carries an error line; the
 * unit's own error and a dependency's are recorded apart. With `--skjs`, SKJS
 * itself is run over every derived file (Docker, from the main checkout that
 * holds the built binary: `SKJS_ROOT`, default the repository's main
 * worktree), and its verdict is recorded beside the marker one; a unit SKJS
 * rejects is not counted as accepted. Without `--skjs` the markers alone
 * decide (`skjs: "not-run"`). Every derived file is regenerated under `--out`
 * (default: a directory in the system's temporary directory).
 *
 * Outcome per unit: `verified`, or the first blocker — `source` (the parser's
 * gate), `proposal` (the producer's `unsupported:`), `search`/`check` (Lean
 * found no derivation), or `error` (timeout, crash). The blocker is located:
 * in the unit itself, or in a dependency the closure brought along. Blockers
 * are grouped into language-feature groups by the table `GROUPS` below; an
 * unmatched reason is its own group, named by its text, so a new refusal
 * appears rather than hiding in "other".
 *
 * The result JSON (default `verification/ocaml-producer/skjs-coverage.json`)
 * has one row per unit, the per-group counts, and the totals.
 */
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import { spawnSync } from "node:child_process";
import * as ts from "../tools/node_modules/typescript/dist/ast/index.js";
import { openText, close } from "../tools/fragment-parse.mts";
import { checkApart, type Outcome } from "./check.mts";
import { pooled } from "./run-cases.mts";

const here = import.meta.dirname;
const repo = path.resolve(here, "../..");

/* ------------------------------------------------------------ arguments -- */
const argv = process.argv.slice(2);
const flag = (name: string) => argv.includes(name);
const option = (name: string, fallback: string) => {
  const i = argv.indexOf(name);
  return i >= 0 && argv[i + 1] ? argv[i + 1] : fallback;
};
const outDir = path.resolve(option("--out", path.join(os.tmpdir(), "skjs-coverage")));
const resultPath = path.resolve(option("--result", path.join(here, "skjs-coverage.json")));
const width = Number(option("--width", String(Math.max(2, os.availableParallelism() - 2))));
const only = option("--only", "");

/* --------------------------------------------------------------- corpus -- */
type Source = {
  file: string; // repo-relative
  suite: string;
  /** 1-based lines SKJS reports an error on. */
  errorLines: Set<number>;
};

const ANNOTATION = /^\s*\/\/\s*@(ts-expect-error|skjs-expect-error|skjs-expect-warning)/;
const ERROR_ANNOTATION = /^\s*\/\/\s*@(ts-expect-error|skjs-expect-error)/;

/** The lines the harness expects an error on: each error annotation names the
 * first following line that is not itself an annotation. */
function annotatedLines(text: string): Set<number> {
  const lines = text.split("\n");
  const out = new Set<number>();
  for (let i = 0; i < lines.length; i++) {
    if (!ERROR_ANNOTATION.test(lines[i])) continue;
    let j = i + 1;
    while (j < lines.length && ANNOTATION.test(lines[j])) j++;
    out.add(j + 1);
  }
  return out;
}

function referenceLines(file: string): Set<number> {
  const base = path.basename(file, ".ts");
  const ref = path.join(repo, "tests/ts-conformance/reference", `${base}.errors.txt`);
  const out = new Set<number>();
  if (!fs.existsSync(ref)) return out;
  for (const m of fs.readFileSync(ref, "utf8").matchAll(/^\S+\.ts\((\d+),\d+\): error/gm))
    out.add(Number(m[1]));
  return out;
}

function walk(dir: string): string[] {
  if (!fs.existsSync(dir)) return [];
  return fs.readdirSync(dir, { withFileTypes: true }).flatMap((e) => {
    const p = path.join(dir, e.name);
    return e.isDirectory() ? walk(p) : e.name.endsWith(".ts") && !e.name.endsWith(".d.ts") ? [p] : [];
  }).sort();
}

/** A project is run only when its files stand alone and SKJS judged them
 * under the options the pipeline assumes (strict, default truthiness). */
function projectExcluded(dir: string): string | undefined {
  const files = walk(dir);
  for (const f of files)
    if (/^\s*(import|export)\b[^;]*\bfrom\s/m.test(fs.readFileSync(f, "utf8")))
      return "files import each other (multi-file project)";
  const configs = fs.readdirSync(dir).filter((n) => /^tsconfig.*\.json$/.test(n))
    .map((n) => fs.readFileSync(path.join(dir, n), "utf8")).join("\n");
  if (!configs) return "no tsconfig";
  if (/"strict"\s*:\s*false/.test(configs) || !/"strict"\s*:\s*true/.test(configs) && !/"extends"/.test(configs))
    return "not strict";
  if (/"truthiness"/.test(configs) && !/"truthiness"\s*:\s*"safe"/.test(configs)) return "non-default truthiness";
  if (/"(strictNullChecks|strictFunctionTypes|noImplicitAny|exactOptionalPropertyTypes|noFallthroughCasesInSwitch)"\s*:\s*false/.test(configs))
    return "a strict sub-option disabled";
  if (/"extends"/.test(configs)) return "tsconfig extends another (options not resolved here)";
  return undefined;
}

function corpus(): { sources: Source[]; excluded: { file: string; reason: string }[] } {
  const sources: Source[] = [];
  const excluded: { file: string; reason: string }[] = [];
  const rel = (p: string) => path.relative(repo, p);
  for (const f of walk(path.join(repo, "tests/expect-error")))
    sources.push({ file: rel(f), suite: "expect-error", errorLines: annotatedLines(fs.readFileSync(f, "utf8")) });
  for (const f of walk(path.join(repo, "tests/ts-conformance/cases")))
    sources.push({ file: rel(f), suite: "ts-conformance", errorLines: referenceLines(f) });
  for (const f of walk(path.join(repo, "tests/ts-conformance/not-supported")))
    excluded.push({ file: rel(f), reason: "ts-conformance/not-supported asserts only that SKJS reports an error" });
  for (const suite of ["callgraph", "constprop", "deadcode", "cfg"])
    for (const f of walk(path.join(repo, "tests", suite)))
      sources.push({ file: rel(f), suite, errorLines: new Set() });
  for (const f of walk(path.join(repo, "tests/callgraph-unsupported")))
    excluded.push({ file: rel(f), reason: "callgraph-unsupported asserts errors" });
  const projects = path.join(repo, "tests/projects");
  for (const p of fs.existsSync(projects) ? fs.readdirSync(projects).sort() : []) {
    const dir = path.join(projects, p);
    const why = projectExcluded(dir);
    const config = fs.existsSync(path.join(dir, "tsconfig.json"))
      ? fs.readFileSync(path.join(dir, "tsconfig.json"), "utf8") : "";
    const listed = /"files"\s*:\s*\[([^\]]*)\]/.exec(config)?.[1];
    const excludes = [.../"exclude"\s*:\s*\[([^\]]*)\]/.exec(config)?.[1].matchAll(/"([^"*]+)/g) ?? []]
      .map((m) => m[1].replace(/\/$/, ""));
    for (const f of walk(dir)) {
      const inProject = path.relative(dir, f);
      if (why) excluded.push({ file: rel(f), reason: why });
      else if (listed !== undefined && !listed.includes(inProject))
        excluded.push({ file: rel(f), reason: "not in the project's files: SKJS does not check it" });
      else if (excludes.some((e) => inProject.startsWith(e + "/") || inProject === e))
        excluded.push({ file: rel(f), reason: "excluded by the project's tsconfig: SKJS does not check it" });
      else sources.push({ file: rel(f), suite: "projects", errorLines: annotatedLines(fs.readFileSync(f, "utf8")) });
    }
  }
  return { sources: only ? sources.filter((s) => s.file.includes(only)) : sources, excluded };
}

/* ---------------------------------------------------------------- units -- */
type Stmt = {
  index: number;
  kind: "function" | "class" | "variable" | "statement" | "context" | "prologue";
  names: string[];
  refs: Set<string>;
  text: string;
  startLine: number;
  endLine: number;
};
type Unit = {
  id: string; // file#name
  source: string;
  suite: string;
  name: string;
  kind: Stmt["kind"];
  line: number;
  /** The unit's own statement, and the statements of its derived file in
   * source order. */
  self: number;
  selfNames: string[];
  /** Value-level statements (functions, classes, variables, code) the
   * closure holds besides the unit's own. */
  valueDeps: number;
  closure: number[];
  skjsMarker: "accepted" | "rejected-self" | "rejected-dependency";
  derived?: string;
  /** Derived line ranges of the unit itself, for locating the blocker. */
  selfLines?: [number, number];
};

const hasModifier = (n: ts.Node, kind: ts.SyntaxKind) =>
  !!(n as { modifiers?: ts.NodeArray<ts.ModifierLike> }).modifiers?.some((m) => m.kind === kind);

function bindingNames(n: ts.Node, out: string[]): void {
  if (ts.isIdentifier(n)) out.push(n.text);
  else if (ts.isObjectBindingPattern(n) || ts.isArrayBindingPattern(n))
    for (const e of n.elements) if (ts.isBindingElement(e) && e.name) bindingNames(e.name, out);
}

function declaredNames(s: ts.Statement): string[] {
  const out: string[] = [];
  const named = s as { name?: ts.Node };
  if ((ts.isFunctionDeclaration(s) || ts.isClassDeclaration(s) || ts.isInterfaceDeclaration(s) ||
       ts.isTypeAliasDeclaration(s) || ts.isEnumDeclaration(s) || ts.isModuleDeclaration(s) ||
       ts.isImportEqualsDeclaration(s)) && named.name && ts.isIdentifier(named.name))
    out.push(named.name.text);
  else if (ts.isVariableStatement(s))
    for (const d of s.declarationList.declarations) bindingNames(d.name, out);
  else if (ts.isImportDeclaration(s) && s.importClause) {
    const c = s.importClause;
    if (c.name) out.push(c.name.text);
    const b = c.namedBindings;
    if (b && ts.isNamespaceImport(b)) out.push(b.name.text);
    else if (b && ts.isNamedImports(b)) for (const e of b.elements) out.push(e.name.text);
  }
  return out;
}

/** Every identifier a statement mentions, except member names after a dot or
 * in a member position, which never name a top-level declaration. */
function references(s: ts.Node): Set<string> {
  const out = new Set<string>();
  const visit = (n: ts.Node) => {
    if (ts.isIdentifier(n)) { out.add(n.text); return; }
    if (ts.isPropertyAccessExpression(n)) { visit(n.expression); return; }
    if (ts.isQualifiedName(n)) { visit(n.left); return; }
    if ((ts.isPropertyAssignment(n) || ts.isMethodDeclaration(n) || ts.isPropertyDeclaration(n) ||
         ts.isGetAccessorDeclaration(n) || ts.isSetAccessorDeclaration(n) ||
         n.kind === ts.SyntaxKind.PropertySignature || n.kind === ts.SyntaxKind.MethodSignature ||
         ts.isEnumMember(n)) && (n as { name?: ts.Node }).name) {
      const name = (n as unknown as { name: ts.Node }).name;
      n.forEachChild((c) => { if (c !== name || !ts.isIdentifier(c)) visit(c); });
      return;
    }
    n.forEachChild(visit);
  };
  visit(s);
  return out;
}

function lineOf(text: string, pos: number): number {
  let line = 1;
  for (let i = 0; i < pos && i < text.length; i++) if (text.charCodeAt(i) === 10) line++;
  return line;
}

function statements(file: string): { stmts: Stmt[]; isModule: boolean } {
  const absolute = path.join(repo, file);
  const text = fs.readFileSync(absolute, "utf8");
  const sf = openText(absolute, text);
  let prologue = true;
  let isModule = false;
  const stmts = sf.statements.map((s, index): Stmt => {
    const start = s.getStart(sf);
    const names = declaredNames(s);
    if (ts.isImportDeclaration(s) || ts.isExportDeclaration(s) || ts.isExportAssignment(s) ||
        hasModifier(s, ts.SyntaxKind.ExportKeyword)) isModule = true;
    let kind: Stmt["kind"];
    const ambient = hasModifier(s, ts.SyntaxKind.DeclareKeyword);
    if (prologue && ts.isExpressionStatement(s) && ts.isStringLiteral(s.expression)) kind = "prologue";
    else if (ts.isFunctionDeclaration(s)) kind = s.body && !ambient ? "function" : "context";
    else if (ts.isClassDeclaration(s)) kind = ambient ? "context" : "class";
    else if (ts.isVariableStatement(s)) kind = ambient ? "context" : "variable";
    else if (ts.isInterfaceDeclaration(s) || ts.isTypeAliasDeclaration(s) || ts.isEnumDeclaration(s) ||
             ts.isModuleDeclaration(s) || ts.isImportDeclaration(s) || ts.isImportEqualsDeclaration(s) ||
             ts.isExportDeclaration(s) || ts.isExportAssignment(s)) kind = "context";
    else kind = "statement";
    if (kind !== "prologue") prologue = false;
    return {
      index, kind, names, refs: references(s), text: text.slice(start, s.end),
      startLine: lineOf(text, start), endLine: lineOf(text, s.end),
    };
  });
  return { stmts, isModule };
}

function unitsOf(src: Source): { units: Unit[]; stmts: Stmt[]; isModule: boolean } {
  const { stmts, isModule } = statements(src.file);
  const byName = new Map<string, number[]>();
  for (const s of stmts) for (const n of s.names) byName.set(n, [...(byName.get(n) ?? []), s.index]);
  const erroneous = (s: Stmt) =>
    [...src.errorLines].some((l) => l >= s.startLine && l <= s.endLine);
  const units: Unit[] = [];
  const taken = new Map<string, number>();
  for (const s of stmts) {
    if (s.kind === "context" || s.kind === "prologue") continue;
    // A function's overload signatures, and a merged declaration, go with it.
    const seed = new Set<number>([s.index, ...s.names.flatMap((n) => byName.get(n) ?? [])]);
    const todo = [...seed];
    while (todo.length) {
      const i = todo.pop()!;
      for (const r of stmts[i].refs)
        for (const j of byName.get(r) ?? []) if (!seed.has(j)) { seed.add(j); todo.push(j); }
    }
    for (const p of stmts) if (p.kind === "prologue") seed.add(p.index);
    const closure = [...seed].sort((a, b) => a - b);
    let base = s.names.length ? s.names.join(",") : `${s.kind}@${s.startLine}`;
    const n = taken.get(base) ?? 0;
    taken.set(base, n + 1);
    if (n) base = `${base}#${n + 1}`;
    const self = erroneous(s);
    const dep = closure.some((i) => i !== s.index && erroneous(stmts[i]));
    units.push({
      id: `${src.file}#${base}`, source: src.file, suite: src.suite, name: base, kind: s.kind,
      line: s.startLine, self: s.index, selfNames: s.names, closure,
      valueDeps: closure.filter((i) => i !== s.index && !["context", "prologue"].includes(stmts[i].kind)).length,
      skjsMarker: self ? "rejected-self" : dep ? "rejected-dependency" : "accepted",
    });
  }
  return { units, stmts, isModule };
}

function derive(unit: Unit, stmts: Stmt[], isModule: boolean): string {
  let text = "";
  let line = 1;
  const chunks: string[] = [];
  for (const i of unit.closure) {
    const t = stmts[i].text;
    if (i === unit.self)
      unit.selfLines = [line, line + t.split("\n").length - 1];
    chunks.push(t);
    line += t.split("\n").length + 1;
  }
  // `isModule` is not restored: an `export {}` is itself outside the
  // fragment. A script's names can meet the global library's; the gate reads
  // TypeScript's diagnostics and says so where it happens.
  void isModule;
  text = chunks.join("\n\n") + "\n";
  return text;
}

/* ----------------------------------------------------------------- SKJS -- */
/** SKJS's own verdict on every derived file, from one container invocation.
 * Returns the derived paths it reported an error in, or undefined when SKJS
 * could not be run. */
function skjsVerdicts(files: string[]): Set<string> | undefined {
  const main = process.env.SKJS_ROOT ?? (() => {
    const r = spawnSync("git", ["worktree", "list", "--porcelain"], { cwd: repo, encoding: "utf8" });
    return /^worktree (.+)$/m.exec(r.stdout)?.[1] ?? repo;
  })();
  const bin = process.env.SKJS_BIN ?? "target/host/dev/skjs";
  const image = process.env.DOCKER_IMAGE ?? "skiplabs/skip:latest";
  const skip = process.env.SKIP_DIR ?? path.resolve(main, "../skip");
  const inside = files.map((f) => `/work/corpus/${path.relative(outDir, f)}`);
  const list = path.join(outDir, "skjs-files.txt");
  fs.writeFileSync(list, inside.join("\n") + "\n");
  const r = spawnSync("docker", ["run", "--rm", "-v", `${main}:/work/skjs`, "-v", `${skip}:/work/skip`,
    "-v", `${outDir}:/work/corpus`, "-w", "/work/skjs", image, "sh", "-c",
    `xargs ${bin} check --import-stubs import-stubs < /work/corpus/skjs-files.txt`],
    { encoding: "utf8", maxBuffer: 256 * 1024 * 1024, timeout: 900_000 });
  if (r.error || r.status === null) {
    process.stderr.write(`skjs: not run: ${r.error?.message ?? r.signal}\n`);
    return undefined;
  }
  const output = r.stdout + "\n" + r.stderr;
  fs.writeFileSync(path.join(outDir, "skjs-output.txt"), output);
  const rejected = new Set<string>();
  for (const block of output.split(/(?=^File ")/m)) {
    const named = /^File "([^"]+)"/.exec(block);
    if (named && /^error/m.test(block))
      rejected.add(path.join(outDir, path.relative("/work/corpus", named[1])));
  }
  if (r.status !== 0 && rejected.size === 0) {
    process.stderr.write(`skjs: exit ${r.status} and no error parsed:\n${output.slice(0, 2000)}\n`);
    return undefined;
  }
  return rejected;
}

/* --------------------------------------------------------------- groups -- */
/* A blocker's text is the pipeline's own sentence. Positions and quoted
 * identifiers are dropped so the same refusal groups across units. */
function reason(text: string): string {
  const first = (text.split("\n").find((l) => l.trim()) ?? "unknown").trim();
  return first
    .replace(/^(gate|error|unsupported):\s*/, "")
    .replace(/\s*\((line \d+,? col(umn)? \d+)\)/g, "")
    // A declaration of the checked source is named by its snapshot's path.
    .replace(/ in \/\S*\/source\.ts#\S*/g, " in a declaration of the source")
    .replace(/\bat \[\d+,\d+\)/g, "at _")
    .replace(/: Verification\.Model\.\S*.*$/, "")
    .replace(/\b(missing field|unbound name|unresolved type reference|declarations for|module constant) [\w$]+/g, "$1 _")
    .replace(/(TypeScript reports an error in a declaration of the source): .*/, "$1")
    .replace(/(cannot establish) .*/, "$1 …")
    .replace(/'[^']*'/g, "'_'")
    .replace(/"[^"]*"/g, '"_"')
    .replace(/\s+/g, " ")
    .trim()
    .slice(0, 160);
}

/** Where a blocker lies: in the unit's own statement, or in a statement its
 * closure brought along. Gate refusals name a line, search refusals a span,
 * declaration refusals the declaration; proposal refusals name nothing, and
 * are the unit's own when its closure holds no other value-level statement. */
function locate(detail: string, u: Unit): { where: Row["where"]; at?: string } {
  const text = u.derived && fs.existsSync(u.derived) ? fs.readFileSync(u.derived, "utf8") : "";
  let line: number | undefined;
  const byLine = /\(line (\d+),? col/.exec(detail);
  const bySpan = /\bat \[(\d+),(\d+)\)/.exec(detail);
  const byDecl = /\/source\.ts#([\w$]+)/.exec(detail);
  if (byLine) line = Number(byLine[1]);
  else if (bySpan) line = text.slice(0, Number(bySpan[1])).split("\n").length;
  else if (byDecl) return { where: u.selfNames.includes(byDecl[1]) ? "self" : "dependency", at: `declaration ${byDecl[1]}` };
  else return { where: u.valueDeps === 0 ? "self" : "unknown" };
  const at = (bySpan ? text.slice(Number(bySpan[1]), Number(bySpan[2])) : text.split("\n")[line - 1] ?? "")
    .replace(/\s+/g, " ").trim().slice(0, 120);
  if (!u.selfLines) return { where: "unknown", at };
  return { where: line >= u.selfLines[0] && line <= u.selfLines[1] ? "self" : "dependency", at };
}

/** A blocker's first line, without the snapshot's temporary path. */
function brief(detail: string): string {
  return (detail.split("\n")[0] ?? "").replace(/\/\S*\/ocaml-producer-\w+\/source\.ts/g, "source.ts").slice(0, 300);
}

/* Feature groups: [group, pattern over the phase-prefixed reason]. First match
 * wins; order is specificity, not value. Unmatched reasons are grouped under
 * their own text, so a new refusal shows up rather than hiding in "other". */
const GROUPS: [string, RegExp][] = [
  ["top-level only: no function to verify", /no source functions to verify/],
  ["bigint", /BigInt|non-decimal numeric literal type/],
  ["enums", /EnumDeclaration/],
  ["ambient declarations (declare let/var, overloaded generic functions)", /`declare let` or `declare var`|overloaded generic function|an ambient constant needs/],
  ["switch statements", /SwitchStatement/],
  ["template literals (expressions and types)", /Template(Expression|LiteralType)|FirstTemplateToken/],
  ["library globals as values (Array, Symbol, Error, Promise, Set, Map, Date, JSON, …)", /the global \w+ is not an annotated variable|unbound name/],
  ["relational operators (< <= > >=) and **", /binary operator outside the fragment \((<|<=|>|>=|\*\*|\*\*=)\)/],
  ["unary operators (- + ~ on numbers)", /unary operator outside the fragment/],
  ["in / instanceof / typeof tests", /\((in|instanceof)\)|expression typeof|TypeQuery/],
  ["mutable bindings: evolving let (null, undefined, []), let with neither initializer nor annotation, closure parameter assignment", /has no storage contract|a `let` needs an initializer|module constant _ has no claimed initializer|assignment to immutable binding/],
  ["control-flow forms (else-if, bare return, early return in closures, dead code)", /closure block must return|`else if` and non-block|a bare `return`|statements after (an unconditional )?return|closure returning from a branch/],
  ["loops (for, for-in, for-of forms)", /(ForStatement|ForInStatement)\)|for\.\.\.of/],
  ["exceptions (try/catch/throw)", /TryStatement|ThrowStatement/],
  ["void expression", /VoidExpression/],
  ["destructuring and rest/default parameters", /statement (arrayPattern|pattern)|destructuring parameter|rest elements|array pattern holes|nested patterns|`let` pattern|default parameters|rest parameter needs|ordinary closure parameter/],
  ["object literal members (methods, accessors, spreads)", /expected a plain property|unsupported object member/],
  ["discriminated-union narrowing (a field read after a tag test)", /missing field _/],
  ["classes: modifiers, inheritance, fields, parameter properties, receivers", /class member|class inheritance|extending the standard library|inheritance needs|optional or definitely-assigned class field|parameter property|constructor (statement|parameter)|method receiver|optional, generator or generic method/],
  ["generic classes", /a generic class is outside the fragment/],
  ["generics: constraints, explicit type arguments, rigid types, generic function types", /only `extends boolean`|explicit type arguments are admitted|rigid type nested|union containing rigid types|generic claim checking|closure under a binder|unknown type parameter|generic function types|field read on rigid parameter/],
  ["type forms: literal types, keyof, indexed access, mapped, object, index signatures, intersections, method signatures", /literal type outside|TypeOperator|IndexedAccessType|MappedType|mapped type|ObjectKeyword|index signature|intersection|unsupported method signature|unsupported member in a record type|expected a required mutable field|a record with no field|optional named fields with a string index/],
  ["type aliases and names the declaration reader cannot resolve", /unresolved type reference|unknown type alias|TypeScript found \d+ declarations|TypeScript reports an error/],
  ["optional chaining", /optional property access/],
  ["compound and update assignments (x++, ||=, ??=, a[i] op=)", /expression (update|logicalAssign|nullishAssign|arrayAssign)|only field and local assignments/],
  ["reads on unions/primitives (field/index read on non-object, string keys)", /(field|indexed) read on non-object|record index requires a string key|numeric array key|dynamic string index write/],
  ["value-level && / || (non-boolean operands)", /operator (&&|\|\|)/],
  ["equality against string/boolean literals", /equality requires a null, undefined or numeric singleton/],
  ["await of non-promises and unions (the await bound)", /quantified call does not satisfy the closure's bound: cannot establish/],
  ["calls: overloads, .call, spread arguments, Object.assign, arrow callee", /overloaded call|\.call requires|spread (argument|into)|array literal spreads|Object\.assign|single arrow the arguments can call/],
  ["sloppy (non-strict) code", /sloppy code|must be strict code/],
  ["other source forms", /TypeAssertionExpression|EmptyStatement|ExportDeclaration|missing type annotation|shadowing|duplicate or shadowing|body requires a variable/],
  ["search: no derivation found (evidence search failed)", /evidence search failed/],
  ["search: producer claim differs from the annotation (literal-union parameters, cells)", /claimed (parameter|return) type differs|cell read and write types|declaration intersection has no representable clause/],
];

function groupOf(key: string): string {
  for (const [g, re] of GROUPS) if (re.test(key)) return g;
  return `unclassified: ${key}`;
}

/* ------------------------------------------------------------------ run -- */
type Row = Omit<Unit, "closure" | "derived" | "self" | "selfNames" | "selfLines"> & {
  closureSize: number;
  skjs?: "accepted" | "rejected" | "not-run";
  status?: Outcome["status"];
  phase?: string;
  detail?: string;
  key?: string;
  group?: string;
  where?: "self" | "dependency" | "unknown";
  /** The source text the blocker names, when it names a place. */
  at?: string;
};

async function main() {
  const { sources, excluded } = corpus();
  fs.rmSync(outDir, { recursive: true, force: true });
  fs.mkdirSync(outDir, { recursive: true });
  const units: Unit[] = [];
  const failed: { file: string; reason: string }[] = [];
  for (const src of sources) {
    try {
      const { units: us, stmts, isModule } = unitsOf(src);
      for (const u of us) {
        if (u.skjsMarker !== "accepted") { units.push(u); continue; }
        const slug = `${src.file.replace(/^tests\//, "").replace(/\.ts$/, "").replace(/[^A-Za-z0-9_-]+/g, "_")}__${u.name.replace(/[^A-Za-z0-9_-]+/g, "_")}`;
        const derived = path.join(outDir, `${slug}.ts`);
        fs.writeFileSync(derived, derive(u, stmts, isModule));
        u.derived = derived;
        units.push(u);
      }
    } catch (e) {
      failed.push({ file: src.file, reason: e instanceof Error ? e.message : String(e) });
    }
  }
  close();
  const candidates = units.filter((u) => u.derived);
  process.stderr.write(`corpus: ${sources.length} files, ${units.length} units, ${candidates.length} SKJS-accepted by the markers\n`);

  let skjs: Set<string> | undefined;
  if (flag("--skjs")) skjs = skjsVerdicts(candidates.map((u) => u.derived!));

  const started = Date.now();
  let done = 0;
  const attempt = async (u: Unit) => {
    const t0 = Date.now();
    const o = await checkApart(u.derived!);
    if (!flag("--keep")) fs.rmSync(o.artifacts, { recursive: true, force: true });
    return { o, ms: Date.now() - t0 };
  };
  const outcomes = await pooled(candidates, async (u) => {
    const r = await attempt(u);
    if (++done % 100 === 0) process.stderr.write(`  ${done}/${candidates.length} (${Math.round((Date.now() - started) / 1000)} s)\n`);
    return r;
  }, width);
  // An infrastructure error under load (a step timeout, the compiler's
  // "context canceled") is not an outcome: such a unit is run again, alone.
  for (const [i, settled] of outcomes.entries())
    if (settled.status === "rejected" || settled.value.o.status === "error")
      [outcomes[i]] = await pooled([candidates[i]], attempt, 1);

  const rows: Row[] = units.map((u) => {
    const { closure, derived, self, selfNames, selfLines, ...rest } = u;
    return { ...rest, closureSize: closure.length };
  });
  const byId = new Map(rows.map((r) => [r.id, r]));
  candidates.forEach((u, i) => {
    const row = byId.get(u.id)!;
    row.skjs = skjs === undefined ? "not-run" : skjs.has(u.derived!) ? "rejected" : "accepted";
    const settled = outcomes[i];
    let full = "";
    if (settled.status === "rejected") {
      row.status = "error"; row.phase = "run"; full = String(settled.reason);
    } else {
      const o = settled.value.o;
      row.status = o.status; row.phase = o.phase;
      if (o.status !== "verified") full = o.detail;
    }
    if (row.status !== "verified") {
      row.key = `${row.phase}: ${reason(full)}`;
      row.group = groupOf(row.key);
      const { where, at } = locate(full, u);
      row.where = where;
      if (at) row.at = at;
      row.detail = brief(full);
    }
  });

  const accepted = rows.filter((r) => r.skjsMarker === "accepted" && r.skjs !== "rejected");
  const count = <T,>(xs: T[], f: (x: T) => string) => {
    const m = new Map<string, number>();
    for (const x of xs) m.set(f(x), (m.get(f(x)) ?? 0) + 1);
    return Object.fromEntries([...m].sort((a, b) => b[1] - a[1]));
  };
  const blocked = accepted.filter((r) => r.status !== "verified");
  const summary = {
    corpusFiles: sources.length,
    excludedFiles: excluded.length,
    unreadableFiles: failed.length,
    units: rows.length,
    unitsByMarker: count(rows, (r) => r.skjsMarker),
    skjsConfirmation: count(rows.filter((r) => r.skjs), (r) => r.skjs!),
    accepted: accepted.length,
    verified: accepted.filter((r) => r.status === "verified").length,
    byStatus: count(accepted, (r) => `${r.status} (${r.phase})`),
    bySuite: Object.fromEntries(Object.entries(count(accepted, (r) => r.suite)).map(([s, n]) =>
      [s, { accepted: n, verified: accepted.filter((r) => r.suite === s && r.status === "verified").length }])),
    filesAllVerified: [...new Set(accepted.map((r) => r.source))].filter((f) =>
      accepted.filter((r) => r.source === f).every((r) => r.status === "verified")).length,
    filesWithAccepted: new Set(accepted.map((r) => r.source)).size,
    functions: {
      accepted: accepted.filter((r) => r.kind === "function").length,
      verified: accepted.filter((r) => r.kind === "function" && r.status === "verified").length,
    },
    /* Units whose first blocker is in the group; `self` of them blocked in
     * their own statement, `dependency` in one their closure brought. */
    byGroup: Object.fromEntries(Object.keys(count(blocked, (r) => r.group!)).map((g) => {
      const rs = blocked.filter((r) => r.group === g);
      return [g, { units: rs.length, self: rs.filter((r) => r.where === "self").length,
        dependency: rs.filter((r) => r.where === "dependency").length,
        files: new Set(rs.map((r) => r.source)).size }];
    })),
    /* Reached Lean (parsed and proposed) and refused there: the candidates
     * for an SKJS unsoundness, or for a pipeline incompleteness. */
    reachedButRefused: blocked.filter((r) => r.phase === "search" || r.phase === "check").length,
    byKey: count(accepted.filter((r) => r.status !== "verified"), (r) => r.key!),
  };
  // One row per line, so a rerun's movement reads as a line diff.
  const slim = ({ id, suite, valueDeps, closureSize, ...r }: Row) => r;
  fs.writeFileSync(resultPath, "{\n" +
    `"summary": ${JSON.stringify(summary, null, 1)},\n` +
    `"excluded": [\n${excluded.map((e) => JSON.stringify(e)).join(",\n")}\n],\n` +
    `"failed": ${JSON.stringify(failed)},\n` +
    `"rows": [\n${rows.map((r) => JSON.stringify(slim(r))).join(",\n")}\n]\n}\n`);
  process.stderr.write(`elapsed: ${Math.round((Date.now() - started) / 1000)} s\n`);
  process.stdout.write(`${summary.verified}/${summary.accepted} SKJS-accepted units verified ` +
    `(${summary.units} units in ${summary.corpusFiles} files)\n`);
  for (const [g, n] of Object.entries(summary.byGroup).slice(0, 25))
    process.stdout.write(`  ${String(n.units).padStart(4)} ${String(n.files).padStart(3)} files  ${g}\n`);
  process.stdout.write(`result: ${path.relative(process.cwd(), resultPath)}; derived files: ${outDir}\n`);
}

await main();
