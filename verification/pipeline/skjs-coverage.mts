#!/usr/bin/env node
/*
 * SKJS coverage: how much of what SKJS accepts in its own test suite this
 * pipeline (parser → OCaml producer → Lean) verifies, and what stops the rest.
 *
 *   node verification/pipeline/skjs-coverage.mts [--only <substr>]
 *        [--out <dir>] [--result <json>] [--width <n>] [--keep]
 *
 * An assessment, never a test: nothing here is asserted, every outcome is a
 * row. `verification/test-all.sh` does not run it.
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
 * unit's own error and a dependency's are recorded apart. Selection uses
 * the expected-error annotations. Every derived file is regenerated under `--out`
 * (default: a directory in the system's temporary directory).
 *
 * Each derived file is checked in SKJS's test environment (see `environment`
 * below). A verified run counts for a unit only when it checked the unit's
 * own code (`checkedCode`).
 *
 * Outcome per unit: `verified`, or the first blocker — `source` (the parser's
 * gate), `proposal` (the producer's `unsupported:`), `search`/`check` (Lean
 * found no derivation), or `error` (timeout, crash). The blocker is located:
 * in the unit itself, or in a dependency the closure brought along. Blockers
 * are grouped into language-feature groups by the table `GROUPS` below; an
 * unmatched reason is its own group, named by its text, so a new refusal
 * appears rather than hiding in "other".
 *
 * Each accepted unit also has a class: `verified`, or its refusal's class,
 * `principled`, `gap` or `unexplained`, by the table `CLASSES` below, or
 * `skjs-unsound` for a unit of a confirmed SKJS unsoundness (`SKJS_UNSOUND`).
 *
 * The result JSON (default `verification/pipeline/skjs-coverage.json`)
 * has one row per unit, the per-group and per-class counts, and the totals.
 */
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import { spawnSync } from "node:child_process";
import * as ts from "../tools/node_modules/typescript/dist/ast/index.js";
import { openText, close } from "../tools/fragment-parse.mts";
import { childrenOf, nameOf } from "../tools/syntax.mts";
import { checkApart, type Outcome } from "./verify-source.mts";
import { pooled } from "./run-cases.mts";

const here = import.meta.dirname;
const repo = path.resolve(here, "../..");

/* ------------------------------------------------------------ arguments -- */
const argv = process.argv.slice(2);
for (let i = 0; i < argv.length; i++) {
  const arg = argv[i];
  if (["--only", "--out", "--result", "--width"].includes(arg)) {
    if (!argv[i + 1] || argv[i + 1].startsWith("--")) throw Error(`Missing value for ${arg}`);
    i++;
  } else if (arg !== "--keep") {
    throw Error(`Unknown argument: ${arg}`);
  }
}
const flag = (name: string) => argv.includes(name);
const option = (name: string, fallback: string) => {
  const i = argv.indexOf(name);
  return i >= 0 && argv[i + 1] ? argv[i + 1] : fallback;
};
const outDir = path.resolve(option("--out", path.join(os.tmpdir(), "skjs-coverage")));
const resultPath = path.resolve(option("--result", path.join(here, "skjs-coverage.json")));
// A quarter of the cores by default: several runs, and Lean builds, often
// share the machine. `--width` raises it for a machine to itself.
const width = Number(option("--width", String(Math.max(2, Math.floor(os.availableParallelism() / 4)))));
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
  /** Derived character span of the unit itself, for attributing a verdict. */
  selfSpan?: [number, number];
};

const hasModifier = (n: ts.Node, kind: ts.SyntaxKind) =>
  childrenOf(n, "modifiers").some((m) => m.kind === kind);

function bindingNames(n: ts.Node, out: string[]): void {
  if (ts.isIdentifier(n)) out.push(n.text);
  else if (ts.isObjectBindingPattern(n) || ts.isArrayBindingPattern(n))
    for (const e of n.elements) if (ts.isBindingElement(e) && e.name) bindingNames(e.name, out);
}

function declaredNames(s: ts.Statement): string[] {
  const out: string[] = [];
  const name = nameOf(s);
  if ((ts.isFunctionDeclaration(s) || ts.isClassDeclaration(s) || ts.isInterfaceDeclaration(s) ||
       ts.isTypeAliasDeclaration(s) || ts.isEnumDeclaration(s) || ts.isModuleDeclaration(s) ||
       ts.isImportEqualsDeclaration(s)) && name && ts.isIdentifier(name))
    out.push(name.text);
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
    const name = ts.isPropertyAssignment(n) || ts.isMethodDeclaration(n) || ts.isPropertyDeclaration(n) ||
      ts.isGetAccessorDeclaration(n) || ts.isSetAccessorDeclaration(n) ||
      n.kind === ts.SyntaxKind.PropertySignature || n.kind === ts.SyntaxKind.MethodSignature ||
      ts.isEnumMember(n) ? nameOf(n) : undefined;
    if (name) {
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
    // `;` runs nothing and declares nothing: no unit, as a type declaration is none.
    else if (ts.isEmptyStatement(s)) kind = "context";
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
    for (let i = todo.pop(); i !== undefined; i = todo.pop()) {
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
  let offset = 0;
  const chunks: string[] = [];
  for (const i of unit.closure) {
    const t = stmts[i].text;
    if (i === unit.self) {
      unit.selfLines = [line, line + t.split("\n").length - 1];
      unit.selfSpan = [offset, offset + t.length];
    }
    chunks.push(t);
    line += t.split("\n").length + 1;
    offset += t.length + 2;
  }
  // `isModule` is not restored: an `export {}` is itself outside the
  // fragment. A script's names can meet the global library's; the gate reads
  // TypeScript's diagnostics and says so where it happens.
  void isModule;
  text = chunks.join("\n\n") + "\n";
  return text;
}

/* ---------------------------------------------------------- environment -- */
/* SKJS checks every test with `--import-stubs import-stubs`: a bare import
 * specifier resolves in that directory, and its builtins stub declares the
 * host's globals. The pipeline runs each derived file in a project of its own
 * that extends `skjs-environment/tsconfig.json`, which gives it the same
 * environment: `paths` sends a bare specifier to the stubs, and
 * `skjs-environment.d.ts` restates the builtins the ECMAScript library lacks
 * (`__SKJS_show`, `process`, `Closed<T>`). */
// skjs-environment/skjs-environment.d.ts restates the builtins SKJS's stub declares and the ECMAScript library lacks; each unit's project lists it.
const environmentDir = path.join(here, "skjs-environment");
const projectOf = (derived: string) => derived.replace(/\.ts$/, ".tsconfig.json");
const environment = (derived: string) => ({
  extends: path.join(environmentDir, "tsconfig.json"),
  files: [derived, path.join(environmentDir, "skjs-environment.d.ts")],
});

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
    // A stub is named by its path from the derived file's project.
    .replace(/(\.\.\/)+\S*?\/import-stubs\//g, "import-stubs/")
    .replace(/\bat \[\d+,\d+\)/g, "at _")
    .replace(/: Verification\.Model\.\S*.*$/, "")
    .replace(/\b(missing field|unbound name|unresolved type reference|declarations for|module constant) [\w$]+/g, "$1 _")
    .replace(/(TypeScript reports an error in a declaration of the source): .*/, "$1")
    .replace(/(TypeScript refuses this code too) .*/, "$1")
    .replace(/(cannot establish) .*/, "$1 …")
    // A quoted identifier, never a possessive's apostrophe (`library's`).
    .replace(/(^|[^\w])'[^']*'/g, "$1'_'")
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
  // A failed search's `obligation:` line (verify-source.mts) says what was not
  // established, in source terms: it follows the first line.
  const lines = detail.split("\n");
  const obligation = lines.find((l) => l.startsWith("obligation: "));
  return ((lines[0] ?? "").replace(/\/\S*\/pipeline-\w+\/source\.ts/g, "source.ts")
    .replace(/(\.\.\/)+\S*?\/import-stubs\//g, "import-stubs/").slice(0, 300)) +
    (obligation ? " — " + obligation.slice("obligation: ".length, 400) : "");
}

/* Feature groups: [group, pattern over the phase-prefixed reason]. First match
 * wins; order is specificity, not value. Unmatched reasons are grouped under
 * their own text, so a new refusal shows up rather than hiding in "other". */
const GROUPS: [string, RegExp][] = [
  ["generic contracts requiring an unsupported exact representation", /generic contract (?:at|:)/],
  ["TypeScript refuses the code too (the pipeline follows TypeScript's types)", /TypeScript refuses this code too/],
  ["arrays and open records: `Array.isArray` on `unknown`, `length` of an array read as a record's", /after `Array\.isArray`|array used as a record naming `length`|`length` of a mutable tuple|past the positions of a mutable tuple/],
  ["a non-null assertion on a read at a for...in key after code that may remove the key or change the object read", /non-null assertion on a read at a for\.\.\.in key/],
  ["generic methods: two declarations' instances related", /an instance of a declaration with generic methods at an instance of another/],
  ["implicit index signatures: a record at an index signature (`Closed<T>` read as `T` among them)", /a record at an index signature/],
  ["a named function at a signature binding more parameters, or indifferent to the receiver it requires (its type is its annotated signature)", /a named function where a signature binding more parameters|a function whose `this` is typed where a callback/],
  ["invariance: a writable element or field at a wider one (TypeScript relates them covariantly)", /a mutable array at one of a wider element|an instance at another whose writable field differs/],
  ["tests on a value of a type parameter or `unknown` (no rule narrows a parameter row to its meet `T & number`)", /test on a value of a type parameter or `unknown`|`\?\?` on a value of a type parameter/],
  ["cells read at their contract (contents known only as primitives or as no `undefined`, and forgotten across a step that may write them)", /a `let` holding an object read where it must be assigned|a cell read at its contract|a field read at its contract/],
  ["dictionaries: a spread of one, a key `in` found in one", /a spread of a dictionary|a read of a key `in` found in a dictionary/],
  ["bigint", /BigInt|non-decimal numeric literal type/],
  ["enums", /EnumDeclaration|enum member|an ambient enum|an enum without members/],
  ["ambient declarations (declare let/var, overloaded generic functions)", /`declare let` or `declare var`|overloaded generic function|an ambient constant needs/],
  ["switch statements", /SwitchStatement/],
  ["template literals (expressions and types)", /Template(Expression|LiteralType)|FirstTemplateToken|is a string pattern/],
  ["library globals as values (Array, Symbol, Error, Promise, Set, Map, Date, JSON, …)", /the global \w+ is not an annotated variable|unbound name|reviewed overlay of library globals|is read only through its members|construct signatures are not read|a callable object with methods needs a combined clause|new Date\(…\) is read/],
  ["relational operators (< <= > >=) and **", /binary operator outside the fragment \((<|<=|>|>=|\*\*|\*\*=)\)|a relational comparison of operands/],
  ["unary operators (- + ~ on numbers)", /unary operator outside the fragment/],
  ["in / instanceof / typeof tests", /\((in|instanceof)\)|expression typeof|TypeQuery|`in` (with|needs|on)|`instanceof`|does not narrow `unknown`/],
  ["mutable bindings: evolving let (null, undefined, []), let with neither initializer nor annotation, closure parameter assignment", /has no storage contract|a `let` needs an initializer|module constant _ has no claimed initializer|assignment to immutable binding|contract does not settle/],
  ["control-flow forms (else-if, bare return, early return in closures, dead code)", /closure block must return|`else if` and non-block|a bare `return`|statements after (an unconditional )?return|closure returning from a branch/],
  ["iterables the program defines: an iterator whose type states no `return`, a spread or a pattern the protocol's lowering does not place, a well-known symbol key other than `Symbol.iterator`", /states no `return`|if it owns one \(IteratorClose\)|a spread of a program|array pattern over a program|well-known symbol key other than/],
  ["generator functions (a body suspended at `yield` is not expressed; the path is a state-machine lowering)", /a generator function is outside/],
  ["loops (for, for-in, for-of forms)", /(ForStatement|ForInStatement)\)|for\.\.\.of/],
  ["exceptions (try/catch/throw)", /TryStatement|ThrowStatement|a jump out of a `try`/],
  ["void expression", /VoidExpression/],
  ["destructuring and rest/default parameters", /statement (arrayPattern|pattern)|destructuring parameter|rest elements|array pattern holes|nested patterns|`let` pattern|default parameters|rest parameter needs|ordinary closure parameter|an array rest needs one|an array pattern over a value|position \d+ is outside the array/],
  ["object growth: a key-adding write on an object another reference may hold, a dynamic index write", /may add (it|the key) to an object another reference holds|a key-adding write|may name `__proto__`, whose setter/],
  ["object literal members (methods, accessors, spreads)", /expected a plain property|unsupported object member|a spread copies the own enumerable|a computed key in an object literal|an accessor runs code|a spread of an object with a symbol-keyed property|a spread with a written field that the arms|an optional field given `undefined`/],
  ["discriminated-union narrowing (a field read after a tag test)", /missing field _|a `let` holding a union of objects|a union of an array and a record/],
  ["classes: modifiers, inheritance, fields, parameter properties, receivers", /class member|class inheritance|extending the standard library|inheritance needs|parameter property|constructor (statement|parameter|assigns)|a static (field|method|member|initializer)|method receiver|method with a `this` parameter|Symbol.hasInstance|#private|class extending|class accessor|index signature in a class|static block|optional, generator or generic method|optional or generator method|generic class method|a class extends/],
  ["generic classes", /a generic class is outside the fragment|reading its own class/],
  ["generics: constraints, explicit type arguments, rigid types, generic function types", /only `extends boolean`|explicit type arguments are admitted|rigid type nested|union containing rigid types|generic claim checking|closure under a binder|unknown type parameter|generic (function|constructor) types|field read on rigid parameter|establish (its|the) declared bound|an argument list is not a runtime value|a quantified closure has no checked instantiation|generic return contract|quantified callable claim encoding|qualified callable requires descriptor scheme checking|read as a value is a resolution-qualified scheme/],
  ["type forms: literal types, keyof, indexed access, mapped, object, index signatures, intersections, method signatures", /literal type outside|TypeOperator|IndexedAccessType|MappedType|mapped type|ObjectKeyword|index signature|intersection|unsupported method signature|unsupported member in a record type|expected a required mutable field|a record with no field|optional named fields with a string index|keyof|the indexed access|typeof [\w.$]+ (is|has)|computes no type for this|unique symbol|computed key|optional method of a nested type literal|an annotation's type literal|construct signatures and other members/],
  ["type aliases and names the declaration reader cannot resolve", /unresolved type reference|unknown type alias|TypeScript found \d+ declarations|TypeScript reports an error/],
  ["optional chaining", /optional property access|an optional call of a method/],
  ["compound and update assignments (x++, ||=, ??=, a[i] op=)", /expression (update|logicalAssign|nullishAssign|arrayAssign)|only field and local assignments|an array assignment pattern writing|(compound|logical) assignment inside a closed expression/],
  ["reads on unions/primitives (field/index read on non-object, string keys)", /(field|indexed) read on non-object|record index requires a string key|numeric array key|dynamic string index write/],
  ["value-level && / || (non-boolean operands)", /operator (&&|\|\|)/],
  ["await of non-promises and unions (the await bound)", /quantified call does not satisfy the closure's bound: cannot establish|an await of a non-promise object|the result of an async function that may be an object|the modeled await requires a native promise or a stably non-thenable value|fresh async resolution requires a stably non-thenable payload/],
  ["calls: overloads, .call, spread arguments, Object.assign, arrow callee", /overloaded call|\.(call|apply|bind) requires|spread (argument|into)|a constructor spread needs|generic spread|array literal spreads|Object\.assign|single arrow the arguments can call|no admitted call signature|read off its object is not a function value|a call writes more positions than its callee/],
  ["sloppy (non-strict) code", /sloppy code|must be strict code/],
  ["other source forms", /TypeAssertionExpression|EmptyStatement|ExportDeclaration|missing type annotation|shadowing|duplicate or shadowing|body requires a variable|unannotated closure parameter/],
  ["receiver types the producer and TypeScript disagree on (a member read on a primitive TypeScript excludes)", /the producer and TypeScript disagree on the receiver/],
  ["search: no derivation found (evidence search failed)", /evidence search failed/],
  ["search: producer claim differs from the annotation (literal-union parameters, cells)", /claimed (parameter|return) type differs|cell read and write types/],
];

function groupOf(key: string): string {
  for (const [g, re] of GROUPS) if (re.test(key)) return g;
  return `unclassified: ${key}`;
}

/* ------------------------------------------------------------- classes -- */
/* Every SKJS-accepted unit is `verified` or refused, and a refusal is one of
 * (SKJS-COVERAGE.md, Method, "Refusal classes"):
 *   - `principled`: the construct is unsound, not faithful to JavaScript, or
 *     rejected by TypeScript itself, or its soundness would need an
 *     assumption the project declines (DESIGN.md "Fragment boundary",
 *     "Refused on principle"); nothing else, and a model's or a
 *     representation's limit never;
 *   - `gap`: a sound construct not yet supported: a lowering not written or a
 *     limit of the model or its representation (DESIGN.md "Fragment
 *     boundary", "Model limits", and "Next steps");
 *   - `unexplained`: no named cause (a failed search, which names the
 *     obligation it could not establish but not why; a crash or timeout);
 *   - `skjs-unsound`: a unit of a confirmed SKJS unsoundness family, with a
 *     runtime witness SKJS accepts and node crashes on (SKJS-COVERAGE.md,
 *     "Suspected SKJS unsoundnesses"); its refusal is correct.
 * A reason is classified by its key (the phase-prefixed normalized reason)
 * and any unit and diagnostic guards; first match wins.
 * Where the judgement is not clear-cut the entry is a gap
 * and `review` says why it could be principled. A key no entry matches is a
 * gap too, listed in `summary.unmatchedReasons`, so a new refusal is seen. */
type RefusalClass = "principled" | "gap" | "unexplained";
type ClassEntry = { cls: RefusalClass; label: string; re: RegExp; why: string; review?: string;
  unit?: string; detail?: RegExp };
const CLASSES: ClassEntry[] = [
  // Reviewed search failures: require both the unit and its observed obligation.
  // A different failure in the same unit falls through to the general classifier.
  { cls: "principled", label: "SKJS closed-object semantics are outside the pipeline",
    unit: "tests/expect-error/json-generated-service.ts#GraphResource",
    re: /^search: reject: source direct obligation at _: GraphCollections: the type argument for EagerCollection/,
    detail: /GraphCollections: the type argument for EagerCollection's "V".*does not establish its declared bound/,
    why: "the environment deliberately reads Closed<T> as T; the resulting open record does not meet the JSON index bound. SKJS's stronger closed-object contract is an intentionally unsupported extension" },
  { cls: "principled", label: "a nested async return annotation requires a promise fulfillment value",
    unit: "tests/expect-error/promise-object.ts#testAwaitNested",
    re: /^search: reject: source expression obligation at _: evidence search failed: no derivation of its return-contract claim$/,
    detail: /The available claim for return await p; is Promise<number>\. This return requires Promise<Promise<number>>\.$/,
    why: "fresh async resolution adopts the returned promise and fulfills with number; Promise<Promise<number>> requires a promise payload under SOURCE-CONTRACTS, Async functions and await" },
  { cls: "gap", label: "a generic contract cannot be represented in full", re: /generic contract (?:at|:)/,
    why: "dependent bounds, mixed binder roles or a recursive quantified family exceed the exact lowering; the contract is refused, not replaced by unknown" },
  { cls: "gap", label: "a callable value has no admitted call signature", re: /no admitted call signature/,
    why: "the type grants callable shape without an invocation promise",
    review: "an explicit Function annotation intentionally grants no call signature; inspect the callee before treating this as a recoverable library gap" },
  // ------------------------------------------------------- unexplained
  { cls: "unexplained", label: "search: no derivation found", re: /evidence search failed|: cannot establish|No rule derives/,
    why: "Lean found no derivation; the obligation is named, its cause is not" },
  { cls: "unexplained", label: "run error or unattributed verification", re: /^\w+: attribution:/,
    why: "no refusal was stated (a crash or timeout is classed here by its status)" },
  // ------------------------------------------------ key-adding write gaps
  { cls: "gap", label: "a key-adding write on an object another reference may hold", re: /may add (it|the key) to an object another reference holds|a key-adding write is typed only on a local's own fresh object/,
    why: "typed only on an unaliased local; alias tracking beyond that is open (DESIGN, Next steps)" },
  { cls: "gap", label: "a write at a runtime string key of an object or `null` value", re: /may name `__proto__`, whose setter/,
    why: "the key may be `__proto__`, whose setter makes such a value the object's prototype; the copy that adds a key adds no prototype" },
  { cls: "gap", label: "a key-adding write at a key that may be a string or a symbol", re: /at a key that may be a string or a symbol/,
    why: "the copy is made onto the object for a string key and onto the key's allocation for a symbol key; one copy does not do both" },
  { cls: "gap", label: "a key-adding write of a symbol key, a spread of a symbol-keyed property", re: /a key-adding write of a symbol key|a spread of an object with a symbol-keyed property/,
    why: "the copy step copies string keys only (Trust surface: JavaScript also copies an own enumerable symbol-keyed property): a symbol key is added to an object whose type lists its keys" },
  { cls: "gap", label: "a spread's written field typed apart by several arms of the expected union with the copy's keys", re: /a spread with a written field that the arms/,
    why: "the copy is allocated per pair of its operands' clauses at the one record the claim gives for it; several arms with the copy's keys typing a written field apart leave no one record" },
  // -------------------------------------------------------- principled
  { cls: "principled", label: "TypeScript refuses the code", re: /TypeScript refuses this code too|TypeScript reports an error in a declaration|which TypeScript rejects|TypeScript computes no type for this typeof: it is not valid TypeScript/,
    why: "TypeScript itself rejects the program or a declaration it depends on" },
  { cls: "principled", label: "an empty intersection", re: /the intersection is empty/,
    why: "no value of the model has both operands' shapes (a branded primitive, a callable array, an array owning a prototype's key): TypeScript keeps such a type, and verifying it would be vacuous (Fragment boundary)" },
  { cls: "principled", label: "`...x: T` with T no array", re: /the array a call collects is no value of a type that is not an array/,
    why: "TypeScript rejects a rest parameter of a non-array type (TS2370)" },
  { cls: "principled", label: "a rest typed by an intersection", re: /one typed by an intersection would view the fresh array/,
    why: "its declared contract can be empty at an instance TypeScript admits: at `T := boolean`, no array is both a writable `boolean[]` and a `number[]` (writable storage is invariant), yet TypeScript accepts `f<boolean>()` for `...xs: T[] & (number[] | string[])`, and a body writing through one operand's view returns a number as a `boolean` (Fragment boundary)" },
  { cls: "principled", label: "a type parameter typing a rest and a value", re: /a type parameter typing a rest parameter and anything else/,
    why: "the array a call collects is fresh: it holds the actuals and none of the parameter's other members, so it is no value of it. TypeScript infers `T := string[] & { tag: string }` from a spread of a tagged array, and `rest<T extends readonly string[]>(...args: T): T { return args }` then returns an array whose `tag` is `undefined` typed `string` (`invalid-rest-pack-value`, run under Node; Fragment boundary)" },
  { cls: "principled", label: "implicit index signature", re: /a record at an index signature/,
    why: "TypeScript's implicit index signature is unsound: a value of a type literal may carry other keys of any type" },
  { cls: "principled", label: "mixed number/bigint arithmetic", re: /number[–-]bigint arithmetic|mixes? (a )?number and (a )?bigint|`\+` on a bigint/,
    why: "JavaScript throws; TypeScript refuses it (Fragment boundary)" },
  { cls: "principled", label: "a base class from outside the file", re: /one from a library, an ambient declaration or a value is outside the fragment|base class declared later/,
    why: "nothing in the file says what its constructor allocates; trusting it is an assumption declined (Fragment boundary)" },
  { cls: "principled", label: "`instanceof` of a constructor from outside the file", re: /`instanceof` whose right operand is not a class declared/,
    why: "nothing in the file says which prototype it gives its instances (Fragment boundary)" },
  { cls: "principled", label: "`instanceof` narrowing `unknown`", re: /does not narrow `unknown` to C/,
    why: "an object gets C's prototype without C's constructor running (`Object.create(C.prototype)`, `Object.setPrototypeOf`, `Reflect.construct`): the brand is no evidence of C's fields, and assuming it of every value a unit receives is false of ordinary JavaScript (Fragment boundary)" },
  { cls: "principled", label: "iterator without a stated `return`", re: /states no `return`|if it owns one \(IteratorClose\)/,
    why: "IteratorClose calls whatever `return` an open record owns (Fragment boundary)" },
  { cls: "principled", label: "`new Array(n)`, holes", re: /new Array\(n\)|makes an array with holes|could create a hole/,
    why: "an array type promises no holes (Fragment boundary)" },
  { cls: "principled", label: "invariance of writable storage", re: /a mutable array at one of a wider element|an instance at another whose writable field differs|a readonly view as a writable/,
    why: "TypeScript relates writable storage covariantly, which is unsound (Fragment boundary)" },
  { cls: "principled", label: "a mutable tuple's `length` at its arity, a position past it", re: /the `length` of a mutable tuple|past the positions of a mutable tuple/,
    why: "`push` is allowed on a mutable tuple: TypeScript's literal length, and its `undefined` past the positions, are unsound" },
  { cls: "principled", label: "method extraction", re: /read off its object is not a function value/,
    why: "a method read off its object loses its receiver; TypeScript's typing of it is unsound (Fragment boundary)" },
  { cls: "principled", label: "a `this`-typed function as a receiver-indifferent callback", re: /a function whose `this` is typed where a callback/,
    why: "the callback type admits any receiver, the function requires its own: TypeScript's relation is unsound" },
  { cls: "principled", label: "method bivariance, narrower overrides", re: /bivarian|narrower parameters/,
    why: "the member may be invoked with the wider argument (Fragment boundary)" },
  { cls: "principled", label: "a contextual `any` parameter", re: /from its context as `any`|TypeScript's `any`/,
    why: "`any` states no contract (Fragment boundary)" },
  { cls: "principled", label: "`this` before `super(...)`", re: /`this` before `super/,
    why: "TypeScript rejects it (TS17009), and JavaScript throws" },
  { cls: "principled", label: "a catch binding typed other than `unknown`", re: /a caught value is `unknown`|catch binding/,
    why: "anything may be thrown: TypeScript admits only `unknown` or `any` there, and `any` states no contract (Fragment boundary)" },
  { cls: "principled", label: "`await` of a non-promise object, an async result that may be an object: thenable adoption", re: /await of a non-promise|a record type does not rule out a `then`|the result of an async function that may be an object|the modeled await requires a native promise or a stably non-thenable value|fresh async resolution requires a stably non-thenable payload/,
    why: "JavaScript adopts thenables and a record type does not rule out `then`, its own or its prototype's: an awaited value is a realm promise or stably non-thenable, a fresh async result's payload stably non-thenable (Fragment boundary)" },
  { cls: "principled", label: "the host runs client code", re: /the host runs client code|`toString`, `valueOf`/,
    why: "the host calls program code (`toString`, an iterator, a reviver) (Fragment boundary)" },
  { cls: "principled", label: "a forged promise (`then` member)", re: /forge|a `then` member/,
    why: "a `Promise<T>` is assumed a realm promise; the source must not forge one (Fragment boundary)" },
  // --------------------------------------------------------------- gap
  // Model and representation limits: sound JavaScript TypeScript accepts,
  // needing no assumption the project declines, which the model cannot state.
  { cls: "gap", label: "a resolution-qualified scheme as a value's type", re: /qualified callable requires descriptor scheme checking|read as a value is a resolution-qualified scheme|resolution-qualified construct scheme/,
    why: "a representation limit: a scheme whose binders carry resolution descriptors has no scheme row a value's type can name (SOURCE-FRAGMENT, Model limits)" },
  { cls: "gap", label: "a computed type over a function's own type parameter", re: /over a type parameter, .* is computed only at an instance|the indexed access .* over a type parameter is computed only at an instance/,
    why: "a model limit: `keyof T` and `T[K]` are functions of the type an instance names (its declared keys, optional and readonly members), and a parameter row denotes a value set, which does not determine a type's key set: no row states them" },
  { cls: "gap", label: "relational comparison of operands not both numbers or both strings", re: /relational comparison (converts|of operands)/,
    why: "a model limit: the model's comparison is of two numbers or two strings; `undefined` or a Boolean converts without running code (to NaN, to 0 or 1), which no rule states (an object's conversion runs code and stays refused, but the refusal does not tell them apart)" },
  { cls: "gap", label: "`this` in sloppy code", re: /a function that reads `this` must be strict code|sloppy code replaces/,
    why: "a model limit: the receiver rule is strict code's; sloppy code's replacement of an undefined or primitive receiver by the global object or a wrapper has no term" },
  { cls: "principled", label: "`extends Array`", re: /extending the standard library's Array/,
    why: "a subclass is its instances' `constructor`, so `map`, `filter` and `slice` construct through it (`ArraySpeciesCreate`): the construction the ordinary array construction assumption excludes (DESIGN, Arrays; Refused on principle)" },
  { cls: "gap", label: "`extends` a library constructor", re: /extending the standard library/,
    why: "a model limit: construction allocates an ordinary object at the class's fields; a library constructor's instance has no construction rule, and its members are read at the library type's meaning" },
  { cls: "gap", label: "an array pattern over a value that may not be an array", re: /an array pattern over a value that may not be an array/,
    why: "a lowering limit: the pattern reads an array's positions; over a host non-array iterable it needs the reads as steps of `%Iterate:K%` (DESIGN, Next steps, Iteration left open)" },
  { cls: "gap", label: "module storage: `declare let`/`var`, a module-level `let`", re: /`declare let` or `declare var`|module-level `let`/,
    why: "a model limit: a unit's module inputs are immutable slots; module storage needs cells every call may write, read at their declared type" },
  { cls: "gap", label: "an ambient enum", re: /an ambient enum is outside/,
    why: "a representation limit: an enum type is its value set, which an ambient declaration need not state, and the declaration reader has no ambient enum value" },
  { cls: "gap", label: "object growth (a key-adding write)", re: /a write adds the property|a write to the optional property|a dynamic index write/,
    why: "sound JavaScript; needs a key-adding write (DESIGN Next steps)" },
  { cls: "gap", label: "a spread of a dictionary", re: /a spread of a dictionary/,
    why: "needs the key-adding write's spread into an index (Next steps)" },
  { cls: "gap", label: "a read at a `for...in` key under `!`", re: /non-null assertion on a read at a for\.\.\.in key/,
    why: "sound where nothing runs between the loop's step and the read: a plain data object inherits no enumerable key (Object.prototype owns none), so the key the loop yields is one the object owns then, at its index's contract; adding it needs a fact relating the key's slot to the object's own keys, which no statement entry states (a relation, as a user guard's is, DESIGN Next steps)" },
  { cls: "gap", label: "a named function at a longer signature", re: /a named function where a signature binding more parameters/,
    why: "sound: a function declaration of fixed arity discards the actuals past its parameters, so its code meets the padded signature (`restsT_of_graph`); its slot is its annotated signature, checked by its own unit, and needs to carry that promise too (the slot a claim its unit checks, as a closure's offered signatures are)" },
  { cls: "gap", label: "`Array.isArray` on `unknown`", re: /used as an array after `Array\.isArray`/,
    why: "the array invariant is a fact of record and dictionary types; `unknown` is also a handler's binding type, and the throw outcome states nothing of a thrown value: needs the throw outcome to carry the invariant (Next steps)" },
  { cls: "gap", label: "an array at a record's `length`", re: /array used as a record naming `length`/,
    why: "needs a readonly `length` view an array meets through its store, at a type admitting every array length, and a dispatch on `Array.isArray` at each such read (Next steps)" },
  { cls: "gap", label: "generic methods: `then` through a callback returning a promise, `catch`", re: /an instance of a declaration with generic methods at an instance of another|a call inferring a binder written beside|a call instantiating a binder its result accumulates/,
    why: "producer inference through an application (a callback returning a promise); an accumulating binder's family is truncated a level early under instantiation (Next steps)" },
  { cls: "gap", label: "a guard finding an object where a field or cell holds one beside a primitive", re: /holding a primitive beside an object|holding an object beside null/,
    why: "what a location is known to hold is a union of primitives, or its contract less `undefined`: a guard's `!== null` of one holding an object states nothing (DESIGN, Current-content assertions); needs a contents fact of its contract less the primitives the guard excludes" },
  { cls: "gap", label: "cells after a step that may write them", re: /a cell read at its contract|a `let` holding an object read where/,
    why: "a call forgets heap facts: needs a reachability statement (Next steps, Precision)" },
  { cls: "gap", label: "an optional field given `undefined`", re: /an optional field given `undefined`/,
    why: "the pipeline reads `f?: T` exactly, as `exactOptionalPropertyTypes` does; TypeScript's default reading, which admits a present `undefined`, is also sound: a reading chosen, not a soundness limit (a class's optional field is read as TypeScript declares it, `f?: T | undefined`)",
    review: "`f?: T | undefined` states it" },
  { cls: "gap", label: "dictionary presence facts", re: /a read of a key `in` found in a dictionary/,
    why: "needs an observation establishing dictionary presence" },
  { cls: "gap", label: "numeric keys and indices", re: /numeric array key|numeric property keys|position \d+ is outside the array|`in` with a key that is not a union|record index requires a string key/,
    why: "a numeric key read where TypeScript's types are not an array and a `number` (the host's `%ElementAt%` reads those): a receiver that may be a record, a key of several numeric literals, which the model reads as array indices only where each is proved one" },
  { cls: "gap", label: "reads the producer holds on no object", re: /(field|indexed) read on non-object|the producer and TypeScript disagree on the receiver/,
    why: "producer typing of the receiver: a bounded binder instantiated at its bound where TypeScript infers an object literal's type" },
  { cls: "gap", label: "a generic or optional method with a `this` parameter", re: /an? (generic|optional) method with a `this` parameter/,
    why: "sound: TypeScript checks the receiver at each call; a generic method's member is a scheme its member bound to the host meets at every receiver, which states no type the host must meet; an optional method is an optional field, whose function takes its declaration as receiver (DESIGN, Model limits)" },
  { cls: "gap", label: "`Symbol.hasInstance`", re: /Symbol\.hasInstance/,
    why: "sound; `instanceof` becomes a call the lowering does not make" },
  { cls: "gap", label: "rest parameters (closure or declaration binder, alias bound)", re: /a rest parameter needs a tuple|rest parameter of a definition/,
    why: "sound forms without a rule: a closure's pack rest (its scheme reads a bound as a meet, and argument lists have no meet row); a rest typed by a class's type parameter inside the class, whose argument lists are a value's elements, which the heap holds and a heap-free argument contract cannot state" },
  { cls: "gap", label: "intersections without a representable clause", re: /an intersection with a union holding a type parameter|the intersection of a function type and a record with|callable with readonly fields|callable with optional fields/,
    why: "a representation limit: a union holding a binder distributes into meets known only at an instance; no clause states a callable with readonly or optional fields, methods or an index" },
  { cls: "gap", label: "`typeof` of inferred bindings, template patterns", re: /the type TypeScript infers for a binding without an annotation|typeof \S+ is a class with static|\$\{string\}|non-decimal numeric literal type|construct signatures and other members|optional named fields with a string index/,
    why: "no term of the fragment states the type exactly (an inferred method, a string pattern): a representation limit" },
  { cls: "gap", label: "generics: generic closures, methods, function types, dependent bounds", re: /generic class method|generic (function|constructor) types|quantified closure|quantified callable|body requires a variable|does not establish (its|the) declared bound|types both a value and a rest parameter|generic spread|a class extending a generic class|method of an annotation's type literal over|call or index signatures applied to a type parameter|`\?\?` on a value of a type parameter|test on a value of a type parameter or `unknown`|field read on rigid parameter/,
    why: "generic closures, generic methods and binders as packs are open (Next steps)" },
  { cls: "gap", label: "class forms: constructor rests and defaults reading `this`, computed members, index signatures, statics, private names", re: /constructor parameter must be plain|constructor parameter default that reads|index signature in a class|computed key|static|private name|#\w+ in/,
    why: "no rule constructs at a variadic construct signature, the instance is allocated at the constructor's end, statics read late, private slots in inheritance (Next steps)" },
  { cls: "gap", label: "enum forms: computed members, an empty enum", re: /computed enum member|an enum without members/,
    why: "keys known only at run time; an empty object has no record: representation limits" },
  { cls: "gap", label: "object literal spreads of class values, arrays, strings", re: /a spread copies the own enumerable/,
    why: "the copy's keys are known only at run time (a string's or an array's indices, which no record states), and the model's class value holds none of JavaScript's own properties (a class's statics are bindings of their own): a merge would copy other than JavaScript does; a representation limit" },
  { cls: "gap", label: "well-known symbol keys", re: /well-known symbol key/,
    why: "the model does not state how the host treats them" },
  { cls: "gap", label: "`.call`, `.apply`, `.bind` of a function value read from an object", re: /\.(call|apply|bind) requires/,
    why: "they are Function.prototype's only by lexical provenance (a local function, whose properties the fragment cannot write): a function value read from an object may own a `call` of its own; needs the caller contract to state that a received function owns none of them (a method's is principled: extraction)" },
  { cls: "gap", label: "a constructor spread without a fixed tuple contract", re: /a constructor spread needs/,
    why: "expansion requires a fixed number of required positions; a variadic construct signature has no construction rule (DESIGN Next steps, Constructor rests)" },
  { cls: "gap", label: "calls: spreads, `Object.assign`, array literal spreads", re: /spread argument|array literal spreads|Object\.assign|a call writes more positions/,
    why: "iteration and call forms left open (Next steps)" },
  { cls: "gap", label: "library globals not reviewed", re: /new Date\(|the global \w+ is not|unbound name|reviewed overlay|a callable object with methods|read only through its members|construct signatures are not read/,
    why: "a library signature is trusted only once reviewed" },
  { cls: "gap", label: "source forms left", re: /only field and local assignments|array assignment pattern writing|compound assignment inside a closed|`let` pattern|for\.\.\.of. loop declares|a jump out of a `try`|assignment to immutable binding|`as const` on an operand|generator function|for await|type guard|assertion function|captured by a closure in a `for`|unresolved type reference|well-known/,
    why: "remaining source forms (Next steps)" },
];

/** The confirmed SKJS unsoundnesses, by unit (`source#name`), each witnessed
 * in SKJS-COVERAGE.md "Suspected SKJS unsoundnesses". */
const SKJS_UNSOUND: Record<string, string> = Object.fromEntries([
  ...["testAliasMutableOptionalThenIndex", "testAliasReadonlyOptionalThenIndex", "testAliasWidenedGrantThenIndex",
      "testSameViewInBranchThenAfter", "testViewInsideLoop", "testAliasMutableSymbolOptionalThenIndex"]
    .map((n) => [`tests/expect-error/obj-literal-indexes.ts#${n}`, "aliased views of an empty object literal"]),
  ["tests/expect-error/obj-literal-indexes.ts#testEscapedInferredLiteralStaysClosed", "an inferred literal type through a generic declaration is closed"],
  ["tests/expect-error/callability.ts#testInstanceTypeofFunction", "`typeof c === \"function\"` on a class instance is `never`"],
  ["tests/expect-error/void.ts#returningConstrainedVoid", "a body falling off its end at a binder bounded by `void`"],
  ["tests/expect-error/promise-object.ts#testAwaitPlainObject", "`await` passes a record through"],
]);

function classOf(key: string, row: Row): ClassEntry | undefined {
  return CLASSES.find((c) => c.re.test(key)
    && (c.unit === undefined || c.unit === row.id)
    && (c.detail === undefined || c.detail.test(row.detail ?? "")));
}

/* ------------------------------------------------------------------ run -- */
/** A verified run speaks for a unit only when it checked the unit's own code:
 * a function unit is one of the functions it verified, any other unit
 * (a class, a variable statement, top-level code) holds a statement of the
 * module initialization it checked. */
function checkedCode(o: Extract<Outcome, { status: "verified" }>, u: Unit): boolean {
  if (u.kind === "function") return o.functions.some((f) => u.selfNames.includes(f));
  const [a, b] = u.selfSpan ?? [0, -1];
  return o.initialization.some(([s, e]) => a <= s && e <= b);
}

type Row = Omit<Unit, "closure" | "derived" | "self" | "selfNames" | "selfLines" | "selfSpan"> & {
  closureSize: number;
  status?: Outcome["status"];
  phase?: string;
  detail?: string;
  key?: string;
  group?: string;
  where?: "self" | "dependency" | "unknown";
  /** The source text the blocker names, when it names a place. */
  at?: string;
  /** An accepted unit's class: verified, or its refusal's (see `CLASSES`). */
  class?: "verified" | RefusalClass | "skjs-unsound";
};

async function main() {
  const { sources, excluded } = corpus();
  fs.rmSync(outDir, { recursive: true, force: true });
  fs.mkdirSync(outDir, { recursive: true });
  // Keep relative imports beside their sources, including transitive imports.
  // Each unit's project lists only its derived file and the environment;
  // the compiler reaches other copied files through imports.
  fs.cpSync(path.join(repo, "tests"), path.join(outDir, "tests"), { recursive: true });
  const units: Unit[] = [];
  const failed: { file: string; reason: string }[] = [];
  for (const src of sources) {
    try {
      const { units: us, stmts, isModule } = unitsOf(src);
      for (const u of us) {
        if (u.skjsMarker !== "accepted") { units.push(u); continue; }
        const slug = `${src.file.replace(/^tests\//, "").replace(/\.ts$/, "").replace(/[^A-Za-z0-9_-]+/g, "_")}__${u.name.replace(/[^A-Za-z0-9_-]+/g, "_")}`;
        const derived = path.join(outDir, path.dirname(src.file), `${slug}.ts`);
        fs.writeFileSync(derived, derive(u, stmts, isModule));
        fs.writeFileSync(projectOf(derived), JSON.stringify(environment(derived), null, 1) + "\n");
        u.derived = derived;
        units.push(u);
      }
    } catch (e) {
      failed.push({ file: src.file, reason: e instanceof Error ? e.message : String(e) });
    }
  }
  close();
  // An accepted unit with the file derived for it, which the pipeline runs.
  const candidates = units.flatMap((u): (Unit & { derived: string })[] => {
    const derived = u.derived;
    return derived === undefined ? [] : [{ ...u, derived }];
  });
  process.stderr.write(`corpus: ${sources.length} files, ${units.length} units, ${candidates.length} SKJS-accepted by the markers\n`);

  // The pipeline runs the producer's built executable: build it from this
  // checkout's sources, so the coverage run measures them.
  const dune = spawnSync("dune", ["build", "--root", path.join(here, "../ocaml-producer")], { stdio: "inherit" });
  if (dune.status !== 0) throw new Error("dune build of the OCaml producer failed");

  const started = Date.now();
  let done = 0;
  const attempt = async (u: Unit & { derived: string }) => {
    const t0 = Date.now();
    const o = await checkApart(u.derived, projectOf(u.derived), true);
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
    const { closure, derived, self, selfNames, selfLines, selfSpan, ...rest } = u;
    return { ...rest, closureSize: closure.length };
  });
  const byId = new Map(rows.map((r) => [r.id, r]));
  candidates.forEach((u, i) => {
    const row = byId.get(u.id);
    if (!row) throw new Error(`no row for the unit ${u.id}`);
    const settled = outcomes[i];
    let full = "";
    if (settled.status === "rejected") {
      row.status = "error"; row.phase = "run"; full = String(settled.reason);
    } else {
      const o = settled.value.o;
      row.status = o.status; row.phase = o.phase;
      // In its project a derived file is named by its own path: name it as
      // `verify-source.mts` names a lone file's snapshot, so a refusal reads the same.
      if (o.status !== "verified") full = o.detail.replaceAll(u.derived, "/pipeline-unit/source.ts");
      else if (!checkedCode(o, u)) {
        row.status = "unverified";
        full = "attribution: the verified run checked none of this unit's own code";
      }
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

  // Classes for the units selected by the expected-error annotations.
  const reasonOf = new Map<string, string>();
  const unmatched = new Set<string>();
  const unsoundVerified: string[] = [];
  for (const row of rows) {
    if (row.skjsMarker !== "accepted") continue;
    if (row.status === "verified") {
      row.class = "verified";
      if (SKJS_UNSOUND[row.id]) unsoundVerified.push(row.id);
      continue;
    }
    if (SKJS_UNSOUND[row.id]) {
      row.class = "skjs-unsound";
      reasonOf.set(row.id, `SKJS unsoundness: ${SKJS_UNSOUND[row.id]}`);
      continue;
    }
    if (row.status === "exhausted") {
      row.class = "gap";
      reasonOf.set(row.id, "subtype execution budget exhausted (inconclusive)");
      continue;
    }
    const key = row.key;
    if (key === undefined) throw new Error(`${row.id}: not verified, with no reason recorded`);
    const entry = row.status === "error" ? CLASSES.find((c) => c.label === "run error or unattributed verification")
      : classOf(key, row);
    if (!entry) unmatched.add(key);
    row.class = entry?.cls ?? "gap";
    reasonOf.set(row.id, entry?.label ?? `unmatched: ${row.key}`);
  }
  for (const id of unsoundVerified)
    process.stderr.write(`warning: ${id}, a confirmed SKJS unsoundness, verified: read it\n`);

  const accepted = rows.filter((r) => r.skjsMarker === "accepted");
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
    byGroup: Object.fromEntries(Object.keys(count(blocked.flatMap((r) => r.group ?? []), (g) => g)).map((g) => {
      const rs = blocked.filter((r) => r.group === g);
      return [g, { units: rs.length, self: rs.filter((r) => r.where === "self").length,
        dependency: rs.filter((r) => r.where === "dependency").length,
        files: new Set(rs.map((r) => r.source)).size }];
    })),
    /* Reached Lean (parsed and proposed) and refused there: the candidates
     * for an SKJS unsoundness, or for a pipeline incompleteness. */
    exhausted: blocked.filter((r) => r.status === "exhausted").length,
    reachedButRefused: blocked.filter((r) => r.phase === "search" || r.phase === "check").length,
    /* Every accepted unit by class (`CLASSES`): verified, refused on
     * principle, a gap, unexplained, or a confirmed SKJS unsoundness. */
    byClass: {
      verified: accepted.filter((r) => r.class === "verified").length,
      principled: accepted.filter((r) => r.class === "principled").length,
      gap: accepted.filter((r) => r.class === "gap").length,
      unexplained: accepted.filter((r) => r.class === "unexplained").length,
      skjsUnsound: accepted.filter((r) => r.class === "skjs-unsound").length,
    },
    /* Unexplained refusals whose failed search carries the reader's
     * `obligation:` line (what was not established, not why). */
    unexplainedWithObligation: accepted.filter((r) => r.class === "unexplained" && / — /.test(r.detail ?? "")).length,
    /* Units by classified reason: [class, label] → units, files. */
    byReason: Object.fromEntries(Object.keys(count(blocked.flatMap((r) => reasonOf.get(r.id) ?? []),
      (label) => label)).map((label) => {
      const rs = blocked.filter((r) => reasonOf.get(r.id) === label);
      return [label, { class: rs[0].class, units: rs.length, files: new Set(rs.map((r) => r.source)).size }];
    })),
    unmatchedReasons: [...unmatched].sort(),
    skjsUnsoundVerified: unsoundVerified,
    byKey: count(accepted.flatMap((r) => r.status !== "verified" ? r.key ?? [] : []), (key) => key),
  };
  // One row per line, so a rerun's movement reads as a line diff.
  const slim = ({ id, suite, valueDeps, closureSize, ...r }: Row) => r;
  fs.writeFileSync(resultPath, "{\n" +
    `"summary": ${JSON.stringify(summary, null, 1)},\n` +
    `"excluded": [\n${excluded.map((e) => JSON.stringify(e)).join(",\n")}\n],\n` +
    `"failed": ${JSON.stringify(failed)},\n` +
    `"rows": [\n${rows.map((r) => JSON.stringify(slim(r))).join(",\n")}\n]\n}\n`);
  process.stderr.write(`elapsed: ${Math.round((Date.now() - started) / 1000)} s\n`);
  process.stdout.write(`${summary.verified}/${summary.accepted} marker-accepted units verified ` +
    `(${summary.units} units in ${summary.corpusFiles} files)\n`);
  const c = summary.byClass;
  process.stdout.write(`${c.verified} verified + ${c.principled + c.skjsUnsound} refused on principle ` +
    `(${c.skjsUnsound} of them SKJS unsoundnesses) = ${c.verified + c.principled + c.skjsUnsound} of ` +
    `${summary.accepted} done; ${c.gap} gaps, ${c.unexplained} unexplained\n`);
  if (summary.unmatchedReasons.length)
    process.stdout.write(`  ${summary.unmatchedReasons.length} reasons no class entry matches (counted as gaps): see summary.unmatchedReasons\n`);
  for (const [g, n] of Object.entries(summary.byGroup).slice(0, 25))
    process.stdout.write(`  ${String(n.units).padStart(4)} ${String(n.files).padStart(3)} files  ${g}\n`);
  process.stdout.write(`result: ${path.relative(process.cwd(), resultPath)}; derived files: ${outDir}\n`);
}

await main();
