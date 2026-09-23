import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { tmpdir } from "node:os";
import { createHash } from "node:crypto";
import { resolve } from "node:path";
import { openText, parseFile, definedClassCallables, close as closeParser } from "../tools/fragment-parse.mts";
import { moduleEdges } from "../tools/module-deps.mts";
import { resolveGlobalType, resolveNamedImports, resolveModuleImport } from "../tools/module-resolve.mts";
import { loadImportUniverseFromProject } from "../tools/import-universe-project.mts";
import { crossCheckImports, crossCheckResolvedBindings } from "../tools/import-crosscheck.mts";
import { collectImportDocument, collectTypeClosure } from "../tools/module-closure.mts";
import type { ImportDocument } from "../tools/imported-types.mts";
import { spawnSync } from "node:child_process";
import { check, verifier } from "./check.mts";
import { cases } from "./cases.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";
import { checkGenericRest } from "./generic-rest.mts";
import { checkOverloads } from "./overload-claims.mts";
import { checkDefaults, checkSchemeDefaults, checkEarlyDefault } from "./default-parameters.mts";
// The reader's collector, imported rather than served: `serve.mts` takes the
// port only when it is run directly.
import { analyse } from "../report-viewer/serve.mts";
const here = import.meta.dirname;
{
  const source = join(mkdtempSync(join(tmpdir(), "skjs-reopen-")), "client.ts");
  writeFileSync(source, "function before(): boolean { return true; }\n");
  assert.equal(parseFile(source).functions[0]?.name, "before");
  writeFileSync(source, "function after(): boolean { return false; }\n");
  assert.equal(parseFile(source).functions[0]?.name, "after");
}
let pinnedImportDocument: ImportDocument | null = null;
let recursiveJson = "";
// The framework fixture is the upstream source, including its imports and
// classes. A simplified replacement must not quietly inherit its census row.
for (const [file, expected] of [
  ["examples/reactive-sum-prettier-ignore.ts", "f6463ff031d46252cc2a1442c022ea3d709758233e91607eec9673595ea9e271"],
] as const) {
  assert.equal(createHash("sha256").update(readFileSync(join(here, file))).digest("hex"), expected,
    `${file}: update the upstream provenance and census before replacing this fixture`);
}
{
  const source = resolve(here, "examples/reactive-sum-prettier-ignore.ts");
  assert.deepEqual(definedClassCallables(source).map(c => c.name), [
    "AddIndex.constructor", "AddIndex.mapEntry", "Plus.mapEntry",
    "Minus.mapEntry", "Add.instantiate", "Sub.instantiate",
  ]);
  const edges = moduleEdges(openText(source, readFileSync(source, "utf8")));
  assert.deepEqual(edges.map(({ specifier, imported, typeOnly }) =>
    [specifier, imported, typeOnly]), [
    ["@skipruntime/core", "EagerCollection", true],
    ["@skipruntime/core", "Mapper", true],
    ["@skipruntime/core", "Resource", true],
    ["@skipruntime/core", "Values", true],
    ["@skipruntime/server", "runService", false],
  ]);
  const api = resolve(here, "upstream/skipruntime-ts/core/src/api.ts");
  const transitive = moduleEdges(openText(api, readFileSync(api, "utf8")));
  assert(transitive.some((e) => e.kind === "import" && e.imported === "Json" && e.typeOnly));
  assert(transitive.some((e) => e.kind === "reexport" && e.imported === "deepFreeze" && !e.typeOnly));
  const importUniverse = loadImportUniverseFromProject(resolve(here, "upstream"));
  const { modules, config } = importUniverse;
  const coreIndex = must(modules.find(m => m.id === "core/src/index.ts"), "core index source");
  const apiModule = must(modules.find(m => m.id === "core/src/api.ts"), "core API source");
  const jsonModule = must(modules.find(m => m.id === "skiplang/skjson/ts/binding/src/index.ts"),
    "Json source");
  assert.equal(apiModule.sha256,
    "3bfa83b7c2328f4adda5f0bb54569a46c0d776d93184fdb5eb0e789f4b190909");
  assert.equal(jsonModule.sha256,
    "f1a66edb8c1ee719f867c7202a6edf1bb90bac60dab84914a06ae22ba4ef5ffc");
  assert.equal(config.mappingSources.get("symlink:core/skiplang-json"),
    "skiplang/skjson/ts/binding/src");
  const resolved = resolveNamedImports(openText(source, readFileSync(source, "utf8")),
    modules, config);
  assert.deepEqual(resolved.map(r => [r.binding.local, r.declaration.module,
    r.declaration.name, r.declaration.capability, r.route.map(m => m.module)]), [
    ["EagerCollection", "core/src/api.ts", "EagerCollection", "type",
      ["core/src/index.ts", "core/src/api.ts"]],
    ["Mapper", "core/src/api.ts", "Mapper", "type",
      ["core/src/index.ts", "core/src/api.ts"]],
    ["Resource", "core/src/api.ts", "Resource", "type",
      ["core/src/index.ts", "core/src/api.ts"]],
    ["Values", "core/src/api.ts", "Values", "type",
      ["core/src/index.ts", "core/src/api.ts"]],
    ["runService", "server/src/server.ts", "runService", "value",
      ["server/src/server.ts"]],
  ]);
  const mapperRoot = must(resolved.find(r => r.binding.local === "Mapper"),
    "Mapper import");
  const iterable = resolveGlobalType("Iterable", modules, config);
  assert.equal(iterable?.declaration.module, "typescript/lib/lib.es2015.iterable.d.ts");
  assert.equal(iterable?.declaration.name, "Iterable");
  assert.throws(() => collectTypeClosure(mapperRoot, modules, config),
    /type argument arity: typescript\/lib\/lib.es2015.iterable.d.ts#Iterable/);
  crossCheckResolvedBindings(openText(source, readFileSync(source, "utf8")), resolved,
    modules, source, importUniverse.tsconfigPath);
  const wrongMapper = structuredClone(resolved);
  wrongMapper[1].declaration = wrongMapper[0].declaration;
  assert.throws(() => crossCheckResolvedBindings(openText(source, readFileSync(source, "utf8")),
    wrongMapper, modules, source, importUniverse.tsconfigPath),
    /import resolution differs for Mapper/);
  const wrongService = structuredClone(resolved);
  wrongService[4].declaration = { ...wrongService[4].declaration, span: [0, 0] };
  assert.throws(() => crossCheckResolvedBindings(openText(source, readFileSync(source, "utf8")),
    wrongService, modules, source, importUniverse.tsconfigPath),
    /import resolution differs for runService/);
  const alteredApiText = apiModule.source.getFullText().replace("export interface Mapper<",
    "export interface Mappar<");
  assert.notEqual(alteredApiText, apiModule.source.getFullText());
  const alteredApiModules = modules.map(m => m.id === apiModule.id ? {
    ...m, source: openText(m.source.fileName, alteredApiText),
    sha256: createHash("sha256").update(alteredApiText).digest("hex"),
  } : m);
  assert.throws(() => crossCheckResolvedBindings(openText(source, readFileSync(source, "utf8")),
    resolved, alteredApiModules, source, importUniverse.tsconfigPath),
    /TypeScript source bytes differ for core\/src\/api.ts/);
  assert.throws(() => resolveNamedImports(openText(source, readFileSync(source, "utf8")),
    modules.filter(m => m.id !== "core/src/api.ts"), config), /module not supplied/);
  const duplicate = "export interface Mapper {}\n";
  assert.throws(() => resolveNamedImports(openText(source, readFileSync(source, "utf8")),
    [...modules.filter(m => m.id !== "core/src/errors.ts"), {
      id: "core/src/errors.ts",
      sha256: createHash("sha256").update(duplicate).digest("hex"),
      source: openText(resolve(here, "duplicate-errors.ts"), duplicate),
    }], config), /ambiguous export core\/src\/index.ts#Mapper/);
  const broken = "export { Mapper } from './empty.js';\n";
  const empty = "export const other = 1;\n";
  assert.throws(() => resolveNamedImports(openText(source, readFileSync(source, "utf8")),
    [...modules.filter(m => m.id !== "core/src/errors.ts"), {
      id: "core/src/errors.ts",
      sha256: createHash("sha256").update(broken).digest("hex"),
      source: openText(resolve(here, "broken-errors.ts"), broken),
    }, {
      id: "core/src/empty.ts",
      sha256: createHash("sha256").update(empty).digest("hex"),
      source: openText(resolve(here, "empty.ts"), empty),
    }], config), /broken named reexport core\/src\/errors.ts#Mapper/);
  const jsonPath = resolve(here, "examples/recursive-json.ts");
  const jsonClient = readFileSync(jsonPath, "utf8");
  const jsonImports = resolveNamedImports(openText(jsonPath, jsonClient),
    modules, config);
  assert.deepEqual(jsonImports.map(r => [r.binding.local, r.declaration.module,
    r.declaration.name, r.available, r.route.map(m => m.module)]), [
    ["Json", "skiplang/skjson/ts/binding/src/index.ts", "Json", "type",
      ["core/src/index.ts", "core/src/api.ts", "skiplang/skjson/ts/binding/src/index.ts"]],
    ["JsonObject", "skiplang/skjson/ts/binding/src/index.ts", "JsonObject", "type",
      ["core/src/index.ts", "core/src/api.ts", "skiplang/skjson/ts/binding/src/index.ts"]],
  ]);
  assert.deepEqual(jsonImports.map(r => r.mappings.map(m => m.source)),
    [["symlink:core/skiplang-json"], ["symlink:core/skiplang-json"]]);
  assert.throws(() => resolveNamedImports(openText(jsonPath, jsonClient),
    modules, { ...config, mappingSources: new Map([["symlink:core/skiplang-json", "changed"]]) }),
    /mapping fingerprint differs/);
  const apiJson = resolveModuleImport("core/src/api.ts", "Json", modules, config);
  assert.equal(apiJson?.declaration.module, "skiplang/skjson/ts/binding/src/index.ts");
  assert.equal(resolveModuleImport("core/src/api.ts", "notImported", modules, config), null);
  const jsonClosure = collectTypeClosure(jsonImports[0], modules, config);
  pinnedImportDocument = collectImportDocument(jsonImports, modules, config);
  const wrongReference = structuredClone(pinnedImportDocument);
  const jsonDefinition = wrongReference.definitions.find(d => d.declaration.name === "Json");
  assert(jsonDefinition);
  const objectReference = jsonDefinition.references.find(r => r.name === "JsonObject");
  assert(objectReference);
  objectReference.target = jsonDefinition.declaration;
  assert.throws(() => crossCheckImports(openText(jsonPath, jsonClient), wrongReference,
    modules, jsonPath, importUniverse.tsconfigPath), /import resolution differs.*JsonObject/);
  assert.throws(() => parseFile(jsonPath), /imports need an explicit module universe/);
  const importedAst = parseFile(jsonPath, false, importUniverse);
  assert.deepEqual(importedAst.imports.roots.map(r => r.binding.local), ["Json", "JsonObject"]);
  assert.deepEqual(importedAst.imports.definitions, pinnedImportDocument.definitions);
  assert.deepEqual(importedAst.imports.sources, pinnedImportDocument.sources);
  assert.deepEqual(importedAst.imports.mappings, pinnedImportDocument.mappings);
  const exported = join(mkdtempSync(join(tmpdir(), "skjs-export-")), "client.ts");
  writeFileSync(exported, "export function own(this: undefined): undefined { return this; }\n");
  assert.equal(parseFile(exported).functions[0]?.body[0]?.k, "return");
  writeFileSync(exported, "export async function own(): Promise<boolean> { return true; }\n");
  assert.throws(() => parseFile(exported),
    /only the export modifier is admitted on a source function/);
  const jsonAst = parseFile(jsonPath, false, importUniverse);
  assert.deepEqual(jsonAst.functions.map(f => f.name), ["nest", "lookup"]);
  assert.deepEqual(jsonAst.imports.definitions, pinnedImportDocument.definitions);
  const valuesPath = resolve(here, "examples/recursive-json-values.ts");
  const shadowText = "export type Json = boolean;\n" + coreIndex.source.getFullText();
  const shadowModules = modules.map(m => m.id === coreIndex.id ? {
    ...m,
    sha256: createHash("sha256").update(shadowText).digest("hex"),
    source: openText(m.source.fileName, shadowText),
  } : m);
  assert.throws(() => parseFile(valuesPath, false, { ...importUniverse, modules: shadowModules }),
    /gate:.*import resolution differs for Json/);
  const changedText = jsonModule.source.getFullText().replace("| boolean", "| number ");
  assert.notEqual(changedText, jsonModule.source.getFullText());
  const changedModules = modules.map(m => m.id === jsonModule.id ? {
    ...m,
    sha256: createHash("sha256").update(changedText).digest("hex"),
    source: openText(m.source.fileName, changedText),
  } : m);
  assert.throws(() => parseFile(jsonPath, false, { ...importUniverse, modules: changedModules }),
    /gate:.*TypeScript source bytes differ/);
  const nest = jsonAst.functions[0];
  const lookup = jsonAst.functions[1];
  assert(nest && lookup);
  assert.deepEqual(nest.params[0]?.type.atoms[0], { a: "alias", name: "Json", args: [] });
  assert.deepEqual(lookup.params[0]?.type.atoms[0], { a: "alias", name: "JsonObject", args: [] });
  assert(lookup.retType.atoms.some(atom => atom.a === "alias" && atom.name === "Json"));
  const checkedJson = check(jsonPath, importUniverse);
  recursiveJson = checkedJson.artifacts;
  assert.equal(checkedJson.status, "verified", JSON.stringify(checkedJson));
  assert.equal(checkedJson.phase, "check");
  assert.deepEqual(checkedJson.functions, ["nest", "lookup"]);
  const upstreamConfig = must(importUniverse.tsconfigPath, "upstream tsconfig");
  const typeScript = spawnSync(resolve(here, "../tools/node_modules/.bin/tsc"),
    ["-p", upstreamConfig, "--pretty", "false", "--noEmit"], { encoding: "utf8" });
  assert.ifError(typeScript.error);
  const typeScriptOutput = typeScript.stdout + typeScript.stderr;
  assert.match(typeScriptOutput, /invalid-recursive-json-bound\.ts/,
    "TypeScript must have checked the imported-Json clients");
  assert.doesNotMatch(typeScriptOutput, /invalid-recursive-json-alias-write\.ts/,
    "TypeScript should accept the covariant array assignment that the model refuses");
  const cli = spawnSync(process.execPath, [join(here, "check.mts"), jsonPath,
    "--project", join(here, "upstream")], { encoding: "utf8", timeout: 30_000 });
  assert.ifError(cli.error);
  assert.equal(cli.status, 0, cli.stdout + cli.stderr);
  const cliResult: unknown = JSON.parse(cli.stdout);
  assert.ok(cliResult && typeof cliResult === "object" && "status" in cliResult &&
    "functions" in cliResult && Array.isArray(cliResult.functions));
  assert.equal(cliResult.status, "verified");
  assert.deepEqual(cliResult.functions, ["nest", "lookup"]);
  process.stdout.write("pinned Json imports: 2 functions verified\n");
  const checkedFragment: unknown = JSON.parse(readFileSync(join(checkedJson.artifacts,
    "fragment.json"), "utf8"));
  assert.ok(checkedFragment && typeof checkedFragment === "object" &&
    "imports" in checkedFragment);
  assert.deepEqual(checkedFragment.imports, jsonAst.imports);
  assert.deepEqual(pinnedImportDocument.roots.map(r => r.binding.local), ["Json", "JsonObject"]);
  assert.deepEqual(pinnedImportDocument.definitions.map(d => d.declaration.name),
    ["Json", "JsonObject"]);
  assert.deepEqual(pinnedImportDocument.sources.map(s => s.module), [
    "core/src/api.ts", "core/src/index.ts", "skiplang/skjson/ts/binding/src/index.ts",
  ]);
  assert.deepEqual(pinnedImportDocument.mappings.map(m => m.source), ["symlink:core/skiplang-json"]);
  for (const source of pinnedImportDocument.sources)
    assert.equal(createHash("sha256").update(source.text).digest("hex"), source.sha256);
  for (const mapping of pinnedImportDocument.mappings)
    assert.equal(createHash("sha256").update(mapping.text).digest("hex"), mapping.sha256);
  assert.throws(() => collectImportDocument([
    { ...jsonImports[0], route: [{ ...jsonImports[0].route[0], sha256: "0".repeat(64) },
      ...jsonImports[0].route.slice(1)] },
  ], modules, config), /route fingerprint differs/);
  assert.throws(() => collectImportDocument([
    { ...jsonImports[0], mappings: [{ ...jsonImports[0].mappings[0], sha256: "0".repeat(64) }] },
  ], modules, config), /mapping route differs/);
  assert.deepEqual(jsonClosure.definitions.map(d => [d.declaration.name,
    d.references.map(r => r.target.name)]), [
    ["Json", ["Json", "JsonObject"]],
    ["JsonObject", ["Json"]],
  ]);
  assert(jsonClosure.definitions.every(d =>
    d.declaration.module === "skiplang/skjson/ts/binding/src/index.ts" &&
    d.sha256 === jsonModule.sha256));
  const json = jsonClosure.definitions.find(d => d.declaration.name === "Json");
  const jsonObject = jsonClosure.definitions.find(d => d.declaration.name === "JsonObject");
  assert(json && jsonObject && json.expression.k === "union" &&
    jsonObject.expression.k === "object");
  const array = json.expression.parts.find(p => p.k === "array");
  const objectRef = json.expression.parts.find(p => p.k === "reference" &&
    p.reference.target.name === "JsonObject");
  assert(array && array.k === "array" && array.readonly &&
    array.element.k === "union" && objectRef && objectRef.k === "reference");
  assert(array.element.parts.some(p => p.k === "reference" &&
    p.reference.target.name === "Json" && p.reference.target.module === json.declaration.module));
  assert(array.element.parts.some(p => p.k === "atom" && p.name === "null"));
  const index = jsonObject.expression.stringIndex;
  assert(index && index.readonly && index.value.k === "union");
  assert(index.value.parts.some(p => p.k === "reference" &&
    p.reference.target.name === "Json" && p.reference.target.module === json.declaration.module));
  assert(index.value.parts.some(p => p.k === "atom" && p.name === "null"));
  const a = "import type { B } from './b.js'; export type A<T> = { next: B<T> }; export type Bound<T extends B<number>> = T;";
  const b = "import type { A } from './a.js'; export type B<T> = { prev: A<T> };";
  const pairDir = mkdtempSync(join(tmpdir(), "skjs-generic-import-"));
  writeFileSync(join(pairDir, "a.ts"), a);
  writeFileSync(join(pairDir, "b.ts"), b);
  const barrel = "export type { A } from './a.js';\n";
  writeFileSync(join(pairDir, "barrel.ts"), barrel);
  const box = "export interface Box { readonly flag: boolean; }\n" +
    "export interface FromGlobal { readonly item: GlobalBox; }\n" +
    "export interface Node { readonly next: Node | null; }\n" +
    "export interface CallableBox { readonly invoke: (value: number) => boolean; }\n" +
    "export interface OptionalCallable { readonly invoke: (value?: number) => boolean; }\n" +
    "export interface WithMethod { read(): boolean; }\n" +
    "export interface RestMethod { accepts(...values: number[]): boolean; }\n" +
    "export interface Overloaded { (value: boolean): number; (value: number): boolean; }\n" +
    "export interface TaggedCallable { label: boolean; (value: boolean): number; }\n" +
    "export interface VariadicCallable { (...values: number[]): boolean; }\n" +
    "export type CallableAlias = { (value: number): boolean };\n" +
    "export interface ReadonlyCallable { readonly label: boolean; (value: boolean): number; }\n" +
    "export interface IndexedCallable { readonly [key: string]: boolean; (value: boolean): number; }\n" +
    "export interface GenericCall { <T>(value: T): T; }\n" +
    "export type WithMethodAlias = WithMethod;\n" +
    "export type Pair = [boolean, number];\n" +
    "export type ReadonlyPair = readonly [boolean, number];\n" +
    "export type OptionalPair = [boolean, number?];\n" +
    "export type RestPair = [boolean, ...number[]];\n" +
    "export type NamedPair = [flag: boolean, count: number];\n" +
    "export type NestedMethod = { inner: { read(): boolean } };\n" +
    "export interface GenericMethod { read<T>(value: T): T; }\n" +
    "export interface OptionalMethod { read(value?: boolean): boolean; }\n" +
    "export interface Derived extends Box { readonly label: string; }\n";
  const genericShapes = "export type GenericBox<T> = { readonly value: T };\n" +
    "export type GenericPair<L, R> = { readonly left: L; readonly right: R };\n" +
    "export type GenericOuter<T> = { readonly inner: GenericBox<T> };\n" +
    "export type GenericTuple<T> = readonly [T, number];\n" +
    "export type GenericCallable<T> = (value: T) => T;\n" +
    "export type BoundedBox<T extends boolean> = { readonly value: T };\n";
  writeFileSync(join(pairDir, "box.ts"), box + genericShapes);
  const globalText = "interface GlobalBox { readonly flag: boolean; }\n";
  writeFileSync(join(pairDir, "global.d.ts"), globalText);
  writeFileSync(join(pairDir, "tsconfig.json"), JSON.stringify({
    compilerOptions: { strict: true, noEmit: true, module: "Node16",
      moduleResolution: "Node16", paths: { "@fixture/a": ["./a.ts"],
        "@fixture/barrel": ["./barrel.ts"], "@fixture/box": ["./box.ts"],
        "@fixture/merged": ["./merged.ts"] } },
    include: ["*.ts"],
  }));
  const pair = [
    { id: "fixture/a.ts", sha256: createHash("sha256").update(a).digest("hex"),
      source: openText(join(pairDir, "a.ts"), a) },
    { id: "fixture/b.ts", sha256: createHash("sha256").update(b).digest("hex"),
      source: openText(join(pairDir, "b.ts"), b) },
    { id: "fixture/barrel.ts", sha256: createHash("sha256").update(barrel).digest("hex"),
      source: openText(join(pairDir, "barrel.ts"), barrel) },
    { id: "fixture/box.ts", sha256: createHash("sha256").update(box + genericShapes).digest("hex"),
      source: openText(join(pairDir, "box.ts"), box + genericShapes) },
    { id: "fixture/global.d.ts", sha256: createHash("sha256").update(globalText).digest("hex"),
      source: openText(join(pairDir, "global.d.ts"), globalText) },
  ];
  const pairClient = "import type { A } from '@fixture/a';";
  const pairConfig = { packages: new Map([["@fixture/a", "fixture/a.ts"]]),
    globals: new Set<string>(), links: new Map(), mappingSources: new Map() };
  const pairRoot = resolveNamedImports(openText(join(pairDir, "client.ts"), pairClient),
    pair, pairConfig)[0];
  assert.ok(pairRoot);
  const pairClosure = collectTypeClosure(pairRoot, pair, pairConfig);
  const pairDocument = collectImportDocument([pairRoot], pair, pairConfig);
  assert.deepEqual(pairDocument.sources.map(s => s.module), ["fixture/a.ts", "fixture/b.ts"]);
  assert.equal(pairDocument.mappings.length, 0);
  const genericClient = join(pairDir, "client.ts");
  writeFileSync(genericClient,
    'import type { A } from "@fixture/a";\n' +
    'export function keep(value: A<boolean>): A<boolean> { return value; }\n');
  const genericAst = parseFile(genericClient, false, { modules: pair, config: pairConfig,
    tsconfigPath: join(pairDir, "tsconfig.json") });
  assert.deepEqual(genericAst.functions[0]?.params[0]?.type.atoms[0],
    { a: "alias", name: "A", args: [{ top: false, atoms: [{ a: "boolean" }] }] });
  const recursiveGeneric = check(genericClient, { modules: pair, config: pairConfig,
    tsconfigPath: join(pairDir, "tsconfig.json") });
  assert.equal(recursiveGeneric.status, "unsupported", JSON.stringify(recursiveGeneric));
  assert.equal(recursiveGeneric.phase, "proposal");
  assert.match(recursiveGeneric.detail,
    /recursive generic imported application needs memoized rows/);
  writeFileSync(genericClient,
    'import type { A } from "@fixture/barrel";\n' +
    'export function throughBarrel(value: A<boolean>): A<boolean> { return value; }\n');
  const barrelAst = parseFile(genericClient, false, { modules: pair,
    config: { ...pairConfig, packages: new Map([
      ["@fixture/a", "fixture/a.ts"], ["@fixture/barrel", "fixture/barrel.ts"]]) },
    tsconfigPath: join(pairDir, "tsconfig.json") });
  assert.deepEqual(barrelAst.imports.roots[0]?.route.map(step => step.module),
    ["fixture/barrel.ts", "fixture/a.ts"]);
  const boxClient = join(pairDir, "box-client.ts");
  writeFileSync(boxClient,
    'import type { Box, FromGlobal, Node, CallableBox, OptionalCallable, WithMethod, WithMethodAlias, RestMethod, Overloaded, TaggedCallable, VariadicCallable, CallableAlias, Pair, ReadonlyPair, OptionalPair, RestPair } from "@fixture/box";\n' +
    'export function readBox(box: Box): boolean { return box.flag; }\n' +
    'export function readGlobal(box: FromGlobal): boolean { return box.item.flag; }\n' +
    'export function nextNode(node: Node): Node | null { return node.next; }\n' +
    'export function invokeBox(box: CallableBox): boolean { return box.invoke(1); }\n' +
    'export function omitOptional(box: OptionalCallable): boolean { return box.invoke(); }\n' +
    'export function callMethod(box: WithMethod): boolean { return box.read(); }\n' +
    'export function callMethodAlias(box: WithMethodAlias): boolean { return box.read(); }\n' +
    'export function callRestMethod(box: RestMethod): boolean { return box.accepts(1, 2); }\n' +
    'export function callOverload(fn: Overloaded): number { return fn(true); }\n' +
    'export function callTagged(fn: TaggedCallable): number { return fn(fn.label); }\n' +
    'export function callVariadic(fn: VariadicCallable): boolean { return fn(1, 2); }\n' +
    'export function callAlias(fn: CallableAlias): boolean { return fn(1); }\n' +
    'export function pairFirst(pair: Pair): boolean { return pair[0]; }\n' +
    'export function readonlyPairSecond(pair: ReadonlyPair): number { return pair[1]; }\n' +
    'export function optionalSecond(pair: OptionalPair): number | undefined { return pair[1]; }\n' +
    'export function restHead(pair: RestPair): boolean { return pair[0]; }\n' +
    'export function restTail(pair: RestPair): number | undefined { return pair[1]; }\n');
  const boxConfig = { ...pairConfig, globals: new Set(["fixture/global.d.ts"]), packages: new Map([
    ["@fixture/box", "fixture/box.ts"]]) };
  const boxUniverse = { modules: pair, config: boxConfig,
    tsconfigPath: join(pairDir, "tsconfig.json") };
  const checkedBox = check(boxClient, boxUniverse);
  assert.equal(checkedBox.status, "verified", JSON.stringify(checkedBox));
  assert.deepEqual(checkedBox.functions,
    ["readBox", "readGlobal", "nextNode", "invokeBox", "omitOptional", "callMethod",
      "callMethodAlias", "callRestMethod", "callOverload", "callTagged",
      "callVariadic", "callAlias",
      "pairFirst", "readonlyPairSecond", "optionalSecond", "restHead", "restTail"]);
  const genericShapesClient = join(pairDir, "generic-shapes-client.ts");
  writeFileSync(genericShapesClient,
    'import type { GenericBox, GenericPair, GenericOuter, GenericTuple, GenericCallable } from "@fixture/box";\n' +
    'export function unbox(value: GenericBox<boolean>): boolean { return value.value; }\n' +
    'export function right(value: GenericPair<boolean, number>): number { return value.right; }\n' +
    'export function nested(value: GenericOuter<boolean>): boolean { return value.inner.value; }\n' +
    'export function first(value: GenericTuple<boolean>): boolean { return value[0]; }\n' +
    'export function applied(value: GenericCallable<boolean>): boolean { return value(true); }\n');
  const checkedGenericShapes = check(genericShapesClient, boxUniverse);
  assert.equal(checkedGenericShapes.status, "verified", JSON.stringify(checkedGenericShapes));
  assert.deepEqual(checkedGenericShapes.functions,
    ["unbox", "right", "nested", "first", "applied"]);
  const badGenericShapeClient = join(pairDir, "bad-generic-shape-client.ts");
  writeFileSync(badGenericShapeClient,
    'import type { GenericBox } from "@fixture/box";\n' +
    'export function wrong(value: GenericBox<boolean>): number { return value.value; }\n');
  const rejectedGenericShape = check(badGenericShapeClient, boxUniverse);
  assert.equal(rejectedGenericShape.status, "unverified", JSON.stringify(rejectedGenericShape));
  assert.equal(rejectedGenericShape.phase, "search");
  const boundedShapeClient = join(pairDir, "bounded-shape-client.ts");
  writeFileSync(boundedShapeClient,
    'import type { BoundedBox } from "@fixture/box";\n' +
    'export function bounded(value: BoundedBox<boolean>): boolean { return value.value; }\n');
  const boundedShape = check(boundedShapeClient, boxUniverse);
  assert.equal(boundedShape.status, "unverified", JSON.stringify(boundedShape));
  assert.match(boundedShape.detail, /bounded imported application needs bound verification/);
  const boxAst = parseFile(boxClient, false, boxUniverse);
  assert.equal(boxAst.imports.definitions.find(d => d.declaration.name === "GlobalBox")?.
    declaration.module, "fixture/global.d.ts");
  const alteredGlobalText = globalText.replace("boolean", "unknown");
  const alteredGlobalModules = pair.map(m => m.id === "fixture/global.d.ts" ? {
    ...m, source: openText(m.source.fileName, alteredGlobalText),
    sha256: createHash("sha256").update(alteredGlobalText).digest("hex"),
  } : m);
  assert.throws(() => crossCheckImports(openText(boxClient,
    readFileSync(boxClient, "utf8")), boxAst.imports, alteredGlobalModules,
    boxClient, boxUniverse.tsconfigPath),
  /TypeScript source bytes differ for fixture\/global.d.ts/);
  const duplicateGlobal = "interface GlobalBox { readonly other: number; }\n";
  const secondGlobal = { id: "fixture/other-global.d.ts",
    sha256: createHash("sha256").update(duplicateGlobal).digest("hex"),
    source: openText(join(pairDir, "other-global.d.ts"), duplicateGlobal) };
  assert.throws(() => resolveGlobalType("GlobalBox", [...pair, secondGlobal],
    { ...boxConfig, globals: new Set(["fixture/global.d.ts", secondGlobal.id]) }),
  /ambiguous global type GlobalBox/);
  const badBoxClient = join(pairDir, "bad-box-client.ts");
  writeFileSync(badBoxClient,
    'import type { Box } from "@fixture/box";\n' +
    'export function badBox(box: Box): number { return box.flag; }\n');
  const rejectedBox = check(badBoxClient, boxUniverse);
  assert.equal(rejectedBox.status, "unverified", JSON.stringify(rejectedBox));
  assert.equal(rejectedBox.phase, "search");
  assert.match(rejectedBox.detail, /evidence search failed/);
  const badInvokeClient = join(pairDir, "bad-invoke-client.ts");
  writeFileSync(badInvokeClient,
    'import type { CallableBox } from "@fixture/box";\n' +
    'export function badInvoke(box: CallableBox): number { return box.invoke(1); }\n');
  const rejectedInvoke = check(badInvokeClient, boxUniverse);
  assert.equal(rejectedInvoke.status, "unverified", JSON.stringify(rejectedInvoke));
  assert.equal(rejectedInvoke.phase, "search");
  const detachedClient = join(pairDir, "detached-method-client.ts");
  writeFileSync(detachedClient,
    'import type { WithMethod } from "@fixture/box";\n' +
    'export function detached(box: WithMethod): boolean { const read = box.read; return read(); }\n');
  const detached = check(detachedClient, boxUniverse);
  assert.equal(detached.status, "unverified", JSON.stringify(detached));
  assert.equal(detached.phase, "search");
  assert.match(detached.detail, /method-receiver/);
  const badPairClient = join(pairDir, "bad-pair-client.ts");
  writeFileSync(badPairClient,
    'import type { Pair } from "@fixture/box";\n' +
    'export function badPair(pair: Pair): number { return pair[0]; }\n');
  const rejectedPair = check(badPairClient, boxUniverse);
  assert.equal(rejectedPair.status, "unverified", JSON.stringify(rejectedPair));
  assert.equal(rejectedPair.phase, "search");
  const namedPairRoot = resolveNamedImports(openText(boxClient,
    'import type { NamedPair } from "@fixture/box";'), pair, boxConfig)[0];
  assert(namedPairRoot);
  assert.throws(() => collectTypeClosure(namedPairRoot, pair, boxConfig),
    /named tuple position in fixture\/box.ts#NamedPair/);
  const nestedRoot = resolveNamedImports(openText(boxClient,
    'import type { NestedMethod } from "@fixture/box";'), pair, boxConfig)[0];
  assert(nestedRoot);
  assert.throws(() => collectTypeClosure(nestedRoot, pair, boxConfig),
    /unsupported method signature in fixture\/box.ts#NestedMethod/);
  const genericMethodRoot = resolveNamedImports(openText(boxClient,
    'import type { GenericMethod } from "@fixture/box";'), pair, boxConfig)[0];
  assert(genericMethodRoot);
  assert.throws(() => collectTypeClosure(genericMethodRoot, pair, boxConfig),
    /unsupported method signature in fixture\/box.ts#GenericMethod/);
  const optionalMethodClient = join(pairDir, "optional-method-client.ts");
  writeFileSync(optionalMethodClient,
    'import type { OptionalMethod } from "@fixture/box";\n' +
    'export function callOptional(box: OptionalMethod): boolean { return box.read(); }\n');
  const checkedOptionalMethod = check(optionalMethodClient, boxUniverse);
  assert.equal(checkedOptionalMethod.status, "verified", JSON.stringify(checkedOptionalMethod));
  const wrongRestClient = join(pairDir, "wrong-rest-client.ts");
  writeFileSync(wrongRestClient,
    'import type { RestMethod } from "@fixture/box";\n' +
    'export function wrongRest(box: RestMethod): boolean { return box.accepts("bad"); }\n');
  const rejectedRest = check(wrongRestClient, boxUniverse);
  assert.equal(rejectedRest.status, "unverified", JSON.stringify(rejectedRest));
  assert.equal(rejectedRest.phase, "search");
  const wrongOverloadClient = join(pairDir, "wrong-overload-client.ts");
  writeFileSync(wrongOverloadClient,
    'import type { Overloaded } from "@fixture/box";\n' +
    'export function wrongOverload(fn: Overloaded): boolean { return fn(true); }\n');
  const rejectedOverload = check(wrongOverloadClient, boxUniverse);
  assert.equal(rejectedOverload.status, "unverified", JSON.stringify(rejectedOverload));
  assert.equal(rejectedOverload.phase, "search");
  for (const [name, detail] of [
    ["ReadonlyCallable", /imported callable object with index or readonly field/],
    ["IndexedCallable", /imported callable object with index or readonly field/],
  ] as const) {
    const client = join(pairDir, `unsupported-${name}.ts`);
    writeFileSync(client,
      `import type { ${name} } from "@fixture/box";\n` +
      `export function keep(value: ${name}): ${name} { return value; }\n`);
    const result = check(client, boxUniverse);
    assert.equal(result.status, "unverified", JSON.stringify(result));
    assert.equal(result.phase, "search");
    assert.match(result.detail, detail);
  }
  const genericCallRoot = resolveNamedImports(openText(boxClient,
    'import type { GenericCall } from "@fixture/box";'), pair, boxConfig)[0];
  assert(genericCallRoot);
  assert.throws(() => collectTypeClosure(genericCallRoot, pair, boxConfig),
    /generic or incomplete call signature in fixture\/box.ts#GenericCall/);
  const derivedRoot = resolveNamedImports(openText(boxClient,
    'import type { Derived } from "@fixture/box";'), pair, boxConfig)[0];
  assert(derivedRoot);
  assert.throws(() => collectTypeClosure(derivedRoot, pair, boxConfig),
    /interface inheritance in fixture\/box.ts#Derived is not collected/);
  const merged = "export interface Merge { readonly flag: boolean; }\n" +
    "export interface Merge { readonly label: string; }\n";
  writeFileSync(join(pairDir, "merged.ts"), merged);
  const mergedClient = join(pairDir, "merged-client.ts");
  writeFileSync(mergedClient,
    'import type { Merge } from "@fixture/merged";\n' +
    'export function readMerged(value: Merge): boolean { return value.flag; }\n');
  const mergedModule = { id: "fixture/merged.ts",
    sha256: createHash("sha256").update(merged).digest("hex"),
    source: openText(join(pairDir, "merged.ts"), merged) };
  const mergedConfig = { ...pairConfig,
    packages: new Map([["@fixture/merged", "fixture/merged.ts"]]) };
  assert.throws(() => parseFile(mergedClient, false, { modules: [...pair, mergedModule],
    config: mergedConfig, tsconfigPath: join(pairDir, "tsconfig.json") }),
    /TypeScript found 2 declarations for Merge/);
  writeFileSync(genericClient,
    'import type { A } from "@fixture/a";\n' +
    'export function wrong(value: A<boolean, number>): boolean { return true; }\n');
  assert.throws(() => parseFile(genericClient, false, { modules: pair, config: pairConfig,
    tsconfigPath: join(pairDir, "tsconfig.json") }),
    /imported type 'A' needs 1 type argument/);
  assert.deepEqual(pairClosure.definitions.map(d => [d.declaration.name,
    d.parameters.map(p => p.name), d.references.map(r => [r.target.name, r.arguments.length])]), [
    ["A", ["T"], [["B", 1]]],
    ["B", ["T"], [["A", 1]]],
  ]);
  const aDef = pairClosure.definitions.find(d => d.declaration.name === "A");
  assert(aDef && aDef.expression.k === "object");
  const next = aDef.expression.fields.find(f => f.name === "next");
  assert(next && next.type.k === "reference" && next.type.args[0]?.k === "parameter");
  assert.equal(next.type.reference.target.module, "fixture/b.ts");
  assert.equal(next.type.args[0].index, 0);
  const boundClient = "import type { Bound } from '@fixture/a';";
  const boundRoot = resolveNamedImports(openText(resolve(here, "bound-client.ts"), boundClient),
    pair, pairConfig)[0];
  assert.ok(boundRoot);
  assert.deepEqual(collectTypeClosure(boundRoot, pair, pairConfig).definitions.map(d =>
    [d.declaration.name, d.references.map(r => r.target.name)]), [
    ["Bound", ["B"]], ["B", ["A"]], ["A", ["B"]],
  ]);
  const bound = collectTypeClosure(boundRoot, pair, pairConfig).definitions[0]?.parameters[0]?.bound;
  assert(bound && bound.k === "reference" && bound.args[0]?.k === "atom");
  assert.equal(bound.args[0].name, "number");
  const missing = "export type MissingEdge = NoDefinition;";
  const missingModule = [{ id: "fixture/missing.ts",
    sha256: createHash("sha256").update(missing).digest("hex"),
    source: openText(resolve(here, "fixture-missing.ts"), missing) }];
  const missingConfig = { packages: new Map([["@fixture/missing", "fixture/missing.ts"]]),
    globals: new Set<string>(), links: new Map(), mappingSources: new Map() };
  const missingRoot = resolveNamedImports(openText(resolve(here, "missing-client.ts"),
    "import type { MissingEdge } from '@fixture/missing';"), missingModule, missingConfig)[0];
  assert.ok(missingRoot);
  assert.throws(() => collectTypeClosure(missingRoot, missingModule, missingConfig),
    /unresolved type reference fixture\/missing.ts#NoDefinition/);
  const conditional = "export type Conditional<T> = T extends boolean ? number : string;";
  const conditionalModule = [{ id: "fixture/conditional.ts",
    sha256: createHash("sha256").update(conditional).digest("hex"),
    source: openText(resolve(here, "fixture-conditional.ts"), conditional) }];
  const conditionalRoot = resolveNamedImports(openText(resolve(here, "conditional-client.ts"),
    "import type { Conditional } from '@fixture/conditional';"), conditionalModule,
  { packages: new Map([["@fixture/conditional", "fixture/conditional.ts"]]),
    globals: new Set<string>(), links: new Map(), mappingSources: new Map() })[0];
  assert(conditionalRoot);
  assert.throws(() => collectTypeClosure(conditionalRoot, conditionalModule,
    { packages: new Map([["@fixture/conditional", "fixture/conditional.ts"]]),
      globals: new Set<string>(), links: new Map(), mappingSources: new Map() }),
    /unsupported type syntax ConditionalType/);
  closeParser();
}
function must<T>(value: T | null | undefined, message: string): T {
  assert.ok(value !== null && value !== undefined, message);
  return value;
}
let good = "";
let generic = "";
let genericClosure = "";
let twoCalls = "";
let bounded = "";
let returned = "";
let captured = "";
let callback = "";
let inference = "";
let indexed = "";
let verifiedFunctions = 0;
for (const test of cases) {
  const universe = test.project
    ? loadImportUniverseFromProject(resolve(here, "../..", test.project))
    : undefined;
  const result = check(join(here, "examples", `${test.file}.ts`), universe);
  assert.equal(
    result.status,
    test.status,
    `${test.file}: ${JSON.stringify(result)}`,
  );
  assert.equal(result.phase, test.phase, `${test.file}: wrong boundary`);
  if (test.diagnostic) {
    assert.notEqual(result.status, "verified");
    if (result.status !== "verified")
      assert.match(
        result.detail,
        test.diagnostic,
        `${test.file}: wrong failure`,
      );
  }
  if (result.status === "verified")
    verifiedFunctions += result.functions.length;
  process.stdout.write(
    `${test.file}: ${result.status} (${result.phase}, ${test.kind})\n`,
  );
  if (test.file === "generic-rest") checkGenericRest(verifier, result.artifacts);
  if (test.file === "overloads") checkOverloads(verifier, result.artifacts);
  if (test.file === "values") good = result.artifacts;
  if (test.file === "default-parameter-scope") checkDefaults(verifier, result.artifacts);
  if (test.file === "invalid-default-invocation") checkEarlyDefault(verifier, result.artifacts);
  if (test.file === "generic-default") checkSchemeDefaults(verifier, result.artifacts);
  if (test.file === "generic-inferred") generic = result.artifacts;
  if (test.file === "generic-closure") genericClosure = result.artifacts;
  if (test.file === "generic-two-calls") twoCalls = result.artifacts;
  if (test.file === "generic-bounded") bounded = result.artifacts;
  if (test.file === "generic-returned") returned = result.artifacts;
  if (test.file === "generic-captured-store") captured = result.artifacts;
  if (test.file === "generic-callback") callback = result.artifacts;
  if (test.file === "generic-inference") inference = result.artifacts;
  if (test.file === "index-signature") indexed = result.artifacts;
}
process.stdout.write(
  `${verifiedFunctions} functions verified; ${cases.filter((c) => c.kind === "negative").length} negative controls; ${cases.filter((c) => c.kind === "gap").length} named gaps\n`,
);
// Mutations work on the shared typed wire document. JSON is first checked by
// Lean above; no second hand-maintained SourceClaims shape is introduced here.
const original: SourceClaims = JSON.parse(
  readFileSync(join(good, "claims.json"), "utf8"),
);
const invoke = (claims: string, evidence: string, artifacts = good,
  ast = join(artifacts, "fragment.json")) => {
  const p = spawnSync(
    verifier,
    [
      "--check-source-claims",
      ast,
      claims,
      join(artifacts, "source.ts"),
      evidence,
    ],
    { encoding: "utf8", timeout: 30_000 },
  );
  assert.ifError(p.error);
  assert.equal(p.signal, null);
  assert.equal(p.status, 1, p.stdout + p.stderr);
  // Returned so a caller can assert the refusal is for the intended reason,
  // not merely that something refused.
  return p.stdout + p.stderr;
};
const fragment: unknown = JSON.parse(readFileSync(join(good, "fragment.json"), "utf8"));
assert.ok(fragment && typeof fragment === "object" && !Array.isArray(fragment));
assert.ok("file" in fragment && typeof fragment.file === "string");
{
  const forged = structuredClone(fragment);
  assert.ok("functions" in forged && Array.isArray(forged.functions));
  const first: unknown = forged.functions[0];
  assert.ok(first && typeof first === "object" && "retType" in first);
  first.retType = { top: false, atoms: [{ a: "graph", label: 4 }] };
  const ast = join(good, "raw-graph-conversion.json");
  const claims = join(good, "empty-native-claims.json");
  writeFileSync(ast, JSON.stringify(forged));
  writeFileSync(claims, "[]");
  const converted = spawnSync(verifier,
    ["--export-source-claims", ast, claims, fragment.file], { encoding: "utf8" });
  assert.equal(converted.status, 1);
  assert.match(converted.stderr, /source cannot state an internal graph label/);
  process.stdout.write("raw graph label at native conversion: refused\n");
}
const forgedImport = join(good, "forged-import.json");
writeFileSync(forgedImport, JSON.stringify({ ...fragment,
  imports: must(pinnedImportDocument, "the pinned Json import document") }));
assert.match(invoke(join(good, "claims.json"), join(good, "evidence.json"), good,
  forgedImport), /imported graph rows are missing/);
process.stdout.write("forged import closure: refused\n");
{
  const claims: SourceClaims = JSON.parse(readFileSync(join(recursiveJson, "claims.json"), "utf8"));
  assert.deepEqual(claims.types[4], []);
  claims.types[4] = ["top"];
  const forged = join(recursiveJson, "forged-imported-row.json");
  writeFileSync(forged, JSON.stringify(claims));
  assert.match(invoke(forged, join(recursiveJson, "evidence.json"), recursiveJson),
    /producer supplied an imported declaration equation/);
  process.stdout.write("producer-authored imported equation: refused\n");
}
{
  const ast = readFileSync(join(recursiveJson, "fragment.json"), "utf8");
  const original = '{"a":"alias","name":"Json","args":[]}';
  assert.ok(ast.includes(original));
  const forged = join(recursiveJson, "forged-internal-label.json");
  writeFileSync(forged, ast.replace(original, '{"a":"graph","label":4}'));
  assert.match(invoke(join(recursiveJson, "claims.json"),
    join(recursiveJson, "evidence.json"), recursiveJson, forged),
    /source cannot state an internal graph label/);
  process.stdout.write("source-authored internal graph label: refused\n");
}
const extraField = join(good, "extra-ast-field.json");
writeFileSync(extraField, JSON.stringify({ ...fragment, unexamined: true }));
assert.match(invoke(join(good, "claims.json"), join(good, "evidence.json"), good,
  extraField), /unexpected fields/);
process.stdout.write("unexamined source field: refused\n");
for (const [name, mutate] of new Map<string, (c: SourceClaims) => void>([
  [
    "fingerprint",
    (c) => {
      c.sourceSha256 = "0".repeat(64);
    },
  ],
  [
    "missing-function",
    (c) => {
      c.functions.pop();
    },
  ],
  [
    "false-expression",
    (c) => {
      const e = c.functions[0]?.expressions[0];
      assert.ok(e);
      e.type = [0];
    },
  ],
])) {
  const c = structuredClone(original);
  mutate(c);
  const path = join(good, `${name}.json`);
  writeFileSync(path, JSON.stringify(c));
  invoke(path, join(good, "evidence.json"));
  process.stdout.write(`tampered ${name}: refused\n`);
}
const badEvidence = join(good, "bad-evidence.json");
writeFileSync(badEvidence, "{}");
invoke(join(good, "claims.json"), badEvidence);
process.stdout.write("tampered evidence: refused\n");

// The dynamic-key rule is bound to the actual indexed term, not interchangeable
// with the static-field rule, even when both promise T | undefined.
{
  const evidence = readFileSync(join(indexed, "evidence.json"), "utf8");
  assert.match(evidence, /"indexDict"/);
  const forged = join(indexed, "forged-static-read.json");
  writeFileSync(forged, evidence.replaceAll('"indexDict"', '"readDict"'));
  invoke(join(indexed, "claims.json"), forged, indexed);
  process.stdout.write("tampered dynamic-key rule: refused\n");
}

// The named view remains part of a mixed dictionary's source contract: an
// index-only replacement must not certify a function annotated with both.
{
  const claims: SourceClaims = JSON.parse(readFileSync(join(indexed, "claims.json"), "utf8"));
  const mixed = claims.types.find((row) =>
    row.length === 1 && typeof row[0] === "object" && "dict" in row[0] &&
    row[0].dict.views.some(([name]) => name === "ready"),
  );
  assert(mixed);
  const clause = mixed[0];
  assert(typeof clause === "object" && "dict" in clause);
  clause.dict.views = [];
  const forged = join(indexed, "forged-missing-named-view.json");
  writeFileSync(forged, JSON.stringify(claims));
  assert.match(invoke(forged, join(indexed, "evidence.json"), indexed),
    /claimed parameter type differs from the source annotation/);
  process.stdout.write("tampered mixed dictionary view: refused\n");
}

// A graph certificate for the checked Boolean instance cannot validate a
// narrower first-occurrence proposal after inference has joined both arguments.
{
  const claims: SourceClaims = JSON.parse(readFileSync(join(inference, "claims.json"), "utf8"));
  const joined = must(claims.functions.find(f => f.name === "joinedArguments"), "joined arguments");
  const call = must(joined.expressions.find(e => e.instantiate), "inferred call");
  assert.deepEqual(call.instantiate, [{name: "T", type: [1, 2]}]);
  const upper = must(claims.functions.find(f => f.name === "callbackUpperBounds"), "upper bounds");
  assert.deepEqual(must(upper.expressions.find(e => e.instantiate), "upper call").instantiate,
    [{name: "T", type: [1]}]);
  must(must(call.instantiate, "substitution")[0], "type argument").type = [1];
  call.type = [1];
  const file = join(inference, "forged-first-candidate.json");
  writeFileSync(file, JSON.stringify(claims));
  invoke(file, join(inference, "evidence.json"), inference);
  process.stdout.write("tampered joined inference candidate: refused\n");
}

// A graph certificate for the checked Boolean instance cannot validate a
// different quantified contract. The scheme itself is independently consumed.
const closureClaims: SourceClaims = JSON.parse(
  readFileSync(join(genericClosure, "claims.json"), "utf8"),
);
const closure = closureClaims.functions[0];
assert.ok(closure);
const schemePoint = closure.expressions.find(
  (e) => !Array.isArray(e.type) && "scheme" in e.type,
);
assert.ok(schemePoint && !Array.isArray(schemePoint.type) && "scheme" in schemePoint.type);
schemePoint.type.scheme.result = [1, 2];
const forgedScheme = join(genericClosure, "forged-scheme.json");
writeFileSync(forgedScheme, JSON.stringify(closureClaims));
invoke(forgedScheme, join(genericClosure, "evidence.json"), genericClosure);
process.stdout.write("tampered quantified closure scheme: refused\n");

// A call's substitution is the elimination it proposes, so evidence produced
// for the checked substitutions cannot certify a different one. Retyping the
// second call's type argument leaves one genuine instance of the same scheme,
// which is why the argument — not the universal gate — is what refuses it.
const twoCallClaims: SourceClaims = JSON.parse(
  readFileSync(join(twoCalls, "claims.json"), "utf8"),
);
const instantiated = twoCallClaims.functions[0];
assert.ok(instantiated);
const sites = instantiated.expressions.filter((e) => e.instantiate);
assert.equal(sites.length, 2, "both eliminations must carry a substitution");
for (const [name, mutate] of [
  ["substitution", (s: NonNullable<typeof sites[1]["instantiate"]>) => {
    must(s[0], "the inferred type argument").type = [1, 2];
  }],
  ["substitution domain", (s: NonNullable<typeof sites[1]["instantiate"]>) => {
    must(s[0], "the inferred type argument").name = "U";
  }],
] as const) {
  const claims = structuredClone(twoCallClaims);
  const forged = must(claims.functions[0], "the containing function").expressions.filter((e) => e.instantiate);
  mutate(must(must(forged[1], "the second call").instantiate, "the second substitution"));
  const file = join(twoCalls, `forged-${name.replace(/ /g, "-")}.json`);
  writeFileSync(file, JSON.stringify(claims));
  invoke(file, join(twoCalls, "evidence.json"), twoCalls);
  process.stdout.write(`tampered ${name}: refused\n`);
}

// A substitution is checked against every declared bound before it is
// compiled. Reversing one call's type arguments keeps them ground and complete,
// so the domain check passes and only the bound obligation can refuse it.
const boundedClaims: SourceClaims = JSON.parse(
  readFileSync(join(bounded, "claims.json"), "utf8"),
);
{
  const claims = structuredClone(boundedClaims);
  const call = must(claims.functions[0], "the containing function").expressions.find((e) => e.instantiate);
  assert.ok(call?.instantiate);
  const [u, t] = call.instantiate;
  assert.ok(u && t && u.name === "U" && t.name === "T");
  u.type = [1];
  t.type = [1, 2];
  const file = join(bounded, "forged-bound.json");
  writeFileSync(file, JSON.stringify(claims));
  const said = invoke(file, join(bounded, "evidence.json"), bounded);
  assert.match(said, /does not satisfy the closure's bound: cannot establish boolean ≤ true/);
  process.stdout.write("tampered substituted bound: refused\n");
}

// A nested closure's claim is the type the compiled graph will use for it, so
// introduction requires it to be exactly the source annotation `() => T`: a
// ground `() => boolean` claim fits every observed call and is still refused.
// And a callable over the binder is meaningful only inside its closure: the
// same claim placed on an expression outside it is refused as an escape.
const returnedClaims: SourceClaims = JSON.parse(
  readFileSync(join(returned, "claims.json"), "utf8"),
);
{
  const fn = must(returnedClaims.functions[0], "the containing function");
  const nested = fn.expressions.find(
    (e) => !Array.isArray(e.type) && "scheme" in e.type && e.type.scheme.typeParams.length === 0,
  );
  assert.ok(nested && !Array.isArray(nested.type) && "scheme" in nested.type);
  const outer = fn.expressions.find(
    (e) => !Array.isArray(e.type) && "scheme" in e.type && e.type.scheme.typeParams.length > 0,
  );
  assert.ok(outer && !Array.isArray(outer.type) && "scheme" in outer.type);
  const grounded = structuredClone(returnedClaims);
  const g = must(grounded.functions[0], "the containing function").expressions.find((e) => e.pos[0] === nested.pos[0] && e.pos[1] === nested.pos[1]);
  assert.ok(g && !Array.isArray(g.type) && "scheme" in g.type);
  g.type.scheme.result = [1, 2];
  const groundedFile = join(returned, "forged-nested-claim.json");
  writeFileSync(groundedFile, JSON.stringify(grounded));
  assert.match(invoke(groundedFile, join(returned, "evidence.json"), returned),
    /nested closure claim differs from its source annotation/);
  process.stdout.write("tampered nested closure claim: refused\n");

  const escaped = structuredClone(returnedClaims);
  const outside = must(escaped.functions[0], "the containing function").expressions.find(
    (e) => e.pos[0] > outer.pos[1] && Array.isArray(e.type),
  );
  assert.ok(outside, "an expression after the closure");
  outside.type = nested.type;
  const escapedFile = join(returned, "forged-escape.json");
  writeFileSync(escapedFile, JSON.stringify(escaped));
  assert.match(invoke(escapedFile, join(returned, "evidence.json"), returned),
    /escapes its closure/);
  process.stdout.write("tampered rigid callable escape: refused\n");
}

// A captured cell keeps the contract its declaration states. Retyping it in the
// entry claim the closure is checked against changes what the body reads, so
// the scheme's own body check refuses: a capture is never retyped per call.
const capturedClaims: SourceClaims = JSON.parse(
  readFileSync(join(captured, "claims.json"), "utf8"),
);
{
  const claims = structuredClone(capturedClaims);
  const fn = must(claims.functions[0], "the containing function");
  const declaration = fn.entries.find((e) => e.bindings.some((b) => b.name === "store") && !e.bindings.some((b) => b.name === "read"));
  assert.ok(declaration, "the entry at the closure's declaration");
  const store = declaration.bindings.find((b) => b.name === "store");
  assert.ok(store);
  store.type = [1, 2];
  const file = join(captured, "forged-capture.json");
  writeFileSync(file, JSON.stringify(claims));
  assert.match(invoke(file, join(captured, "evidence.json"), captured),
    /does not satisfy its scheme universally: cannot establish boolean ≤ number/);
  process.stdout.write("tampered captured cell contract: refused\n");
}

// A substitution proposed through a callback is validated like any other:
// naming `number` for the call whose value is `flag` yields a genuine instance
// of the scheme whose value parameter the argument then fails to meet.
const callbackClaims: SourceClaims = JSON.parse(
  readFileSync(join(callback, "claims.json"), "utf8"),
);
{
  const claims = structuredClone(callbackClaims);
  const fn = claims.functions.find((f) => f.name === "throughCallback");
  assert.ok(fn);
  const site = fn.expressions.find((e) => e.instantiate?.some((i) => Array.isArray(i.type) && i.type.length === 2));
  assert.ok(site?.instantiate, "the call instantiated at boolean");
  must(site.instantiate[0], "the callback substitution").type = [4];
  const file = join(callback, "forged-callback-instance.json");
  writeFileSync(file, JSON.stringify(claims));
  invoke(file, join(callback, "evidence.json"), callback);
  process.stdout.write("tampered callback instantiation: refused\n");
}

// Generic bodies take the rigid-bound path in BOTH producer and consumer.
// Reusing valid evidence must not let an inferred local trust a forged point type.
const genericClaims: SourceClaims = JSON.parse(
  readFileSync(join(generic, "claims.json"), "utf8"),
);
for (const site of ["initializer", "binding"] as const) {
  const claims = structuredClone(genericClaims);
  const fn = claims.functions.find((f) => f.name === "inferred");
  assert.ok(fn);
  if (site === "initializer") {
    const initial = fn.expressions[0];
    assert.ok(initial);
    initial.type = [1, 2];
  } else {
    const saved = fn.entries.flatMap((e) => e.bindings).find((b) => b.name === "saved");
    assert.ok(saved);
    saved.type = [1, 2];
  }
  const file = join(generic, `forged-${site}.json`);
  writeFileSync(file, JSON.stringify(claims));
  const p = spawnSync(verifier, [
    "--check-source-claims", join(generic, "fragment.json"), file,
    join(generic, "source.ts"), join(generic, "evidence.json"),
  ], {encoding: "utf8", timeout: 30_000});
  assert.ifError(p.error);
  assert.equal(p.signal, null);
  assert.equal(p.status, 1, p.stdout + p.stderr);
  assert.match(p.stdout + p.stderr, /generic (entry claim|expression claim|binding annotation|return contract) at \[\d+,\d+\): cannot establish/);
  assert.match(p.stdout + p.stderr, /"role":"(?:expression|entry)-claim"/);
  process.stdout.write(`tampered inferred generic ${site}: refused\n`);
}

// A malformed direct-check input is a located refusal, not prose disguised as
// a failed judgment. The closed failure sum makes this branch mandatory at the
// Lean boundary, and the reader must preserve the distinction.
{
  const claims = structuredClone(genericClaims);
  const fn = claims.functions.find((f) => f.name === "inferred");
  assert.ok(fn);
  fn.expressions.pop();
  const file = join(generic, "missing-generic-expression.json");
  writeFileSync(file, JSON.stringify(claims));
  const p = spawnSync(verifier, [
    "--check-source-claims", join(generic, "fragment.json"), file,
    join(generic, "source.ts"), join(generic, "evidence.json"),
  ], {encoding:"utf8",timeout:30_000});
  assert.equal(p.status,1,p.stdout+p.stderr);
  const refusal = readDiagnostic(p.stdout+p.stderr);
  assert(refusal?.kind === "source-refusal");
  assert.deepEqual(refusal.sourceMap.pos,fn.namePos);
  assert(!("judgment" in refusal));
  process.stdout.write("malformed generic input: located refusal\n");
}

/*
 * The reader collects this producer too. It runs the same two steps `check`
 * runs — the shared parser, then `producer.exe` over the Fragment — and hands
 * what came out to the same verifier, so what it displays is this producer's
 * own document adjudicated the same way. What is checked here is that
 * correspondence: the claims the reader carries are the ones the producer
 * wrote, the verdicts are the verifier's, and a source this producer does not
 * implement is refused in its own words rather than collected as an empty
 * report.
 */
const repositoryPath = (file: string) =>
  `verification/ocaml-producer/examples/${file}.ts`;
{
  const shown = await analyse(repositoryPath("generic-default"), "ocaml");
  const results = shown.manifest.results ?? [];
  assert.deepEqual(results.map((r) => r.status), ["not-established"]);
  assert.notEqual(results[0]?.location, undefined);
  assert.match(JSON.stringify(results), /body requires a variable, a primitive literal, an assignment, a call or a closure/);
  process.stdout.write("reader collection: uncertified scheme defaults visibly refused\n");
}
const collected = await analyse(repositoryPath("values"), "ocaml");
assert.equal(collected.collection?.producer, "ocaml");
assert.equal(collected.collection?.producerRun, true);
assert.equal(collected.collection?.verified, true);
assert.equal(collected.candidate?.format, "source-claims");
// The document the reader offers for editing is the producer's own, not a
// display shape derived from it: the same bytes `check` wrote beside `values`.
assert.deepEqual(collected.candidate?.claims, {
  ...original,
  file: repositoryPath("values"),
});
assert.deepEqual(
  (collected.manifest.results ?? []).map((r) => r.status),
  ["verified", "verified"],
);
process.stdout.write(
  `reader collection: ${collected.manifest.functions.length} functions, producer's own claims verified\n`,
);

const collectedGeneric = await analyse(
  repositoryPath("generic-closure"),
  "ocaml",
);
assert.equal(collectedGeneric.collection?.verified, true);
assert.equal(collectedGeneric.candidate?.format, "source-claims");
assert.match(
  collectedGeneric.manifest.functions[0]?.expressions.find((e) =>
    e.type.startsWith("<"),
  )?.type ?? "",
  /^<T>\(arg0: T\) => T$/,
);
process.stdout.write("reader collection: quantified callable rendered\n");

const collectedDefaults = await analyse(repositoryPath("generic-rigid-default"), "ocaml");
assert.equal(collectedDefaults.collection?.verified, true);
assert.match(
  collectedDefaults.manifest.functions[0]?.expressions.find(e => e.type.startsWith("<"))?.type ?? "",
  /arg1: \(T\) \| \(undefined\)/,
);
process.stdout.write("reader collection: rigid default union rendered\n");


const collectedRest = await analyse(repositoryPath("generic-rest"), "ocaml");
assert.equal(collectedRest.collection?.verified, true);
assert.match(collectedRest.manifest.functions.find(f=>f.name === "genericRestUses")?.expressions
  .find(e=>e.type.startsWith("<"))?.type ?? "", /^<T>\(\.\.\.rest: Array<T>\) => Array<T>$/);
process.stdout.write("reader collection: quantified rest and array contracts rendered\n");

const collectedJsonBound = await analyse(repositoryPath("recursive-json-variants"), "ocaml");
assert.deepEqual(collectedJsonBound.manifest.results?.map(r => r.status), ["verified"]);
assert.equal(collectedJsonBound.collection?.verified, true);
process.stdout.write("reader collection: imported Json bound verified\n");

// A negative control must reach validation and fail there. Failing there means
// failing an obligation, which the reader can show at its span; an adapter that
// throws before any obligation exists has refused, not validated, and the
// reader can point at nothing. Ranging over the inventory is what keeps a new
// control from escaping this.
const directControls = new Set([
  "invalid-generic-rest",
  "invalid-generic-rest-argument",
  "invalid-generic",
  "invalid-generic-copy",
  "invalid-generic-closure",
  "invalid-scheme-capture",
  "invalid-generic-default",
  "invalid-rigid-default",
]);
let testedDirectProtocol = false;
for (const control of cases.filter((c) => c.kind === "negative")) {
  const shown = await analyse(repositoryPath(control.file), "ocaml");
  const results = shown.manifest.results ?? [];
  assert.deepEqual(
    results.map((r) => r.status),
    ["not-established"],
    `${control.file}: reader must show it as not established`,
  );
  assert.notEqual(
    results[0]?.location,
    undefined,
    `${control.file}: reached no obligation, so the reader has nothing to show`,
  );
  if (directControls.has(control.file)) {
    assert.equal(
      results[0]?.obligation?.kind,
      "direct-obligation",
      `${control.file}: a direct checker failure needs a structured judgment`,
    );
    const direct = results[0]?.obligation;
    assert(direct?.kind === "direct-obligation");
    assert(!("statement" in direct.judgment), "direct judgments cannot store prose");
    const judgmentView = results[0]?.obligationView?.judgement;
    assert(judgmentView && !("text" in judgmentView),
      "judgment text must be derived by the shared printer");
    if (!testedDirectProtocol) {
      testedDirectProtocol = true;
      const {input: _input, ...wire} = direct;
      const line = (value: unknown) =>
        `obligation-diagnostic: ${JSON.stringify(value)}`;
      assert(readDiagnostic(line(wire)), "the structured direct judgment decodes");
      const unknown = structuredClone(wire);
      // Deliberately outside the typed union: the reader must refuse it at run time.
      // Reflect keeps this malformed-wire test from weakening the typed source.
      Reflect.set(unknown.judgment, "kind", "future-judgment");
      assert.equal(readDiagnostic(line(unknown)),undefined,"an unhandled judgment variant is refused");
      const unscoped = structuredClone(wire);
      unscoped.judgment.actual = {kind:"rigid",name:"Undeclared"};
      assert.equal(readDiagnostic(line(unscoped)),undefined,"an undeclared rigid type is refused");
      const misplaced = structuredClone(wire);
      misplaced.sourceMap.pos = [0,0];
      assert.equal(readDiagnostic(line(misplaced)),undefined,"a judgment cannot borrow another source span");
    }
  }
}
process.stdout.write(
  `reader collection: ${cases.filter((c) => c.kind === "negative").length} negative controls failed an obligation\n`,
);

// What this producer does not implement is refused where it is refused, in the
// words that boundary uses. It does not become a report with nothing in it.
for (const [file, says] of [
  ["unsupported", /OCaml producer proposed no claims: unsupported:/],
] as const) {
  await assert.rejects(analyse(repositoryPath(file), "ocaml"), says);
  process.stdout.write(`reader collection: ${file} refused by name\n`);
}
