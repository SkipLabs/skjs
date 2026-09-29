import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, realpathSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { tmpdir } from "node:os";
import { createHash } from "node:crypto";
import { resolve } from "node:path";
import { parseFile, definedClassCallables, close as closeParser } from "../tools/fragment-parse.mts";
import { collectDeclarations, importTargets, tsconfigOf } from "../tools/declaration-graph.mts";
import { overlay as arrayOverlay } from "../tools/array-prototype.mts";
import type { DeclarationDocument, Reference, TypeDefinition, TypeTerm } from "../tools/declaration-types.mts";
import type { Ast } from "../tools/fragment.mts";
import { spawnSync, type SpawnSyncReturns } from "node:child_process";
import { check, verifier } from "./check.mts";
import { cases } from "./cases.mts";
import { expectOutcome, pooled, runCase } from "./run-cases.mts";
import type { Row, SourceClaims } from "../tools/source-claims.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";
import { checkGenericRest } from "./generic-rest.mts";
import { checkOverloads } from "./overload-claims.mts";
import { checkDefaults, checkSchemeDefaults, checkEarlyDefault } from "./default-parameters.mts";
import vm from "node:vm";
import { stripTypes } from "../tools/strip-types.mts";
// The reader's collector, imported rather than served: `serve.mts` takes the
// port only when it is run directly.
import { analyse } from "../report-viewer/serve.mts";
import { fromBundle, parseReport } from "../report-viewer/model.mts";
import type { Bundle } from "../report-viewer/types.ts";
const here = import.meta.dirname;
/** Inspect the source equations used by Lean, rather than a second edge list. */
function referencesIn(term: TypeTerm): Reference[] {
  switch (term.k) {
    case "atom":
    case "literal":
    case "self":
    case "parameter":
    case "binder":
    case "callable": return [];
    case "union":
    case "intersection": return term.parts.flatMap(referencesIn);
    case "array": return referencesIn(term.element);
    case "tuple": return [...term.required, ...term.optional,
      ...(term.rest ? [term.rest] : [])].flatMap(referencesIn);
    case "object": return [
      ...term.fields.flatMap(field => referencesIn(field.type)),
      ...(term.stringIndex ? referencesIn(term.stringIndex.value) : []),
      ...(term.numberIndex ? referencesIn(term.numberIndex.value) : []),
      ...(term.symbolIndex ? referencesIn(term.symbolIndex.value) : []),
      ...term.calls.flatMap(referencesIn),
    ];
    case "function": return [
      ...(term.receiver ? referencesIn(term.receiver) : []),
      ...term.params.flatMap(referencesIn),
      ...(term.rest ? referencesIn(term.rest) : []),
      ...referencesIn(term.result),
    ];
    case "constructor": return [...term.params.flatMap(referencesIn),
      ...(term.rest ? referencesIn(term.rest) : []), ...referencesIn(term.result)];
    case "pack": return referencesIn(term.of);
    case "scheme": return [
      ...term.binders.flatMap(b => [...(b.bound ? referencesIn(b.bound) : []),
        ...(b.default ? referencesIn(b.default) : [])]),
      ...term.signatures.flatMap(referencesIn),
    ];
    case "reference": return [term.reference, ...term.args.flatMap(referencesIn)];
    default: {
      const exhaustive: never = term;
      return exhaustive;
    }
  }
}
function referencesInDefinition(definition: TypeDefinition): Reference[] {
  return [
    ...definition.parameters.flatMap(parameter => [
      ...(parameter.bound ? referencesIn(parameter.bound) : []),
      ...(parameter.default ? referencesIn(parameter.default) : []),
    ]),
    ...referencesIn(definition.expression),
    ...definition.bases.flatMap(referencesIn),
  ];
}
{
  const source = join(mkdtempSync(join(tmpdir(), "skjs-reopen-")), "client.ts");
  writeFileSync(source, "function before(): boolean { return true; }\n");
  assert.equal(parseFile(source).functions[0]?.name, "before");
  writeFileSync(source, "function after(): boolean { return false; }\n");
  assert.equal(parseFile(source).functions[0]?.name, "after");
}
let pinnedDeclarationDocument: DeclarationDocument | null = null;
{
  const local = parseFile(resolve(here, "examples/local-inheritance.ts"));
  assert.deepEqual(local.declarations.roots.map(root => [root.binding.kind, root.binding.local]),
    [["local", "Base"], ["local", "Derived"]]);
  assert.deepEqual(local.declarations.definitions.map(definition =>
    [definition.declaration.name, definition.bases.length]),
    [["Base", 0], ["Derived", 1]]);
}
let recursiveJson = "";
// The framework fixture is the upstream source, including its imports and
// classes. A simplified replacement must not quietly inherit its census row.
for (const [file, expected] of [
  ["examples/reactive-sum-prettier-ignore.ts", "8c10ace97b50d5a3521626fe569fcfe87034a48424f84f2d2aeb970eba161efe"],
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
  // The corrected client keeps those callables and adds the service class.
  assert.deepEqual(definedClassCallables(resolve(here, "examples/reactive-sum-sound.ts")).map(c => c.name), [
    "AddIndex.constructor", "AddIndex.mapEntry", "Plus.mapEntry",
    "Minus.mapEntry", "Add.instantiate", "Sub.instantiate", "Service.createGraph",
  ]);
  const upstreamConfig = tsconfigOf(resolve(here, "upstream"));
  // TypeScript resolves the framework's imports: interfaces through the core
  // package's reexports, and a value from the server package. This is
  // provenance for contracts the fragment cannot yet interpret.
  assert.deepEqual(importTargets(source, upstreamConfig).map(t => [t.local, t.module, t.name, t.kind]), [
    ["EagerCollection", "skipruntime-ts/core/src/api.ts", "EagerCollection", "InterfaceDeclaration"],
    ["Mapper", "skipruntime-ts/core/src/api.ts", "Mapper", "InterfaceDeclaration"],
    ["Resource", "skipruntime-ts/core/src/api.ts", "Resource", "InterfaceDeclaration"],
    ["Values", "skipruntime-ts/core/src/api.ts", "Values", "InterfaceDeclaration"],
    ["InputDefinition", "skipruntime-ts/core/src/api.ts", "InputDefinition", "ClassDeclaration"],
    ["runService", "skipruntime-ts/server/src/server.ts", "runService", "FunctionDeclaration"],
  ]);
  // The runtime's value imports resolve, and the whole declaration graph is
  // read: `runService`'s `Promise` and the `Iterable` the mappers return from
  // the standard library, and `ResourceClass` as a construct signature.
  assert.ok(collectDeclarations(source, { tsconfigPath: upstreamConfig }).definitions.length > 0);
  // Each runtime interface sum.ts imports, applied in a client of the same
  // project, and the first declaration the graph refuses on its way.
  const probe = mkdtempSync(join(tmpdir(), "skjs-runtime-api-"));
  writeFileSync(join(probe, "package.json"), '{"type":"module"}');
  writeFileSync(join(probe, "tsconfig.json"),
    JSON.stringify({ extends: upstreamConfig, include: ["*.ts"] }));
  // A generic method is an opaque member and a `unique symbol` key is a
  // field keyed by that symbol, so `Resource`, `Context` and
  // `EagerCollection` (through `Managed`'s `[sk_managed]`) collect, and so do
  // `Mapper` and `Values`, through the library's `Iterable` and `Iterator`.
  for (const [use, imports, refusal] of [
    ["Mapper<string, number, string, number>", "Mapper", null],
    ["Values<number>", "Values", null],
    ["EagerCollection<string, number>", "EagerCollection", null],
    ["Resource<SharedCollections>", "Resource, SharedCollections", null],
    ["Context", "Context", null],
  ] as const) {
    const client = join(probe, `${imports.split(",")[0]}.ts`);
    writeFileSync(client, `import type { ${imports} } from "@skipruntime/core";\nexport type Use = ${use};\n`);
    const collect = () => collectDeclarations(client, { tsconfigPath: join(probe, "tsconfig.json") });
    if (refusal) assert.throws(collect, refusal);
    else assert.ok(collect().definitions.length > 0);
  }
  // The upstream bytes the census row and these results are about.
  const upstreamSha = (path: string) =>
    createHash("sha256").update(readFileSync(resolve(here, "upstream", path))).digest("hex");
  assert.equal(upstreamSha("skipruntime-ts/core/src/api.ts"),
    "1e51e0c9cc1447605d9d718d8c094c4f70a0cf5ca065804b775a2d4c76e0e6a6");
  // The runtime with a sound service binding holds only the three files the
  // binding changes, pinned here; every other file is the snapshot's own.
  const soundSha = (path: string) =>
    createHash("sha256").update(readFileSync(resolve(here, "upstream-sound", path))).digest("hex");
  assert.deepEqual(["skipruntime-ts/core/src/api.ts", "skipruntime-ts/core/src/index.ts",
    "skipruntime-ts/server/src/server.ts"].map(soundSha), [
    "890fb3f5e7e9603d8440f252bc02f069a7fb2e1ced43a2ae4bf8f1e2dd4d5080",
    "c1a9a5e080a8dbe0866f1cb33420132b7baef07158b5800610b93c97abb21368",
    "26cd1719e86d0c8195e41648cd20b74505bcb412d7d624341b3ef4d89f176108",
  ]);
  for (const shared of ["skipruntime-ts/core/src/errors.ts", "skipruntime-ts/core/skiplang-json",
    "skipruntime-ts/core/skiplang-std", "skipruntime-ts/core/package.json",
    "skipruntime-ts/server/package.json"])
    assert.equal(realpathSync(resolve(here, "upstream-sound", shared)),
      realpathSync(resolve(here, "upstream", shared)), `upstream-sound/${shared} is the snapshot's`);
  const jsonModuleSha = upstreamSha("skiplang/skjson/ts/binding/src/index.ts");
  assert.equal(jsonModuleSha,
    "3cdd38bb4b6d394133ee922bccb6eff50839740b204c259edb17c19060bf9021");
  // Node's declarations, as Skip's build has them: `@types/node` at the
  // version Skip's lock pins at the snapshot's commit (`upstream/package.json`,
  // installed by `npm ci --prefix verification/ocaml-producer/upstream`).
  // `process` and the members sum.ts reads are declared in these two files.
  const nodeTypes: unknown = JSON.parse(readFileSync(resolve(here,
    "upstream/node_modules/@types/node/package.json"), "utf8"));
  assert.ok(nodeTypes && typeof nodeTypes === "object" && "version" in nodeTypes &&
    nodeTypes.version === "22.10.7", "run `npm ci --prefix verification/ocaml-producer/upstream`");
  assert.equal(upstreamSha("node_modules/@types/node/globals.d.ts"),
    "ba97261afafe85aafe76d988e65e531da8e8cf791c49caf0531f5dd1689bd91b");
  assert.equal(upstreamSha("node_modules/@types/node/process.d.ts"),
    "42aaa94addeed66a04b61e433c14e829c43d1efd653cf2fda480c5fb3d722ed8");
  // Json reaches the client through the core package's `paths` entry, its
  // reexports and the workspace symlink; TypeScript follows all three.
  const jsonPath = resolve(here, "examples/recursive-json.ts");
  const jsonClient = readFileSync(jsonPath, "utf8");
  pinnedDeclarationDocument = collectDeclarations(jsonPath, { tsconfigPath: upstreamConfig });
  assert.deepEqual(pinnedDeclarationDocument.roots.map(r => [r.binding.local, r.declaration.module,
    r.declaration.name]), [
    ["Json", "skiplang/skjson/ts/binding/src/index.ts", "Json"],
    ["JsonObject", "skiplang/skjson/ts/binding/src/index.ts", "JsonObject"],
  ]);
  // Without the project that configures the package, the import has no meaning.
  assert.throws(() => parseFile(jsonPath), /gate:/);
  const importedAst = parseFile(jsonPath, false, upstreamConfig);
  // The client uses arrays, so the parser also lists `ArrayProto`, first, and
  // the runtime declarations it names: the conversion equation, `Iterator`,
  // which `[Symbol.iterator]` returns, and what that reaches.
  const [arrayProto, ...parsedDefinitions] = importedAst.declarations.definitions;
  assert.equal(arrayProto?.declaration.module, "skjs/array-prototype");
  const standard = (d: { declaration: { module: string } }) => d.declaration.module.startsWith("typescript/lib/");
  assert.ok(parsedDefinitions.some(d => standard(d) && d.declaration.name === "Iterator"));
  assert.deepEqual(importedAst.declarations.symbols.map(s => s.name), ["iterator", "toPrimitive"]);
  assert.deepEqual({ ...importedAst.declarations, definitions: parsedDefinitions.filter(d =>
    !standard(d) && d.declaration.module !== "skjs/array-conversion"),
    symbols: [] }, pinnedDeclarationDocument);
  const exported = join(mkdtempSync(join(tmpdir(), "skjs-export-")), "client.ts");
  writeFileSync(exported, "export function own(this: undefined): undefined { return this; }\n");
  assert.equal(parseFile(exported).functions[0]?.body[0]?.k, "return");
  // No type name here reaches a declaration, so the modifier is the refusal.
  writeFileSync(exported, "export default function own(): undefined { return undefined; }\n");
  assert.throws(() => parseFile(exported),
    /only the export and async modifiers are admitted on a source function/);
  const jsonAst = parseFile(jsonPath, false, upstreamConfig);
  assert.deepEqual(jsonAst.functions.map(f => f.name), ["nest", "lookup"]);
  // The parser reads one file and TypeScript resolves another path: their
  // bytes must be equal, or spans in one tree would name code in the other.
  const changedCopy = join(mkdtempSync(join(tmpdir(), "skjs-copy-")), "client.ts");
  writeFileSync(changedCopy, jsonClient.replace("value, null", "null, value"));
  assert.throws(() => parseFile(changedCopy, false, upstreamConfig, jsonPath),
    /gate:.*TypeScript client source bytes differ/);
  const nest = jsonAst.functions[0];
  const lookup = jsonAst.functions[1];
  assert(nest && lookup);
  // Annotations name the declarations TypeScript resolved.
  const nestParam = nest.params[0]?.type;
  assert(nestParam?.k === "reference" && nestParam.reference.name === "Json" && !nestParam.args.length);
  const lookupParam = lookup.params[0]?.type;
  assert(lookupParam?.k === "reference" && lookupParam.reference.name === "JsonObject");
  const lookupResult = lookup.retType.k === "union" ? lookup.retType.parts : [lookup.retType];
  assert(lookupResult.some(t => t.k === "reference" && t.reference.name === "Json"));
  const checkedJson = check(jsonPath, upstreamConfig);
  recursiveJson = checkedJson.artifacts;
  assert.equal(checkedJson.status, "verified", JSON.stringify(checkedJson));
  assert.equal(checkedJson.phase, "check");
  assert.deepEqual(checkedJson.functions, ["nest", "lookup"]);
  const typeScript = spawnSync(resolve(here, "../tools/node_modules/.bin/tsc"),
    ["-p", upstreamConfig, "--pretty", "false", "--noEmit"], { encoding: "utf8" });
  assert.ifError(typeScript.error);
  const typeScriptOutput = typeScript.stdout + typeScript.stderr;
  assert.match(typeScriptOutput, /invalid-recursive-json-bound\.ts/,
    "TypeScript must have checked the imported-Json clients");
  assert.doesNotMatch(typeScriptOutput, /invalid-recursive-json-alias-write\.ts/,
    "TypeScript should accept the covariant array assignment that the model refuses");
  // A plain record is not Json: TypeScript accepts both by its implicit index
  // rule. At a declaration's `V extends Json` bound the refusal is the
  // request's, as every application bound's is, so it is checked here rather
  // than as a located control; the Json return is a located one (cases.mts).
  for (const file of ["invalid-sum-record-json", "invalid-sum-record-collection"])
    assert.doesNotMatch(typeScriptOutput, new RegExp(`${file}\\.ts`),
      `TypeScript should accept ${file}, which the model refuses`);
  const recordCollection = check(join(here, "examples/invalid-sum-record-collection.ts"), upstreamConfig);
  assert.equal(recordCollection.status, "unverified", JSON.stringify(recordCollection));
  assert.match(recordCollection.detail, /the type argument for EagerCollection's "V" .* does not establish its declared bound/);
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
    "declarations" in checkedFragment);
  assert.deepEqual(checkedFragment.declarations, jsonAst.declarations);
  const jsonDefinitions = pinnedDeclarationDocument.definitions;
  assert.deepEqual(jsonDefinitions.map(d => [d.declaration.name,
    referencesInDefinition(d).map(r => r.target.name)]), [
    ["Json", ["Json", "JsonObject"]],
    ["JsonObject", ["Json"]],
  ]);
  assert(jsonDefinitions.every(d =>
    d.declaration.module === "skiplang/skjson/ts/binding/src/index.ts"));
  const json = jsonDefinitions.find(d => d.declaration.name === "Json");
  const jsonObject = jsonDefinitions.find(d => d.declaration.name === "JsonObject");
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
  // A fixture project: packages mapped by `paths`, a barrel, a global
  // declaration file. Every client below is resolved by TypeScript in it.
  const a = "import type { B } from './b.js'; export type A<T> = { next: B<T> }; export type Bound<T extends B<number>> = T; export type Grow<T> = { next: Grow<[T]> };";
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
    "export type NestedMethod = { inner: { read?(): boolean } };\n" +
    "export interface GenericMethod { read<T>(value: T): T; }\n" +
    "export interface OptionalMethod { read(value?: boolean): boolean; }\n" +
    "export interface Derived extends Box { readonly label: string; }\n" +
    "export interface Labeled { readonly label: string; }\n" +
    "export interface MultipleBases extends Box, Labeled { readonly count: number; }\n";
  const genericShapes = "export type GenericBox<T> = { readonly value: T };\n" +
    "export type ImportedId<T> = T;\n" +
    "export type GenericPair<L, R> = { readonly left: L; readonly right: R };\n" +
    "export type GenericOuter<T> = { readonly inner: GenericBox<T> };\n" +
    "export type GenericTuple<T> = readonly [T, number];\n" +
    "export type GenericCallable<T> = (value: T) => T;\n" +
    "export type BoundedBox<T extends boolean> = { readonly value: T };\n" +
    "export type BoundedNested<T extends GenericBox<boolean>> = { readonly value: T };\n" +
    "export type DefaultBox<T = boolean> = { readonly value: T };\n" +
    "export type DependentDefault<T, U = T> = { readonly first: T; readonly second: U };\n" +
    "export type DependentBound<T, U extends T = T> = { readonly second: U };\n" +
    "export type BoundedDefault<T extends boolean = boolean> = { readonly value: T };\n";
  const inheritedGeneric =
    "export interface GenericDerived<T> extends GenericBox<T> { readonly label: string; }\n";
  const literalShapes =
    "export type Flag = true;\n" +
    "export type Kind = \"on\";\n" +
    "export type Overload = ((x: boolean) => number) & ((x: number) => boolean);\n" +
    "export type Both = { readonly a: boolean } & { readonly b: number };\n";
  writeFileSync(join(pairDir, "box.ts"),
    box + genericShapes + inheritedGeneric + literalShapes);
  const globalText = "interface GlobalBox { readonly flag: boolean; }\n";
  writeFileSync(join(pairDir, "global.d.ts"), globalText);
  const pairConfig = join(pairDir, "tsconfig.json");
  writeFileSync(pairConfig, JSON.stringify({
    compilerOptions: { strict: true, noEmit: true, module: "Node16",
      moduleResolution: "Node16", paths: { "@fixture/a": ["./a.ts"],
        "@fixture/barrel": ["./barrel.ts"], "@fixture/box": ["./box.ts"],
        "@fixture/merged": ["./merged.ts"], "@fixture/twice": ["./twice.ts"] } },
    include: ["*.ts"],
  }));
  /** The declaration graph of a client consisting of `text`, in the fixture project. */
  let clients = 0;
  const graphOf = (text: string) => {
    const client = join(pairDir, `graph-client-${clients++}.ts`);
    writeFileSync(client, text);
    return collectDeclarations(client, { tsconfigPath: pairConfig });
  };
  const pairDocument = graphOf("import type { A } from '@fixture/a';");
  assert.deepEqual(pairDocument.definitions.map(d => [d.declaration.name,
    d.parameters.map(p => p.name), referencesInDefinition(d).map(r => [r.target.name, r.arguments.length])]), [
    ["A", ["T"], [["B", 1]]],
    ["B", ["T"], [["A", 1]]],
  ]);
  const aDef = pairDocument.definitions.find(d => d.declaration.name === "A");
  assert(aDef && aDef.expression.k === "object");
  const next = aDef.expression.fields.find(f => f.name === "next");
  assert(next && next.type.k === "reference" && next.type.args[0]?.k === "parameter");
  assert.equal(next.type.reference.target.module, "b.ts");
  assert.equal(next.type.args[0].index, 0);
  const genericClient = join(pairDir, "client.ts");
  writeFileSync(genericClient,
    'import type { A } from "@fixture/a";\n' +
    'export function keep(value: A<boolean>): A<boolean> { return value; }\n');
  const genericAst = parseFile(genericClient, false, pairConfig);
  const genericParam = genericAst.functions[0]?.params[0]?.type;
  assert(genericParam?.k === "reference" && genericParam.reference.name === "A" &&
    genericParam.args[0]?.k === "atom" && genericParam.args[0].name === "boolean");
  // Declarations have one lowering, Lean's. A mutually recursive application
  // the producer reserves a row for is that row, which its equation names
  // again: a finite graph.
  const recursiveGeneric = check(genericClient, pairConfig);
  assert.equal(recursiveGeneric.status, "verified", JSON.stringify(recursiveGeneric));
  // One at arguments that grow at each unfolding too: a declaration is one
  // equation, and an application is unfolded one step when it is read
  // (RECURSIVE-EQUATIONS §3.2), so the family is not enumerated.
  writeFileSync(genericClient,
    'import type { Grow } from "@fixture/a";\n' +
    'export function keepGrow(value: Grow<boolean>): Grow<boolean> { return value; }\n');
  const growing = check(genericClient, pairConfig);
  assert.equal(growing.status, "verified", JSON.stringify(growing));
  // A name imported through a barrel is the declaration the barrel reexports.
  writeFileSync(genericClient,
    'import type { A } from "@fixture/barrel";\n' +
    'export function throughBarrel(value: A<boolean>): A<boolean> { return value; }\n');
  const barrelAst = parseFile(genericClient, false, pairConfig);
  assert.equal(barrelAst.declarations.roots[0]?.declaration.module, "a.ts");
  assert.equal(barrelAst.declarations.roots[0]?.binding.kind === "import" &&
    barrelAst.declarations.roots[0].binding.specifier, "@fixture/barrel");
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
  const checkedBox = check(boxClient, pairConfig);
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
  const checkedGenericShapes = check(genericShapesClient, pairConfig);
  assert.equal(checkedGenericShapes.status, "verified", JSON.stringify(checkedGenericShapes));
  assert.deepEqual(checkedGenericShapes.functions,
    ["unbox", "right", "nested", "first", "applied"]);
  const inheritedClient = join(pairDir, "inherited-client.ts");
  writeFileSync(inheritedClient,
    'import type { Derived, MultipleBases, GenericDerived } from "@fixture/box";\n' +
    'export function inherited(value: Derived): boolean { return value.flag; }\n' +
    'export function owned(value: Derived): string { return value.label; }\n' +
    'export function multiple(value: MultipleBases): number { return value.count; }\n' +
    'export function genericBase(value: GenericDerived<boolean>): boolean { return value.value; }\n');
  const checkedInherited = check(inheritedClient, pairConfig);
  assert.equal(checkedInherited.status, "verified", JSON.stringify(checkedInherited));
  assert.deepEqual(checkedInherited.functions,
    ["inherited", "owned", "multiple", "genericBase"]);
  // An interface's base is the declaration TypeScript binds its heritage name to.
  const inheritedGraph = collectDeclarations(inheritedClient, { tsconfigPath: pairConfig });
  const derived = must(inheritedGraph.definitions.find(d => d.declaration.name === "Derived"),
    "Derived declaration");
  assert.equal(must(referencesInDefinition(derived)[0], "Derived heritage reference").target.name, "Box");
  const importedIdentityClient = join(pairDir, "imported-identity-client.ts");
  writeFileSync(importedIdentityClient,
    'import type { ImportedId } from "@fixture/box";\n' +
    'export function rigid<T>(value: ImportedId<T>): T { return value; }\n' +
    'export function ground(value: ImportedId<boolean>): boolean { return value; }\n');
  const importedIdentity = check(importedIdentityClient, pairConfig);
  assert.equal(importedIdentity.status, "verified", JSON.stringify(importedIdentity));
  assert.deepEqual(importedIdentity.functions, ["rigid", "ground"]);
  // Local/imported parity for declarations applied to a rigid binder: one
  // source-equation expansion serves both. The same function is written with a
  // local declaration and with the imported one; the outcomes must agree.
  const parity = (name: string, local: string, imported: string, body: string) => {
    const localClient = join(pairDir, `parity-local-${name}.ts`);
    writeFileSync(localClient, local + body);
    const importedClient = join(pairDir, `parity-imported-${name}.ts`);
    writeFileSync(importedClient, imported + body);
    const l = check(localClient, pairConfig), i = check(importedClient, pairConfig);
    const outcome = (o: typeof l) => [o.status, o.phase,
      o.status === "verified" ? "" : o.detail.split("\n")[0]?.replace(/\[\d+,\d+\)/g, "[span]")];
    assert.deepEqual(outcome(l), outcome(i), `${name}: local and imported outcomes differ`);
    return l;
  };
  const callableLocal = "type GenericCallable<T> = (value: T) => T;\n";
  const callableImported = 'import type { GenericCallable } from "@fixture/box";\n';
  const rigidCall = parity("rigid-call", callableLocal, callableImported,
    "export function applyRigid<T>(f: GenericCallable<T>, x: T): T { return f(x); }\n");
  assert.equal(rigidCall.status, "verified", JSON.stringify(rigidCall));
  const wrongRigidCall = parity("wrong-rigid-call", callableLocal, callableImported,
    "export function wrongRigid<T>(f: GenericCallable<T>, x: T): boolean { return f(x); }\n");
  assert.equal(wrongRigidCall.status, "unverified", JSON.stringify(wrongRigidCall));
  assert.match(wrongRigidCall.detail, /no derivation of its return-contract claim/);
  // A record over a rigid binder is a graph type over its parameter row, for
  // both.
  const rigidRecord = parity("rigid-record", "type GenericBox<T> = { readonly value: T };\n",
    'import type { GenericBox } from "@fixture/box";\n',
    "export function unboxRigid<T>(value: GenericBox<T>): T { return value.value; }\n");
  assert.equal(rigidRecord.status, "verified", JSON.stringify(rigidRecord));
  // Ground applications agree as well.
  const groundCall = parity("ground-call", callableLocal, callableImported,
    "export function applyGround(f: GenericCallable<boolean>): boolean { return f(true); }\n");
  assert.equal(groundCall.status, "verified", JSON.stringify(groundCall));
  // Literal and intersection equations agree too. A nullary declaration
  // whose row equals an annotation's row is the same type.
  const literalLocal = 'type Flag = true;\ntype Kind = "on";\n' +
    "type Overload = ((x: boolean) => number) & ((x: number) => boolean);\n";
  const literalImported = 'import type { Flag, Kind, Overload } from "@fixture/box";\n';
  const literals = parity("literals", literalLocal, literalImported,
    "export function keepFlag(f: Flag): true { return f; }\n" +
    'export function keepKind(k: Kind): "on" { return k; }\n' +
    "export function callOver(f: Overload): number { return f(true); }\n");
  assert.equal(literals.status, "verified", JSON.stringify(literals));
  const wrongLiteral = parity("wrong-literal", literalLocal, literalImported,
    "export function badFlag(f: Flag): false { return f; }\n");
  assert.equal(wrongLiteral.status, "unverified", JSON.stringify(wrongLiteral));
  assert.equal(wrongLiteral.phase, "search");
  // A record intersection is the one record its operands describe, read at
  // each operand's fields.
  const bothLocal = "type Both = { readonly a: boolean } & { readonly b: number };\n";
  const bothImported = 'import type { Both } from "@fixture/box";\n';
  const recordMeet = parity("record-meet", bothLocal, bothImported,
    "export function readBoth(x: Both): number { return x.b; }\n");
  assert.equal(recordMeet.status, "verified", JSON.stringify(recordMeet));
  const wrongMeet = parity("wrong-record-meet", bothLocal, bothImported,
    "export function readWrong(x: Both): boolean { return x.b; }\n");
  assert.equal(wrongMeet.status, "unverified", JSON.stringify(wrongMeet));
  assert.equal(wrongMeet.phase, "search");
  const badInheritedClient = join(pairDir, "bad-inherited-client.ts");
  writeFileSync(badInheritedClient,
    'import type { GenericDerived } from "@fixture/box";\n' +
    'export function wrong(value: GenericDerived<boolean>): number { return value.value; }\n');
  const badInherited = check(badInheritedClient, pairConfig);
  assert.equal(badInherited.status, "unverified", JSON.stringify(badInherited));
  assert.equal(badInherited.phase, "search");
  const badGenericShapeClient = join(pairDir, "bad-generic-shape-client.ts");
  writeFileSync(badGenericShapeClient,
    'import type { GenericBox } from "@fixture/box";\n' +
    'export function wrong(value: GenericBox<boolean>): number { return value.value; }\n');
  const rejectedGenericShape = check(badGenericShapeClient, pairConfig);
  assert.equal(rejectedGenericShape.status, "unverified", JSON.stringify(rejectedGenericShape));
  assert.equal(rejectedGenericShape.phase, "search");
  const boundedShapeClient = join(pairDir, "bounded-shape-client.ts");
  writeFileSync(boundedShapeClient,
    'import type { BoundedBox } from "@fixture/box";\n' +
    'export function bounded(value: BoundedBox<boolean>): boolean { return value.value; }\n');
  const boundedShape = check(boundedShapeClient, pairConfig);
  assert.equal(boundedShape.status, "verified", JSON.stringify(boundedShape));
  const boundedNestedClient = join(pairDir, "bounded-nested-client.ts");
  writeFileSync(boundedNestedClient,
    'import type { BoundedNested, GenericBox } from "@fixture/box";\n' +
    'export function nestedBound(value: BoundedNested<GenericBox<boolean>>): boolean { return value.value.value; }\n');
  const boundedNested = check(boundedNestedClient, pairConfig);
  assert.equal(boundedNested.status, "verified", JSON.stringify(boundedNested));
  const invalidBoundClient = join(pairDir, "invalid-bound-client.ts");
  writeFileSync(invalidBoundClient,
    'import type { BoundedBox } from "@fixture/box";\n' +
    'export function invalidBound(value: BoundedBox<number>): number { return value.value; }\n');
  const invalidBound = check(invalidBoundClient, pairConfig);
  assert.equal(invalidBound.status, "unverified", JSON.stringify(invalidBound));
  assert.match(invalidBound.detail, /the type argument for BoundedBox's "T" .* does not establish its declared bound/);
  const defaultClient = join(pairDir, "default-client.ts");
  writeFileSync(defaultClient,
    'import type { DefaultBox, DependentDefault, DependentBound, BoundedDefault } from "@fixture/box";\n' +
    'export function defaulted(value: DefaultBox): boolean { return value.value; }\n' +
    'export function overridden(value: DefaultBox<number>): number { return value.value; }\n' +
    'export function dependent(value: DependentDefault<boolean>): boolean { return value.second; }\n' +
    'export function dependentBound(value: DependentBound<boolean>): boolean { return value.second; }\n' +
    'export function boundedDefault(value: BoundedDefault): boolean { return value.value; }\n');
  const defaults = check(defaultClient, pairConfig);
  assert.equal(defaults.status, "verified", JSON.stringify(defaults));
  assert.deepEqual(defaults.functions,
    ["defaulted", "overridden", "dependent", "dependentBound", "boundedDefault"]);
  const invalidDependentClient = join(pairDir, "invalid-dependent-client.ts");
  writeFileSync(invalidDependentClient,
    'import type { DependentBound } from "@fixture/box";\n' +
    'export function invalidDependent(value: DependentBound<boolean, number>): number { return value.second; }\n');
  const invalidDependent = check(invalidDependentClient, pairConfig);
  assert.equal(invalidDependent.status, "unverified", JSON.stringify(invalidDependent));
  assert.match(invalidDependent.detail,
    /type argument .*does not establish its declared bound/);
  // A global declaration file of the project supplies an unimported name.
  const boxAst = parseFile(boxClient, false, pairConfig);
  assert.equal(boxAst.declarations.definitions.find(d => d.declaration.name === "GlobalBox")?.
    declaration.module, "global.d.ts");
  const badBoxClient = join(pairDir, "bad-box-client.ts");
  writeFileSync(badBoxClient,
    'import type { Box } from "@fixture/box";\n' +
    'export function badBox(box: Box): number { return box.flag; }\n');
  const rejectedBox = check(badBoxClient, pairConfig);
  assert.equal(rejectedBox.status, "unverified", JSON.stringify(rejectedBox));
  assert.equal(rejectedBox.phase, "search");
  assert.match(rejectedBox.detail, /evidence search failed/);
  const badInvokeClient = join(pairDir, "bad-invoke-client.ts");
  writeFileSync(badInvokeClient,
    'import type { CallableBox } from "@fixture/box";\n' +
    'export function badInvoke(box: CallableBox): number { return box.invoke(1); }\n');
  const rejectedInvoke = check(badInvokeClient, pairConfig);
  assert.equal(rejectedInvoke.status, "unverified", JSON.stringify(rejectedInvoke));
  assert.equal(rejectedInvoke.phase, "search");
  const detachedClient = join(pairDir, "detached-method-client.ts");
  writeFileSync(detachedClient,
    'import type { WithMethod } from "@fixture/box";\n' +
    'export function detached(box: WithMethod): boolean { const read = box.read; return read(); }\n');
  const detached = check(detachedClient, pairConfig);
  assert.equal(detached.status, "unverified", JSON.stringify(detached));
  assert.equal(detached.phase, "search");
  assert.match(detached.detail, /method-receiver/);
  const badPairClient = join(pairDir, "bad-pair-client.ts");
  writeFileSync(badPairClient,
    'import type { Pair } from "@fixture/box";\n' +
    'export function badPair(pair: Pair): number { return pair[0]; }\n');
  const rejectedPair = check(badPairClient, pairConfig);
  assert.equal(rejectedPair.status, "unverified", JSON.stringify(rejectedPair));
  assert.equal(rejectedPair.phase, "search");
  // Forms the fragment cannot state are refused where the graph reaches them.
  for (const [name, refusal] of [
    ["NamedPair", /named tuple members are outside the fragment in box.ts#NamedPair/],
    ["NestedMethod", /an optional method of a nested type literal has no declaration as its receiver in box.ts#NestedMethod/],
    ["GenericCall", /generic or incomplete call signature in box.ts#GenericCall/],
  ] as const)
    assert.throws(() => graphOf(`import type { ${name} } from "@fixture/box";`), refusal);
  // A generic method is a scheme: a call through it is established at the
  // instance it names, and at no other.
  assert.ok(graphOf('import type { GenericMethod } from "@fixture/box";').definitions.length > 0);
  const genericMethodClient = join(pairDir, "generic-method-client.ts");
  writeFileSync(genericMethodClient,
    'import type { GenericMethod } from "@fixture/box";\n' +
    "export function call(m: GenericMethod): boolean { return m.read(true); }\n");
  const genericMethodCall = check(genericMethodClient, pairConfig);
  assert.equal(genericMethodCall.status, "verified", JSON.stringify(genericMethodCall));
  writeFileSync(genericMethodClient,
    'import type { GenericMethod } from "@fixture/box";\n' +
    "export function call(m: GenericMethod): number { return m.read(true); }\n");
  const wrongInstance = check(genericMethodClient, pairConfig);
  assert.equal(wrongInstance.status, "unverified", JSON.stringify(wrongInstance));
  assert.equal(wrongInstance.phase, "search");
  const optionalMethodClient = join(pairDir, "optional-method-client.ts");
  writeFileSync(optionalMethodClient,
    'import type { OptionalMethod } from "@fixture/box";\n' +
    'export function callOptional(box: OptionalMethod): boolean { return box.read(); }\n');
  const checkedOptionalMethod = check(optionalMethodClient, pairConfig);
  assert.equal(checkedOptionalMethod.status, "verified", JSON.stringify(checkedOptionalMethod));
  const wrongRestClient = join(pairDir, "wrong-rest-client.ts");
  writeFileSync(wrongRestClient,
    'import type { RestMethod } from "@fixture/box";\n' +
    'export function wrongRest(box: RestMethod): boolean { return box.accepts("bad"); }\n');
  const rejectedRest = check(wrongRestClient, pairConfig);
  assert.equal(rejectedRest.status, "unverified", JSON.stringify(rejectedRest));
  assert.equal(rejectedRest.phase, "search");
  const wrongOverloadClient = join(pairDir, "wrong-overload-client.ts");
  writeFileSync(wrongOverloadClient,
    'import type { Overloaded } from "@fixture/box";\n' +
    'export function wrongOverload(fn: Overloaded): boolean { return fn(true); }\n');
  const rejectedOverload = check(wrongOverloadClient, pairConfig);
  assert.equal(rejectedOverload.status, "unverified", JSON.stringify(rejectedOverload));
  assert.equal(rejectedOverload.phase, "search");
  for (const [name, detail] of [
    ["ReadonlyCallable", /callable object with index or readonly field/],
    ["IndexedCallable", /callable object with index or readonly field/],
  ] as const) {
    const client = join(pairDir, `unsupported-${name}.ts`);
    writeFileSync(client,
      `import type { ${name} } from "@fixture/box";\n` +
      `export function keep(value: ${name}): ${name} { return value; }\n`);
    const result = check(client, pairConfig);
    assert.equal(result.status, "unverified", JSON.stringify(result));
    assert.equal(result.phase, "search");
    assert.match(result.detail, detail);
  }
  assert.deepEqual(graphOf('import type { Derived } from "@fixture/box";').definitions.map(d =>
    [d.declaration.name, d.bases.length]), [["Derived", 1], ["Box", 0]]);
  // Merged declarations have no single equation: refused, as TypeScript sees them.
  const merged = "export interface Merge { readonly flag: boolean; }\n" +
    "export interface Merge { readonly label: string; }\n";
  writeFileSync(join(pairDir, "merged.ts"), merged);
  const mergedClient = join(pairDir, "merged-client.ts");
  writeFileSync(mergedClient,
    'import type { Merge } from "@fixture/merged";\n' +
    'export function readMerged(value: Merge): boolean { return value.flag; }\n');
  assert.throws(() => parseFile(mergedClient, false, pairConfig),
    /TypeScript found 2 declarations for Merge/);
  // Code the graph uses must be code TypeScript accepts. Two star reexports
  // of one name: TypeScript reports TS2308 on the barrel (and would bind the
  // first); the import is refused there.
  writeFileSync(join(pairDir, "twice.ts"),
    "export * from './box.js';\nexport * from './labeled.js';\n");
  writeFileSync(join(pairDir, "labeled.ts"), "export interface Box { readonly other: number; }\n");
  assert.throws(() => graphOf('import type { Box } from "@fixture/twice";'),
    /TypeScript reports an error in twice.ts on the path to Box: .*already exported a member named 'Box'/);
  // An interface TypeScript rejects is not a contract: refused, not interpreted
  // as the empty conjunction of its incompatible fields.
  writeFileSync(join(pairDir, "wrong.ts"), "import type { Box } from './box.js';\n" +
    "export interface Wrong extends Box { readonly flag: string; }\n");
  assert.throws(() => graphOf("import type { Wrong } from './wrong.js';"),
    /TypeScript reports an error in wrong.ts#Wrong: .*incorrectly extends/);
  // Errors elsewhere in a used file are not the graph's: the Json route passes
  // through upstream modules with unrelated errors (missing snapshot modules).
  writeFileSync(genericClient,
    'import type { A } from "@fixture/a";\n' +
    'export function wrong(value: A<boolean, number>): boolean { return true; }\n');
  assert.throws(() => parseFile(genericClient, false, pairConfig),
    /type 'A' needs 1 type argument/);
  const boundDefinitions = graphOf("import type { Bound } from '@fixture/a';").definitions;
  assert.deepEqual(boundDefinitions.map(d =>
    [d.declaration.name, referencesInDefinition(d).map(r => r.target.name)]), [
    ["Bound", ["B"]], ["B", ["A"]], ["A", ["B"]],
  ]);
  const bound = boundDefinitions[0]?.parameters[0]?.bound;
  assert(bound && bound.k === "reference" && bound.args[0]?.k === "atom");
  assert.equal(bound.args[0].name, "number");
  writeFileSync(join(pairDir, "missing.ts"), "export type MissingEdge = NoDefinition;");
  assert.throws(() => graphOf("import type { MissingEdge } from './missing.js';"),
    /TypeScript reports an error in missing.ts#MissingEdge: Cannot find name 'NoDefinition'/);
  writeFileSync(join(pairDir, "conditional.ts"),
    "export type Conditional<T> = T extends boolean ? number : string;");
  assert.throws(() => graphOf("import type { Conditional } from './conditional.js';"),
    /type outside the fragment \(ConditionalType\) in conditional.ts#Conditional/);
  // A second global declaration merges with the first, as TypeScript merges
  // it: one equation with both declarations' members, identified by the first.
  writeFileSync(join(pairDir, "other-global.d.ts"), "interface GlobalBox { readonly other: number; }\n");
  const mergedBox = parseFile(boxClient, false, pairConfig).declarations.definitions
    .find(d => d.declaration.name === "GlobalBox")?.expression;
  assert(mergedBox?.k === "object");
  assert.deepEqual(mergedBox.fields.map(f => f.name), ["flag", "other"]);
  // Merged declarations must agree on their type parameters.
  writeFileSync(join(pairDir, "other-global.d.ts"), "interface GlobalBox<T> { readonly other: T; }\n");
  assert.throws(() => parseFile(boxClient, false, pairConfig), /TypeScript reports an error|different type parameters/);
  closeParser();
}
function must<T>(value: T | null | undefined, message: string): T {
  assert.ok(value !== null && value !== undefined, message);
  return value;
}
/** The iterator protocol a program's iterable runs, as JavaScript runs the
 * verified example: its iterator's `return` is called on `break`, `return`
 * and a throw out of the body, and not at the end or on `continue`; a throw
 * out of the body wins over one out of the close. The parser's lowering
 * (`protocolForOf`) calls `return` exactly there. */
function checkIteratorProtocol(): void {
  const source = stripTypes(readFileSync(join(here, "examples", "for-of-program-iterable.ts"), "utf8"))
    .replace(/^export /gm, "");
  const run = (expression: string): unknown =>
    vm.runInNewContext(`${source}\n${expression}`, {}, { timeout: 1000 });
  const list = "new LinkedList(new Cell(1, new Cell(5, new Cell(9, null))), { closed: 0 })";
  const closes = (call: string) => run(`const l = ${list}; const r = ${call}; JSON.stringify([r, l.log.closed])`);
  assert.equal(closes("sum(l)"), "[15,0]");
  assert.equal(closes("firstAbove(l, 3)"), "[5,1]");
  assert.equal(closes("firstOver(l, 3)"), "[5,1]");
  assert.equal(closes("skipSmall(l, 3)"), "[14,0]");
  assert.equal(run("const log = { closed: 0 }; JSON.stringify([firstEven(new Countdowns(5, log)), log.closed])"), "[4,1]");
  assert.equal(run("bodyThrows(new Brittle()).message"), "body");
}
// Execute the same sources the verifier refuses. These exercise trusted
// native contracts, not Lean's proved rules: callbacks can mutate aliases and
// conversion invokes methods with arguments absent from TypeScript's type.
for (const [file, call] of [
  ["invalid-native-find-mutation", "wrong([1, 2], { value: 0 })"],
  ["invalid-native-map-mutation", "wrong([1, 2], { value: 0 })"],
  ["invalid-native-join-coercion", "wrong({ value: 0 })"],
  ["invalid-native-sort-coercion", "wrong({ value: 0 })"],
  // What `%Iterate:ForIn%`'s step read is not what a later read finds.
  ["invalid-for-in-entry-call", "wrong({ a: 1 }, (v) => { delete v.a; })"],
  ["invalid-for-in-entry-field", "wrong({ inner: { a: 1, b: 2 } }, {})"],
  ["invalid-for-in-entry-rebound", "wrong({ a: 1, b: 2 }, {})"],
]) {
  const source = stripTypes(readFileSync(join(here, "examples", `${file}.ts`), "utf8"))
    .replace(/^export /gm, "");
  assert.equal(vm.runInNewContext(`${source}\n${call}`, {}, { timeout: 1000 }), undefined,
    `${file}: the actual source returns undefined despite its number contract`);
}
{
  const source = stripTypes(readFileSync(join(here, "examples", "native-sort-contracts.ts"), "utf8"))
    .replace(/^export /gm, "");
  assert.equal(vm.runInNewContext(`${source}\nnoCoercion({ value: 7 })`, {}, { timeout: 1000 }), 7,
    "an explicit comparator never invokes the element's invalid conversion method");
}
// Object.assign writes a function's `name`, which is not writable: it throws.
{
  const source = stripTypes(readFileSync(join(here, "examples", "invalid-function-fields-inferred.ts"), "utf8"))
    .replace(/^export /gm, "");
  assert.throws(() => vm.runInNewContext(`${source}\nnamed()`, {}, { timeout: 1000 }), /read only property 'name'/);
}
// Forwarding through an ordinarily annotated binding does not prevent the
// callback from shortening the source; the final map position remains a hole.
{
  const source = stripTypes(readFileSync(join(here, "examples", "invalid-callback-effect-forwarding.ts"), "utf8"))
    .replace(/^export /gm, "");
  assert.equal(vm.runInNewContext(`${source}\nconst result = wrong([1, 2]); JSON.stringify([result.length, 0 in result, 1 in result])`, {}, { timeout: 1000 }), "[2,true,false]");
}
// These deliberately violate the external-array contract. Even numeric
// tuples can run arbitrary code if their conversion hooks are replaced.
{
  const source = stripTypes(readFileSync(join(here, "examples", "native-array-conversion.ts"), "utf8"))
    .replace(/^export /gm, "");
  for (const [key, expected] of [["toString", undefined], ["Symbol.toPrimitive", "string"]]) {
    const member = key === "toString" ? '"toString"' : "Symbol.toPrimitive";
    assert.equal(vm.runInNewContext(`${source}\nlet seen = 0; const value = [1, 2];
      value[${member}] = function(required) { seen = required; return "x"; };
      tuples([value, value]); seen;`, {}, { timeout: 1000 }), expected);
  }
}
// Reading a hole gives undefined, so it satisfies the input annotation. map
// skips it even when the callback preserves the heap and returns a number.
{
  const source = stripTypes(readFileSync(join(here, "examples", "invalid-map-hole-coalescing.ts"), "utf8"))
    .replace(/^export /gm, "");
  assert.equal(vm.runInNewContext(`${source}\nconst xs = [1, 2]; delete xs[1];
    const result = coalescingCallback(xs); JSON.stringify([result.length, 1 in result, result[1]])`,
    {}, { timeout: 1000 }), "[2,false,null]");
}
// The input has Array.prototype and dense elements, with no accessors or
// proxies. Its extra own constructor is excluded by the ordinary-construction
// invariant. These controls explain why the external-code assumption matters;
// they deliberately call the verified functions outside their input contracts.
{
  const source = stripTypes(readFileSync(join(here, "examples", "ordinary-array-construction.ts"), "utf8"))
    .replace(/^export /gm, "");
  const setup = `class Result { length = "not a number"; }
    class Constructor { static [Symbol.species] = Result; }
    const xs = [1, 2]; xs.constructor = Constructor;
    if (Object.getPrototypeOf(xs) !== Array.prototype || !(0 in xs) || !(1 in xs))
      throw Error("invalid species witness input");`;
  for (const call of ["mappedLength(xs)", "filteredLength(xs)"])
    assert.equal(vm.runInNewContext(`${source}\n${setup}\n${call}`, {}, { timeout: 1000 }), "not a number");
  assert.equal(vm.runInNewContext(`${source}\n${setup}\nArray.isArray(slicedArray(xs))`, {}, { timeout: 1000 }), false);
  // Species runs before the first callback: preserving every callback's
  // entry heap still does not preserve the traversal's original index range.
  assert.equal(vm.runInNewContext(`const xs = [1, 2];
    class Species { constructor(n) { xs.length = 0; return new Array(n); } }
    class Constructor { static [Symbol.species] = Species; }
    xs.constructor = Constructor;
    const result = xs.map(x => x);
    JSON.stringify([result.length, 0 in result, 1 in result]);`, {}, { timeout: 1000 }), "[2,false,false]");
}
let erasedContract = "";
let good = "";
let generic = "";
let genericClosure = "";
let twoCalls = "";
let bounded = "";
let returned = "";
let captured = "";
let callback = "";
// `Array.prototype`'s contract is TypeScript's declarations through the
// overlay: every listed member is read, each quantified over the element and
// taking the array as its receiver, readonly unless it mutates. A declaration
// that differs from the reviewed text is refused.
{
  const arrays = join(here, "examples", "values.ts");
  const doc = collectDeclarations(arrays, { arrays: [0, 0] });
  const proto = doc.definitions.find(d => d.declaration.module === "skjs/array-prototype");
  assert(proto && proto.expression.k === "object");
  // A computed key is the symbol it names: `[Symbol.iterator]` is `Symbol.iterator`.
  const keyText = (name: string | { symbol: number }) =>
    typeof name === "string" ? name : `[Symbol.${doc.symbols[name.symbol]?.name}]`;
  const methods = proto.expression.fields.filter(f => !f.optional);
  assert.deepEqual(methods.map(f => keyText(f.name)), arrayOverlay.map(e => e.name));
  const absentHooks = proto.expression.fields.filter(f => f.optional);
  assert.equal(absentHooks.length, 1);
  assert.equal(keyText(must(absentHooks[0], "conversion hook absence").name), "[Symbol.toPrimitive]");
  assert(absentHooks.every(f => f.readonly && f.type.k === "atom" && f.type.name === "undefined"));
  for (const field of methods) {
    const entry = arrayOverlay.find(e => e.name === keyText(field.name));
    // The member's own binders lead; the element binder `T` is last.
    assert(field.readonly && field.type.k === "scheme" && field.type.binders.at(-1)?.name === "T");
    const receiver = field.type.signatures[0]?.receiver;
    assert(receiver?.k === "array" && receiver.element.k === "binder");
    assert.equal(receiver.readonly, entry?.from === "ReadonlyArray", `${String(field.name)} receiver`);
  }
  const changed = arrayOverlay.map(e => e.name === "reduce"
    ? { ...e, signature: e.signature.replace("initialValue: U", "initialValue?: U") } : e);
  assert.throws(() => collectDeclarations(arrays, { arrays: [0, 0], arrayOverlay: changed }),
    /is not declared as reviewed/);
  const unsound = [{ name: "reduce", from: "ReadonlyArray" as const,
    signature: "reduce(callbackfn: (previousValue: T, currentValue: T, currentIndex: number, array: readonly T[]) => T): T;" }];
  assert.doesNotThrow(() => collectDeclarations(arrays, { arrays: [0, 0], arrayOverlay: unsound }),
    "the overlay, not the reader, decides which overloads are trusted");
  // A member the project's library does not declare is absent, not refused.
  const absent = collectDeclarations(arrays, { arrays: [0, 0], arrayOverlay: [
    { name: "notDeclared", from: "ReadonlyArray", signature: "notDeclared(): T;" }] });
  const absentProto = absent.definitions.find(d => d.declaration.module === "skjs/array-prototype");
  assert(absentProto?.expression.k === "object" && absentProto.expression.fields.length === 0);
  process.stdout.write("array prototype: overlay members read from TypeScript's declarations\n");
}
let inference = "";
let indexed = "";
let moduleFunctions = "";
let moduleInit = "";
let genericModule = "";
let sumMapper = "";
let sumConstructor = "";
let sumCollections = "";
let localClosure = "";
let mutatingClosure = "";
let exactKeys = "";
let restKeys = "";
let variadicOffer = "";
let explicitCalls = "";
let classGeneric = "";
let verifiedFunctions = 0;
const outcomes = await pooled(cases, runCase);
for (const [i, test] of cases.entries()) {
  const settled = outcomes[i];
  if (settled.status === "rejected") throw settled.reason;
  const result = expectOutcome(test, settled.value);
  if (result.status === "verified")
    verifiedFunctions += result.functions.length;
  process.stdout.write(
    `${test.file}: ${result.status} (${result.phase}, ${test.kind})\n`,
  );
  if (test.file === "generic-rest") checkGenericRest(verifier, result.artifacts);
  if (test.file === "overloads") checkOverloads(verifier, result.artifacts);
  if (test.file === "invalid-generic-contract-erasure") erasedContract = result.artifacts;
  if (test.file === "values") good = result.artifacts;
  if (test.file === "default-parameter-scope") checkDefaults(verifier, result.artifacts);
  if (test.file === "for-of-program-iterable") checkIteratorProtocol();
  if (test.file === "invalid-default-invocation") checkEarlyDefault(verifier, result.artifacts);
  if (test.file === "generic-default") checkSchemeDefaults(verifier, result.artifacts);
  if (test.file === "generic-inferred") generic = result.artifacts;
  if (test.file === "generic-closure") genericClosure = result.artifacts;
  if (test.file === "generic-two-calls") twoCalls = result.artifacts;
  if (test.file === "generic-bounded") bounded = result.artifacts;
  if (test.file === "generic-returned") returned = result.artifacts;
  if (test.file === "generic-captured-store") captured = result.artifacts;
  if (test.file === "generic-callback") callback = result.artifacts;
  if (test.file === "module-functions") moduleFunctions = result.artifacts;
  if (test.file === "module-init") moduleInit = result.artifacts;
  if (test.file === "generic-module-calls") genericModule = result.artifacts;
  if (test.file === "generic-inference") inference = result.artifacts;
  if (test.file === "index-signature") indexed = result.artifacts;
  if (test.file === "sum-mapper-signature") sumMapper = result.artifacts;
  if (test.file === "sum-constructor-field") sumConstructor = result.artifacts;
  if (test.file === "sum-collections") sumCollections = result.artifacts;
  if (test.file === "closure-result-contract") localClosure = result.artifacts;
  if (test.file === "closure-graph-captured-cell") mutatingClosure = result.artifacts;
  if (test.file === "invalid-writable-dictionary-exact-keys") exactKeys = result.artifacts;
  if (test.file === "invalid-writable-dictionary-rest-keys") restKeys = result.artifacts;
  if (test.file === "variadic-offer-sync") variadicOffer = result.artifacts;
  if (test.file === "explicit-type-arguments") explicitCalls = result.artifacts;
  if (test.file === "class-generic-method") classGeneric = result.artifacts;
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
  const ast = join(good, "raw-graph-annotation.json");
  // The source states type terms: neither a graph label nor a claim. The
  // producer's own claims are offered, so the refusal is the annotation's.
  for (const [retType, refusal] of [
    [{ a: "graph", label: 4 }, /source cannot state an internal graph label/],
    [{ top: false, atoms: [{ a: "boolean" }] }, /a source annotation is a type term, not a claim/],
  ] as const) {
    Object.assign(first, { retType });
    writeFileSync(ast, JSON.stringify(forged));
    const produced: SpawnSyncReturns<string> = spawnSync(verifier,
      ["--produce-source-claims", ast, join(good, "claims.json"), fragment.file,
        join(good, "raw-graph-evidence.json"), "10"], { encoding: "utf8" });
    assert.equal(produced.status, 1);
    assert.match(produced.stderr, refusal);
  }
  process.stdout.write("raw graph label and claim-shaped annotation as a source annotation: refused\n");
}
const forgedImport = join(good, "forged-import.json");
writeFileSync(forgedImport, JSON.stringify({ ...fragment,
  declarations: must(pinnedDeclarationDocument, "the pinned Json import document") }));
// The claims name declarations by their position in the fragment's
// document: under another import closure they are other types, which the
// evidence does not justify.
assert.match(invoke(join(good, "claims.json"), join(good, "evidence.json"), good,
  forgedImport), /source evidence does not justify/);
process.stdout.write("forged import closure: refused\n");
// Each label tree has one spelling and names a declaration of the fragment's
// document; a binder is a label, never a row the producer writes.
{
  const path = join(recursiveJson, "claims.json");
  const claims: SourceClaims = JSON.parse(readFileSync(path, "utf8"));
  const nullary = Number(must(/\{"decl":(\d+)\}/.exec(readFileSync(path, "utf8")),
    "a nullary declaration's label")[1]);
  const param = must(claims.functions[0]?.params[0], "a parameter's claim");
  const forge = (name: string, type: unknown, row: unknown[] = []) => {
    const forged = join(recursiveJson, `forged-label-${name}.json`);
    writeFileSync(forged, JSON.stringify({ ...claims, types: [...claims.types, ...row] },
      (_key, value: unknown) => value === param.type ? type : value));
    return invoke(forged, join(recursiveJson, "evidence.json"), recursiveJson);
  };
  for (const [name, type, refusal] of [
    ["unknown-field", [{ decl: nullary, span: [0, 0] }], /unexpected fields/],
    ["nullary-arguments", [{ decl: nullary, args: [] }], /a nullary declaration's label leaves its arguments out/],
    ["missing-declaration", [{ decl: 1000 }], /a declaration's label names no declaration/],
    ["missing-arguments", [{ decl: nullary, args: [[3]] }], /one argument per parameter/],
    ["order", [{ binder: "T" }, 3], /canonical order/],
    ["one-part-meet", [{ meet: [[3]] }], /at least two parts/],
  ] as const) {
    assert.match(forge(name, type), refusal);
    process.stdout.write(`label tree (${name}): refused\n`);
  }
  assert.match(forge("parameter-row", [claims.types.length],
    [{ param: claims.types.length, name: "T", kind: "value" }]),
    /a producer's row is a clause row or a scheme row/);
  process.stdout.write("a binder written as a producer row: refused\n");
}
{
  const ast: Ast = JSON.parse(readFileSync(join(recursiveJson, "fragment.json"), "utf8"));
  const parameter = ast.functions[0]?.params[0];
  assert.ok(parameter?.type.k === "reference" && parameter.type.reference.name === "Json");
  const labelled: unknown = { a: "graph", label: 4 };
  Object.assign(parameter, { type: labelled });
  const forged = join(recursiveJson, "forged-internal-label.json");
  writeFileSync(forged, JSON.stringify(ast));
  assert.match(invoke(join(recursiveJson, "claims.json"),
    join(recursiveJson, "evidence.json"), recursiveJson, forged),
    /source cannot state an internal graph label/);
  process.stdout.write("source-authored internal graph label: refused\n");
}
// Bypass the producer's refusal: manufacture its old proposal by erasing
// the method in a copy of the AST. Both verifier entry points must still
// refuse the ORIGINAL contract before accepting any such proposal/evidence.
{
  const ast: Ast = JSON.parse(readFileSync(join(erasedContract, "fragment.json"), "utf8"));
  const declaration = ast.declarations?.definitions.find(d => d.declaration.name === "Witness");
  assert(declaration?.expression.k === "object");
  const member = declaration.expression.fields.find(f => f.name === "choose");
  assert(member?.type.k === "scheme");
  member.type = { k: "atom", name: "unknown", span: member.type.span };
  const weakened = join(erasedContract, "weakened.json");
  writeFileSync(weakened, JSON.stringify(ast));
  const proposal = spawnSync(join(here, "_build/default/producer.exe"), [weakened],
    { encoding: "utf8", timeout: 30_000 });
  assert.equal(proposal.status, 0, proposal.stderr);
  const claims = join(erasedContract, "forged-claims.json");
  const evidence = join(erasedContract, "forged-evidence.json");
  writeFileSync(claims, proposal.stdout);
  writeFileSync(evidence, "{}");
  const searched = spawnSync(verifier, ["--produce-source-claims",
    join(erasedContract, "fragment.json"), claims, join(erasedContract, "source.ts"), evidence, "12"],
    { encoding: "utf8", timeout: 30_000 });
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  assert.match(searched.stdout + searched.stderr, /generic contract.*cannot be erased/);
  assert.match(invoke(claims, evidence, erasedContract), /generic contract.*cannot be erased/);
  process.stdout.write("unsupported generic contract: refused independently of the producer\n");
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

// A method or constructor claim is compared with its annotation by meaning, so
// another row for Values<number> is admitted; a domain wider than the
// annotation, here one that also admits undefined, is still refused.
for (const [artifacts, arity, refusal] of [
  [sumMapper, 2, /closure signature claim is outside the source annotation/],
  [sumConstructor, 1, /construct signature claim is outside the source annotation/],
] as const) {
  const claims: SourceClaims = JSON.parse(readFileSync(join(artifacts, "claims.json"), "utf8"));
  // mapEntry's arrow, or AddIndex's construct signature: its last parameter.
  const domains = claims.types.flatMap((row) => row.flatMap((clause) =>
    typeof clause !== "object" ? [] :
    "arrs" in clause ? clause.arrs.arrows.map((s) => s.arguments) :
    "ctors" in clause ? clause.ctors.signatures.map(([params]) => params) : []));
  const params = must(domains.find((ps) => ps.length === arity), "the claimed signature");
  must(params.at(-1), "a claimed parameter").unshift(3);
  const forged = join(artifacts, "forged-wider-domain.json");
  writeFileSync(forged, JSON.stringify(claims));
  assert.match(invoke(forged, join(artifacts, "evidence.json"), artifacts), refusal);
  process.stdout.write(`a signature claim wider than its annotation (arity ${arity}): refused\n`);
}

// A bound method's variadic signature is covered by the member's when the
// claimed rest is within the member's (`CoveredRestUsing`): `merge`'s rest,
// the producer's own row for `EagerCollection<string, number>[]`, admits the
// declared rest's lists. Widened to admit strings too, the claim is refused
// at the bound member, by search and by the checker.
{
  const claims: SourceClaims = JSON.parse(readFileSync(join(sumCollections, "claims.json"), "utf8"));
  const rest = must(claims.types.flatMap((row) => row.flatMap((clause) =>
    typeof clause === "object" && "pack" in clause ? [clause.pack.first] : []))
    .find((t) => t.rest !== null), "merge's claimed rest").rest;
  must(rest, "the rest's labels").unshift(4);
  const forged = join(sumCollections, "forged-wider-rest.json");
  writeFileSync(forged, JSON.stringify(claims));
  const searched = spawnSync(verifier, ["--produce-source-claims", join(sumCollections, "fragment.json"),
    forged, join(sumCollections, "source.ts"), join(sumCollections, "forged-evidence.json"), "12"],
    { encoding: "utf8", timeout: 30_000 });
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  const member = readFileSync(join(sumCollections, "source.ts"), "utf8").indexOf("cs.input1.merge");
  assert.ok((searched.stdout + searched.stderr).includes(
    `source expression obligation at [${member},${member + "cs.input1.merge".length})`),
    searched.stdout + searched.stderr);
  assert.match(invoke(forged, join(sumCollections, "evidence.json"), sumCollections), /does not justify/);
  process.stdout.write("a bound method's rest claim wider than the member's: refused\n");
}

// Explicit type arguments, written as another type than the one the claimed
// instance fits: on a method call, `reduce<number | null>` written as
// `reduce<number | null | string>`, and on a plain call, `same<number |
// boolean>` written as `same<number | boolean | string>`. The claims are
// unchanged, so each call's instance fits its actuals but is not the one the
// call states.
const forgeTypeArgument = (artifacts: string, kind: "invoke" | "apply"): string => {
  const ast: { k?: string; typeArgs?: { k: string; parts: unknown[]; span: unknown }[] } =
    JSON.parse(readFileSync(join(artifacts, "fragment.json"), "utf8"));
  const calls: typeof ast[] = [];
  const visit = (j: unknown): void => {
    if (Array.isArray(j)) j.forEach(visit);
    else if (j && typeof j === "object") {
      if ((j as typeof ast).k === kind && (j as typeof ast).typeArgs) calls.push(j as typeof ast);
      Object.values(j).forEach(visit);
    }
  };
  visit(ast);
  const [typeArg] = must(calls[0]?.typeArgs, "the call's type arguments");
  must(typeArg, "the type argument").parts.push({ k: "atom", name: "string", span: typeArg.span });
  const forgedAst = join(artifacts, "forged-type-argument.json");
  writeFileSync(forgedAst, JSON.stringify(ast));
  return forgedAst;
};
for (const [artifacts, kind] of [[localClosure, "invoke"], [explicitCalls, "apply"]] as const)
  assert.match(invoke(join(artifacts, "claims.json"), join(artifacts, "evidence.json"), artifacts,
    forgeTypeArgument(artifacts, kind)),
    /the call's instance is not the one its explicit type arguments state/);
process.stdout.write("an instance other than the explicit type argument, method and plain calls: refused\n");

// A producer cannot manufacture heap preservation. The same ordinary
// definition check accepts the pure callback and refuses the captured write.
for (const [artifacts, arity, accepted] of [
  [localClosure, 2, true], [mutatingClosure, 0, false],
] as const) {
  const claims: SourceClaims = JSON.parse(readFileSync(join(artifacts, "claims.json"), "utf8"));
  const arrow = must(claims.types.flatMap(row => row.flatMap(clause =>
    typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : []))
    .find(s => s.arguments.length === arity), "the callback contract");
  arrow.effect = "preservesInputHeap";
  const input = join(artifacts, "qualified-callback.json");
  const output = join(artifacts, "qualified-callback-evidence.json");
  writeFileSync(input, JSON.stringify(claims));
  const produce = spawnSync(verifier, ["--produce-source-claims", join(artifacts, "fragment.json"),
    input, join(artifacts, "source.ts"), output, "12"], {encoding: "utf8", timeout: 30_000});
  assert.ifError(produce.error);
  assert.equal(produce.signal, null);
  assert.equal(produce.status, accepted ? 0 : 1, produce.stdout + produce.stderr);
  if (accepted) {
    const consume = spawnSync(verifier, ["--check-source-claims", join(artifacts, "fragment.json"),
      input, join(artifacts, "source.ts"), output], {encoding: "utf8", timeout: 30_000});
    assert.ifError(consume.error);
    assert.equal(consume.status, 0, consume.stdout + consume.stderr);
  } else {
    const failure = readDiagnostic(produce.stdout + produce.stderr);
    assert.ok(failure && failure.kind === "node-typing", "a failed effect must name the callable's typing obligation");
    assert.ok(failure.source?.sourceMap?.pos, "the failed callable must have a source location");
    assert.match(invoke(input, join(artifacts, "evidence.json"), artifacts), /does not justify/);
  }
  process.stdout.write(`callback heap-preservation claim: ${accepted ? "certified" : "captured write refused"}\n`);
}

// An unannotated closure's claimed result is checked against its body, not
// taken from the producer on trust.
{
  const claims: SourceClaims = JSON.parse(readFileSync(join(localClosure, "claims.json"), "utf8"));
  const evidence = join(localClosure, "evidence.json");
  // The closure's own arrow, two parameters to a number, claimed to return null.
  const own = must(claims.types.flatMap((row) => row.flatMap((clause) =>
    typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : []))
    .find((s) => s.arguments.length === 2), "the closure's own arrow");
  own.result = [0];
  const forged = join(localClosure, "forged-closure-result.json");
  writeFileSync(forged, JSON.stringify(claims));
  const searched = spawnSync(verifier, ["--produce-source-claims", join(localClosure, "fragment.json"),
    forged, join(localClosure, "source.ts"), join(localClosure, "forged-evidence.json"), "12"],
    { encoding: "utf8", timeout: 30_000 });
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  // The body, `p !== null ? p - c : c`, is a number, not the null
  // claimed: the closure's one node returns it at that result.
  const body = readFileSync(join(localClosure, "source.ts"), "utf8").indexOf("p !== null");
  assert.ok((searched.stdout + searched.stderr).includes(
    `source expression obligation at [${body},`), searched.stdout + searched.stderr);
  assert.match(invoke(forged, evidence, localClosure), /does not justify/);
  process.stdout.write("an unannotated closure's result claim its body does not meet: refused\n");
}

// A class's generic method, a closure the prototype holds, covers the
// instance type's member up to renaming the member's binders to the
// closure's: the renamed signatures must still follow from the closure's.
// The class's declaration tampered to promise a number where the closure
// returns its binder is refused at the construct code's return, where the
// fresh instance meets the instance type; the untampered one is derived there.
// `make` alone is kept, so the construct code is the first obligation.
{
  const source = readFileSync(join(classGeneric, "source.ts"), "utf8");
  const claims: SourceClaims = JSON.parse(readFileSync(join(classGeneric, "claims.json"), "utf8"));
  claims.functions = claims.functions.filter((f) => f.name === "make");
  const makeClaims = join(classGeneric, "make-claims.json");
  writeFileSync(makeClaims, JSON.stringify(claims));
  const fragment: unknown = JSON.parse(readFileSync(join(classGeneric, "fragment.json"), "utf8"));
  assert.ok(fragment && typeof fragment === "object" && "functions" in fragment &&
    Array.isArray(fragment.functions));
  fragment.functions = fragment.functions.filter((f: unknown) =>
    f && typeof f === "object" && "name" in f && f.name === "make");
  const kept = JSON.stringify(fragment);
  const at = source.indexOf("pick<V>(a: V): V") + "pick<V>(a: V): ".length;
  const declared = `"result":{"k":"binder","name":"V","span":[${at},${at + 1}]}`;
  assert.ok(kept.includes(declared), "pick's declared result");
  const search = (name: string, text: string) => {
    const ast = join(classGeneric, `${name}.json`);
    writeFileSync(ast, text);
    return spawnSync(verifier, ["--produce-source-claims", ast, makeClaims, join(classGeneric, "source.ts"),
      join(classGeneric, `${name}-evidence.json`), "12"], { encoding: "utf8", timeout: 30_000 });
  };
  const derived = search("make-only", kept);
  assert.equal(derived.status, 0, derived.stdout + derived.stderr);
  const refused = search("forged-member-result",
    kept.replace(declared, '"result":{"k":"atom","name":"number","span":[0,0]}'));
  assert.equal(refused.status, 1, refused.stdout + refused.stderr);
  const ctor = source.indexOf("class Helper") + "class ".length;
  assert.ok((refused.stdout + refused.stderr).includes(
    `source expression obligation at [${ctor},${ctor + "Helper".length}): evidence search failed: no derivation of its return-contract claim`),
    refused.stdout + refused.stderr);
  process.stdout.write("a class's generic method whose closure does not cover the declared member after renaming: refused\n");
}

// A writable index is never met through an own-key bound: a callee holding
// the object as a writable dictionary may add a key the bound says is absent.
// Claims forged to state one, the literal's exact keys (none) or the rest's
// lacking the pattern's key `x`, are refused at the call handing the object to
// the callee. Run as JavaScript with a callee that stores `x`, each function
// returns the string stored, where its result claims `number | undefined`.
for (const [artifacts, file, name, call, clause] of [
  [exactKeys, "invalid-writable-dictionary-exact-keys", "o", "exact((d) => { d.x = 's'; })",
    (_str: number): Row[number] => ({ refs: { first: [], rest: [], views: [],
      bounds: [{ among: true, keys: [] }] } })],
  [restKeys, "invalid-writable-dictionary-rest-keys", "r", "rest((d) => { d.x = 's'; }, {})",
    (str: number): Row[number] => ({ dict: { first: [], rest: [], views: [],
      indexes: [["strings", [str]]], cells: [["strings", [str]]],
      bounds: [{ among: false, keys: ["x", "[[proto]]"] }] } })],
] as const) {
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const claims: SourceClaims = JSON.parse(readFileSync(join(artifacts, "claims.json"), "utf8"));
  const str = claims.types.findIndex((row) => row.length === 1 && row[0] === "str");
  assert.ok(str >= 0, "the string row");
  const label = claims.types.push([clause(str)]) - 1;
  const fn = must(claims.functions[0], "the function's claims");
  for (const entry of fn.entries)
    for (const b of entry.bindings) if (b.name === name) b.type = [label];
  // The object's own sites: its allocation (`{}`, `...r`) and every read of it.
  for (const e of fn.expressions)
    if ([name, "{}", `...${name}`].includes(source.slice(e.pos[0], e.pos[1]))) e.type = [label];
  const forged = join(artifacts, "forged-own-key-bound.json");
  writeFileSync(forged, JSON.stringify(claims));
  const searched = spawnSync(verifier, ["--produce-source-claims", join(artifacts, "fragment.json"),
    forged, join(artifacts, "source.ts"), join(artifacts, "forged-evidence.json"), "12"],
    { encoding: "utf8", timeout: 30_000 });
  const detail = searched.stdout + searched.stderr;
  assert.equal(searched.status, 1, detail);
  const site = source.indexOf(`add(${name})`);
  const at = /source expression obligation at \[(\d+),(\d+)\)/.exec(detail);
  assert.ok(at && Number(at[1]) >= site && Number(at[2]) <= site + `add(${name})`.length, detail);
  const run = stripTypes(readFileSync(join(here, "examples", `${file}.ts`), "utf8")).replace(/^export /gm, "");
  assert.equal(vm.runInNewContext(`${run}\n${call}`, {}, { timeout: 1000 }), "s");
  process.stdout.write(`a forged own-key bound on a writable dictionary (${file}): refused\n`);
}

// A closure is created at a variadic signature only when the signature's
// fixed parameters cover the ones its code binds: `named` binds one, so a
// claim offering it `(...rest: unknown[]) => void` is refused where it is
// created, not taken from the producer on trust.
{
  const claims: SourceClaims = JSON.parse(readFileSync(join(variadicOffer, "claims.json"), "utf8"));
  const offered = must(claims.types.flatMap((row) => row.flatMap((clause) =>
    typeof clause === "object" && "arrs" in clause && clause.arrs.arrows.length > 0
      ? clause.arrs.variadic ?? [] : []))
    .find((s) => s.arguments[0].length === 1), "the variadic signature `named` is offered");
  offered.arguments[0] = [];
  const forged = join(variadicOffer, "forged-variadic-offer.json");
  writeFileSync(forged, JSON.stringify(claims));
  assert.match(invoke(forged, join(variadicOffer, "evidence.json"), variadicOffer),
    /closure signature claim is outside the source annotation/);
  process.stdout.write("a closure claimed at a variadic signature binding into its rest: refused\n");
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
assert.equal(schemePoint.type.scheme.effect, "preservesInputHeap", "identity's inferred effect survives symbolic scheme export");
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

// A substitution names an instance of the scheme row, whose binder bounded by
// another is read as the meet of the two parameter rows, so at the instance as
// the meet of the two type arguments. Reversing one call's type arguments keeps
// them ground and complete, so the domain check passes, but the instance they
// name is not one the call's actuals meet: the evidence no longer justifies it.
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
  assert.match(said, /source evidence does not justify the extracted program/);
  process.stdout.write("tampered substituted bound: refused\n");
}

// A nested closure's claim is checked at the scheme's binder: a ground
// `() => boolean` claim fits every observed call and is still refused, since
// the body returns a `T`. And a callable over the binder is meaningful only
// inside its closure: the same claim placed on an expression outside it names
// a binder not in scope there.
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
  // The body `value` is a `T`, and the return-contract obligation at it asks
  // for a boolean: no derivation exists.
  const searched = spawnSync(verifier, ["--produce-source-claims", join(returned, "fragment.json"),
    groundedFile, join(returned, "source.ts"), join(returned, "forged-nested-evidence.json"), "12"],
    { encoding: "utf8", timeout: 30_000 });
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  const body = readFileSync(join(returned, "source.ts"), "utf8").indexOf("value;");
  assert.ok((searched.stdout + searched.stderr).includes(
    `source expression obligation at [${body},${body + "value".length}): evidence search failed: no derivation of its return-contract claim`),
    searched.stdout + searched.stderr);
  // The original evidence's labels are read against the forged claims'
  // equations, whose heads differ, so the evidence does not decode.
  assert.match(invoke(groundedFile, join(returned, "evidence.json"), returned),
    /NodeEvidence.*head \d+ takes \d+ arguments/);
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
    /is not in scope/);
  process.stdout.write("tampered rigid callable escape: refused\n");
}

// A captured cell keeps the contract its declaration states. Retyping it in the
// entry claim changes what the closure's code, checked once at its scheme, is
// entered with, so the check refuses: a capture is never retyped per call.
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
    /does not justify|evidence search failed/);
  process.stdout.write("tampered captured cell contract: refused\n");
}

// A module function is reached at its own annotated signature, which Lean
// reads from the source; a producer cannot retype the callee.
{
  const claims: SourceClaims = JSON.parse(readFileSync(join(moduleFunctions, "claims.json"), "utf8"));
  const source = readFileSync(join(moduleFunctions, "source.ts"), "utf8");
  const fn = must(claims.functions.find((f) => f.name === "twice"), "twice");
  const callee = source.indexOf("id(id(x))");
  const site = fn.expressions.find((e) => e.pos[0] === callee && e.pos[1] === callee + 2);
  assert.ok(site, "the outer callee's claim");
  const argument = fn.expressions.find((e) => e.pos[0] === source.indexOf("x))", callee));
  assert.ok(argument, "the argument's claim");
  site.type = argument.type;
  const file = join(moduleFunctions, "forged-callee.json");
  writeFileSync(file, JSON.stringify(claims));
  const refusal = invoke(file, join(moduleFunctions, "evidence.json"), moduleFunctions);
  process.stdout.write(`tampered module callee: refused (${refusal.trim().split("\n")[0]})\n`);
}

// The initialization unit's claims are checked like a function's: claiming
// the constant's initializer at another type is refused.
{
  const claims: SourceClaims = JSON.parse(readFileSync(join(moduleInit, "claims.json"), "utf8"));
  const source = readFileSync(join(moduleInit, "source.ts"), "utf8");
  assert.ok(claims.init, "the initialization unit's claims");
  const literal = source.indexOf("true;");
  const site = claims.init.expressions.find((e) => e.pos[0] === literal);
  assert.ok(site, "the initializer's claim");
  site.type = [0];
  const file = join(moduleInit, "forged-initializer.json");
  writeFileSync(file, JSON.stringify(claims));
  invoke(file, join(moduleInit, "evidence.json"), moduleInit);
  process.stdout.write("tampered module initializer: refused\n");
}

// A call to a generic module function names its instance; naming another
// changes the arrow its slot holds, which the evidence does not justify.
{
  const claims: SourceClaims = JSON.parse(readFileSync(join(genericModule, "claims.json"), "utf8"));
  const fn = must(claims.functions.find((f) => f.name === "both"), "both");
  const call = fn.expressions.find((e) => e.instantiate?.length);
  assert.ok(call?.instantiate, "an instantiated call");
  must(call.instantiate[0], "its type argument").type = [0];
  const file = join(genericModule, "forged-instance.json");
  writeFileSync(file, JSON.stringify(claims));
  invoke(file, join(genericModule, "evidence.json"), genericModule);
  process.stdout.write("tampered generic module instance: refused\n");
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

// A generic body is a graph request over its binders' parameter rows. Reusing
// valid evidence must not let an inferred local trust a forged point type.
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
  assert.match(p.stdout + p.stderr, /source evidence does not justify the extracted program and exact claims/);
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
 * The reader collects this producer too, by running `check` itself and
 * building its page from that run's outcome and artifacts. What is checked
 * here is that correspondence: the claims the reader carries are the ones the
 * producer wrote, the verdicts are the verifier's, and a source the pipeline
 * refuses is shown under that outcome, in its own words.
 */
const repositoryPath = (file: string) =>
  `verification/ocaml-producer/examples/${file}.ts`;
/** The page a bundle becomes. The annotated source reads back as the exact
 * source, and the page shows every function the manifest reports, with its
 * verdict and every expression claim at its span. */
const pageOf = (bundle: Bundle) => {
  assert.equal(parseReport(must(bundle.annotated, "the annotated source")).source, bundle.source);
  const page = fromBundle(bundle);
  assert.equal(page.source, bundle.source);
  assert.deepEqual(page.functions.map((f) => f.name), bundle.manifest.functions.map((f) => f.name));
  bundle.manifest.functions.forEach((f, i) => {
    const shown = must(page.functions[i], f.name);
    assert.equal(shown.status, bundle.manifest.results?.[i]?.status ?? "not-run");
    const spans = (ps: number[][]) => ps.map((p) => p.join(":")).sort();
    assert.deepEqual(
      spans(shown.sites.filter((s) => s.kind === "expression").map((s) => s.pos)),
      spans(f.expressions.map((e) => e.pos)));
  });
  return page;
};
{
  const shown = await analyse(repositoryPath("generic-default"), "ocaml");
  const results = shown.manifest.results ?? [];
  assert.deepEqual(results.map((r) => r.status), ["not-established"]);
  assert.notEqual(results[0]?.location, undefined);
  assert.match(JSON.stringify(results), /source expression obligation at \[400,419\)/);
  process.stdout.write("reader collection: a scheme default's bad write visibly refused\n");
  // The page shows the failure at the claim whose obligation stopped.
  const failed = must(pageOf(shown).functions[0], "the refused function");
  assert.equal(failed.status, "not-established");
  assert.equal(failed.failure?.kind, "expression-obligation");
  assert.deepEqual(failed.sites[failed.failure?.at ?? -1]?.pos, [400, 419]);
}
const collected = await analyse(repositoryPath("values"), "ocaml");
pageOf(collected);
assert.equal(collected.collection?.producer, "ocaml");
assert.equal(collected.collection?.producerRun, true);
assert.equal(collected.collection?.verified, true);
// The claims the report is built from are the producer's own, not a display
// shape derived from them: the document `check` wrote beside `values`, named by
// the file it is about.
assert.equal(collected.manifest.claimsSha256, createHash("sha256")
  .update(JSON.stringify({ ...original, file: repositoryPath("values") })).digest("hex"));
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
pageOf(collectedGeneric);
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

// Validation controls must reach validation and fail there. Failing there means
// failing an obligation, which the reader can show at its span; an adapter that
// throws before any obligation exists has refused, not validated, and the
// reader can point at nothing. Ranging over the inventory is what keeps a new
// control from escaping this. Explicit source/proposal refusal controls instead
// require that exact unsupported outcome and cannot claim to have checked a graph.
// A call of a generic module value at a type argument outside its bound
// fails a direct judgment, checked before any graph request exists.
const directControls = new Set([
  "invalid-explicit-type-argument-bound",
]);
let testedDirectProtocol = false;
const controls = cases.filter((c) => c.kind === "negative");
const shownControls = await pooled(controls, (c) => analyse(repositoryPath(c.file), "ocaml"));
for (const [i, control] of controls.entries()) {
  const settled = shownControls[i];
  if (settled.status === "rejected") throw settled.reason;
  const shown = settled.value;
  if (control.phase === "source" || control.phase === "proposal") {
    const outcome = shown.outcome;
    assert(outcome && outcome.status === "unsupported");
    assert.equal(outcome.phase, control.phase);
    if (control.diagnostic) assert.match(outcome.detail, control.diagnostic);
    assert.equal(shown.collection?.verified, false);
    assert.equal(shown.manifest.results?.length ?? 0, 0);
    continue;
  }
  // A control may hold correct functions beside the failing one: those it
  // calls are verified, and only the failing one is shown not established.
  const all = shown.manifest.results ?? [];
  const results = all.filter((r) => r.status !== "verified");
  assert.deepEqual(
    results.map((r) => r.status),
    ["not-established"],
    `${control.file}: reader must show exactly one function not established`,
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
      `${control.file}: a direct failure needs a structured judgment`,
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
      unscoped.judgment.actual = [wire.types.length];
      assert.equal(readDiagnostic(line(unscoped)),undefined,"a label outside the table is refused");
      const misplaced = structuredClone(wire);
      misplaced.sourceMap.pos = [0,0];
      assert.equal(readDiagnostic(line(misplaced)),undefined,"a judgment cannot borrow another source span");
    }
  }
}
assert(testedDirectProtocol, "no direct control reached the direct checker");
// A refusal the verifier makes while validating the source, before a graph
// exists, is shown as a located source refusal.
{
  const i = controls.findIndex((c) => c.file === "invalid-default-invocation");
  const settled = shownControls[i];
  assert(settled?.status === "fulfilled");
  const [refused] = settled.value.manifest.results ?? [];
  assert.equal(refused?.obligation?.kind, "source-refusal");
  assert.equal(refused?.location?.kind, "source-limitation");
  assert.match(refused?.detail ?? "", /pending closure cannot be invoked or exposed/);
  process.stdout.write("reader collection: a source refusal shown at its span\n");
}
process.stdout.write(
  `reader collection: ${cases.filter((c) => c.kind === "negative").length} negative controls refused at their expected boundaries\n`,
);

// What this producer does not implement is refused where it is refused, in the
// words that boundary uses: the reader shows the source under the pipeline's
// own outcome, and nothing claimed.
for (const [file, phase, says] of [
  ["module-function-assignment", "proposal", /^unsupported:/],
] as const) {
  const shown = await analyse(repositoryPath(file), "ocaml");
  const outcome = shown.outcome;
  assert(outcome && outcome.status === "unsupported");
  assert.equal(outcome.phase, phase);
  assert.match(outcome.detail, says);
  assert.deepEqual(shown.manifest.functions, []);
  process.stdout.write(`reader collection: ${file} refused by name\n`);
}
// A source TypeScript reports errors in is refused at the parser's gate. The
// reader shows that outcome, and TypeScript's own errors where it placed them,
// from the same run: the gate names only the declaration holding one.
{
  const file = "verification/ocaml-producer/evidence/service-binding/crashing-service-sound-binding.ts";
  const shown = await analyse(file, "ocaml");
  assert.equal(shown.outcome?.status, "unsupported");
  assert.equal(shown.outcome?.phase, "source");
  assert.match(shown.manifest.diagnostics ?? "",
    new RegExp(`^File "${file}", line 31, character 32-38:\nTypeScript: Property 'input2' does not exist`));
  process.stdout.write("reader collection: TypeScript's errors shown at their spans\n");
}
