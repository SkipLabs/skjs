#!/usr/bin/env node
import assert from "node:assert/strict";
import fs from "node:fs";
import { hash, render } from "../tools/annotate-source.mts";
import { createRequire } from "node:module";
import type { Bundle, FailureKind, Manifest } from "../report-viewer/types.ts";
import type { Span } from "../tools/span.mts";
import {
  fromBundle,
  parseReport,
  renderType,
} from "../report-viewer/model.mts";
import * as marks from "../report-viewer/marks.mts";
import type { ShownFunction, Site } from "../report-viewer/model.mts";
import surface from "../tools/claim-text.mts";
import { decodeGraph, parseGraph, printGraph, graphDefinitions, type Labels, type TypeGraph } from "../tools/type-graph.mts";
import type {
  EdgeCoverage,
  NodeTyping,
  ObligationDiagnostic,
  SourceMapEntry,
} from "../tools/diagnostic.mts";
import { decodeTerm, parseTerm, printTerm } from "../tools/calculus.mts";
import ob from "../tools/diagnostic-view.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";
import { atom, must, rows } from "./edits.mts";
import type { Atom, ClaimType } from "../tools/claim.mts";

import { groups, viewerGroups } from "../report-viewer/examples.mts";
import { cases as ocamlCases } from "../ocaml-producer/cases.mts";

// The corpus projection must retain the viewer's described entries, including
// examples that also appear in a producer-specific group.
for (const group of groups) {
  const shown = must(
    viewerGroups.find((g) => g.label === group.label),
    group.label,
  );
  assert.deepEqual(
    group.files,
    shown.files.map((file) => file.path),
  );
}
for (const group of viewerGroups) {
  for (const file of group.files) {
    assert.ok(file.about.trim(), `${file.path}: missing description`);
    assert.doesNotMatch(
      file.about,
      /[\r\n]/u,
      `${file.path}: multiline description`,
    );
    const c = ocamlCases.find(
      (c) => file.path === `verification/ocaml-producer/examples/${c.file}.ts`,
    );
    if (c)
      assert.equal(
        file.about,
        c.area,
        `${file.path}: inventory description drift`,
      );
  }
}

/** One end of an obligation, as the record names it. */
const sourceMapAt = (
  pos: Span,
  role: string,
  environmentStart: number | null = null,
): SourceMapEntry => ({ pos, role, environmentStart, context: [] });
/** The one field of a record claim the surface tests write. */
const fieldOf = (type: ClaimType) =>
  must(atom(type.atoms[0], "record").fields[0], "the field");
// Plain JavaScript modules; the reader loads these in a browser too.
const require = createRequire(import.meta.url);
const source =
  "// 😀\nfunction f(x: boolean): boolean {\n  return (\n    x\n  );\n}\n";
const start = source.indexOf("function"),
  expr = source.indexOf("(\n"),
  end = source.indexOf(");") + 1;
const claimPos: Span = [expr, end];
const namePos: Span = [source.indexOf("f("), source.indexOf("f(") + 1];
const declaration: Span = [start, source.length - 1];
const entryPos: Span = [start, end];
const claim = {
  pos: claimPos,
  type: '{"reference":{"to":7}}',
  raw: { reference: { to: 7 } },
};
// Typed as the manifest itself, so a fixture that stops being a valid report
// is an error here rather than a puzzling reader failure. The reader's own
// view of the format is report-viewer/types.ts.
const manifest: Manifest = {
  producer: "manual",
  source: { file: "f.ts", sha256: hash(source) },
  functions: [
    {
      id: "f0",
      name: "f",
      namePos: namePos,
      pos: declaration,
      entries: [],
      expressions: [{ id: "f0x0", ...claim }],
    },
  ],
  diagnostics: "Producer stopped at this expression",
  gaps: [],
  results: null,
};
const bundle = { source, manifest };
/** The sites of one kind, in source order. */
/** The failure a function records, and the site it attached to: a check that
 * reads one is about a report that has one. */
const failureOf = (f: ShownFunction) => must(f.failure, "a recorded failure");
const at = (failure: { at: number | null }) =>
  must(failure.at, "the site the failure attached to");
const of = <K extends Site["kind"]>(f: ShownFunction, kind: K) =>
  f.sites.filter((s): s is Extract<Site, { kind: K }> => s.kind === kind);
const report = fromBundle(bundle);
assert.equal(of(report.functions[0], "expression")[0].type, claim.type);
assert.deepEqual(
  JSON.parse(must(of(report.functions[0], "expression")[0]?.raw, "the claim's encoding")),
  claim.raw,
);
assert.equal(
  report.source.slice(...of(report.functions[0], "expression")[0].pos),
  "(\n    x\n  )",
);
assert.equal(report.diagnostics, manifest.diagnostics);
assert.equal(report.functions[0].status, "not-run");
assert.equal(renderType('{"newConstructor":7}').text, '{"newConstructor":7}');
const bad = structuredClone(bundle);
bad.manifest.functions[0].expressions[0].pos = [1, source.length + 1];
assert.throws(() => fromBundle(bad), /span/);
const changed = structuredClone(bundle);
changed.manifest.comparison = {
  baselineProducer: "manual",
  changes: [
    { span: [expr, end], status: "changed", kind: "expression", function: "f" },
  ],
};
assert.match(
  of(fromBundle(changed).functions[0], "unclaimed")[0].detail,
  /claim edit: changed/,
);
const missing = structuredClone(bundle);
missing.manifest.functions = [];
missing.manifest.gaps = [
  { id: "g0", pos: [start, source.length - 1], status: "claims unavailable" },
];
assert.equal(of(fromBundle(missing).functions[0], "unclaimed").length, 1);
const missingFunctionBundle = structuredClone(missing);
missingFunctionBundle.manifest.missingFunctions = [
  {
    name: "f",
    namePos: manifest.functions[0].namePos,
    pos: [start, source.length - 1],
    parameters: ["x"],
    missingSites: [{ kind: "expression", pos: claim.pos }],
  },
];
assert.equal(
  fromBundle(missingFunctionBundle).functions[0].candidateMissing,
  true,
);
const invalidMissing = structuredClone(missingFunctionBundle);
const invalidFunction = must(
  must(invalidMissing.manifest.missingFunctions, "the missing functions")[0],
  "a missing function",
);
must(invalidFunction.missingSites[0], "a missing site").pos = [0, 1];
assert.throws(() => fromBundle(invalidMissing), /outside function/);
invalidFunction.namePos = [0, 1];
assert.throws(() => fromBundle(invalidMissing), /identity/);
const annotated = render(source, manifest);
assert.equal(parseReport(annotated).source, source);
assert.equal(of(parseReport(annotated).functions[0], "expression")[0].type, claim.type);
// Realistic comment-format input, built here rather than stored: a rejected
// snapshot with a recovery label, an unvisited statement and an undecodable
// binding. Reading it back must recover the exact source, including non-ASCII.
{
  const text =
    "// 🌍\nfunction partial(): boolean {\n  const x: boolean = true;\n  return x;\n}\n";
  const nameAt = text.indexOf("partial"),
    first = text.indexOf("const");
  const report = {
    producer: "skjs",
    source: { file: "partial.ts", sha256: hash(text) },
    functions: [
      {
        name: "partial",
        namePos: [nameAt, nameAt + 7],
        collection: {
          completion: "aborted",
          quality: "recovery",
          mode: "keep-going",
          visitedExpressions: [],
        },
        entries: [
          {
            pos: [first, text.indexOf(";", first) + 1],
            bindings: [
              {
                name: "this",
                type: "(unavailable)",
                raw: { unsupported: true },
              },
            ],
          },
        ],
        expressions: [
          {
            pos: [text.indexOf("true"), text.indexOf("true") + 4],
            type: "true",
          },
        ],
      },
    ],
  };
  const parsed = parseReport(render(text, report));
  assert.equal(parsed.source, text);
  assert.equal(hash(parsed.source), parsed.meta["source-sha256"]);
  assert.equal(parsed.file, "partial.ts");
  const partialFn = parsed.functions[0];
  assert.equal(partialFn.name, "partial");
  assert.equal(partialFn.quality, "recovery");
  assert.equal(partialFn.collection, "aborted");
  assert.equal(of(partialFn, "expression")[0].recovery, true);
  assert.equal(of(partialFn, "environment")[0].bindings[0].unavailable, true);
  const unvisited = of(partialFn, "unclaimed").find(
    (g) => g.reason === "statement-not-visited",
  );
  assert(unvisited);
  assert.equal(text.slice(...unvisited.pos), "return x;");
  assert.equal(partialFn.id, "f0");
}

// A site is addressed by its index in source order; an environment comes
// before the claims of its statement, so stepping visits it first.
{
  const shifted = structuredClone(bundle);
  shifted.manifest.functions[0].expressions.unshift({
    id: "f0x9",
    pos: [source.indexOf("x\n"), source.indexOf("x\n") + 1],
    type: "boolean",
  });
  shifted.manifest.functions[0].entries = [{ id: "f0e0", pos: [start, end], bindings: [] }];
  const sites = fromBundle(shifted).functions[0].sites;
  assert.deepEqual(
    sites.map((s) => [s.kind, s.pos[0]]),
    [["environment", start], ["expression", claim.pos[0]], ["expression", source.indexOf("x\n")]],
  );
}

/* ---------- what the source view decides, without a browser ---------- */


// SKJS positions are 1-based with an exclusive end; a diagnostic for another
// file, or past the end of its line, must not be drawn over this source.
{
  const text = "function f(): boolean {\n  return !flag;\n}\n";
  const rep = {
    source: text,
    file: "f.ts",
    diagnostics:
      'File "/work/f.ts", line 2, character 10-15:\nerror: nope\n' +
      'File "/work/other.ts", line 1, character 1-2:\nerror: elsewhere\n' +
      'File "/work/f.ts", line 2, character 10-999:\nnote: past the line\n',
  };
  const found = marks.producerMarks(rep);
  assert.equal(found.length, 2);
  assert.equal(text.slice(...found[0].pos), "!flag");
  assert.equal(found[0].text, "error: nope");
  assert.equal(text.slice(...found[1].pos), "!flag;");
  assert.equal(marks.producerMarks({ source: text, file: "f.ts" }).length, 0);
}

// Both outcomes, and whether they disagree.
{
  // The run this report came from, where one ran: a verified function is
  // stamped as freshly checked only then.
  const fresh = { verified: true };
  const fromFile = null;
  const outcome = (f: marks.Judged, run: { verified: boolean } | null = fresh) =>
    marks.outcome(f, run);
  const verified: marks.Judged = { status: "verified", collection: "complete" };
  assert.deepEqual(
    [outcome(verified).producer[0], outcome(verified).proof[0]],
    ["✓", "✓"],
  );
  assert.equal(outcome(verified).stamp, "fresh");
  assert.equal(outcome(verified, fromFile).stamp, "recorded");
  assert.equal(outcome(verified).disagrees, false);
  const unsound = { status: "not-established", collection: "complete" };
  assert.equal(outcome(unsound).proof[0], "✗");
  assert(outcome(unsound).disagrees && outcome(unsound).attention);
  const beyond = { status: "verified", collection: "aborted" };
  assert(outcome(beyond).disagrees);
  assert.equal(outcome(beyond).attention, false);
  const agreed = { status: "not-established", collection: "aborted" };
  assert.equal(outcome(agreed).disagrees, false);
  // Nothing was concluded: no symbol claiming a verdict, and no disagreement.
  const incomplete: marks.Judged = {
    status: "not-established",
    collection: "complete",
    failure: {
      kind: "missing-expression-claim",
      detail: "",
      role: "",
      binding: "",
      at: null,
      pos: null,
    },
  };
  assert.equal(outcome(incomplete).proof[0], "?");
  assert.equal(outcome(incomplete).disagrees, false);
  assert.equal(outcome(incomplete).attention, false);
  assert.equal(marks.proofLabel("not-established"), "proof search failed");
  assert.equal(marks.proofSymbol("source-limitation"), "?");
  assert.equal(marks.proofSymbol("expression-obligation"), "✗");
}

// The marks drawn for one function: what each density shows, and the symbol a
// claim carries where checking stopped.
{
  const text =
    "// note\nfunction f(x: boolean): boolean {\n  const y: boolean = x;\n  const t: true = true;\n  return y;\n}\n";
  const at = (s: string): Span => [text.indexOf(s), text.indexOf(s) + s.length];
  const literal: Span = [text.lastIndexOf("true"), text.lastIndexOf("true") + 4];
  const rep = { source: text, file: "f.ts" };
  const fn: ShownFunction = {
    id: "f0",
    name: "f",
    status: "not-established",
    collection: "complete",
    quality: "unverified",
    pos: [text.indexOf("function"), text.length - 1],
    sites: [
      {
        kind: "environment",
        pos: at("const y: boolean = x;"),
        bindings: [
          { name: "x", type: "boolean", unavailable: false },
          { name: "this", type: "(unavailable)", unavailable: true },
        ],
        changed: new Set(["x"]),
        recovery: false,
      },
      { kind: "expression", pos: at("x;"), type: "boolean", raw: null, recovery: false },
      { kind: "expression", pos: at("y;"), type: "boolean", raw: null, recovery: false },
      // a literal restating itself: hidden in Compact, shown in Every claim
      { kind: "expression", pos: literal, type: "true", raw: null, recovery: false },
    ],
    failure: { detail: "no", kind: "expression-obligation", role: "", binding: "", at: 2, pos: at("y;") },
  };
  const compact = marks.sourceMarks(rep, fn, { density: "key" });
  assert.deepEqual(
    compact.items.map((i) => [i.site, i.label, i.mark]),
    [
      [1, "boolean", ""],
      [2, "boolean", "✗"],
    ],
  );
  assert.equal(compact.entries[0].label, "x: boolean");
  const all = marks.sourceMarks(rep, fn, { density: "all", unsupported: true });
  assert.equal(all.entries[0].label, "x: boolean,  this: (unavailable)");
  assert.deepEqual(
    all.items.map((i) => i.site),
    [1, 2, 3],
  );
}

// A gap reads like the other marks: its own words, plus the proof symbol where
// verification stopped there.
{
  const text = "function f(): boolean {\n  return true;\n}\n";
  const rep = { source: text, file: "f.ts" };
  const site: Span = [text.indexOf("return"), text.indexOf("true;") + 5];
  const fn: ShownFunction = {
    id: "f0",
    name: "f",
    status: "not-established",
    collection: "aborted",
    pos: [0, text.length],
    sites: [
      { kind: "unclaimed", pos: site, reason: "statement-not-visited", detail: "statement not visited" },
    ],
    failure: { detail: "needed a claim", kind: "missing-environment-claim", role: "", binding: "", at: 0, pos: site },
  };
  const [gap] = marks.sourceMarks(rep, fn, { density: "key" }).items;
  assert.equal(gap.label, "not visited by producer");
  assert.equal(gap.mark, "?");
  assert.equal(gap.cls, "gap failed");
}

// A comment written above a function belongs to it; a neighbour's does not.
{
  const text = "function a() {}\n\n// about b\n// still b\nfunction b() {}\n";
  const starts = marks.lineStarts(text);
  const b = text.indexOf("function b");
  assert.equal(marks.commentStartLine(text, starts, b, 0), 2);
  assert.equal(
    marks.commentStartLine(text, starts, b, text.indexOf("// still b")),
    3,
  );
  assert.equal(marks.commentStartLine(text, starts, 0, 0), 0);
}

// Packing must count the proof symbol, or the next mark would overlap it.
{
  const row = marks.packRows([
    { col: 0, end: 4, label: "boolean", mark: "✗" },
    { col: 12, end: 16, label: "true", mark: "" },
  ]);
  assert.equal(row.length, 2);
  assert.equal(marks.markWidth({ col: 0, end: 4, label: "boolean", mark: "✗" }), 4 + 1 + 7 + 2);
  assert.equal(marks.bracket(1), "╵");
  assert.equal(marks.bracket(5), "╰───╯");
}

// A required type the producer never exported: extraction stops before any
// obligation, so it is not a failed search and not a disagreement.
{
  const unavailable = structuredClone(bundle);
  unavailable.manifest.functions[0].entries = [
    { id: "f0e0", pos: [start, end], bindings: [{ name: "cell", type: "(unavailable)", raw: { unsupported: true } }] },
  ];
  unavailable.manifest.results = [
    {
      function: "f0",
      status: "not-established",
      detail: "reject: source environment obligation at 3: unavailable claimed binding 'cell'",
      stage: "source-extraction",
      location: { kind: "unavailable-type-claim", start, binding: "cell" },
    },
  ];
  const f = fromBundle(unavailable).functions[0];
  assert.equal(failureOf(f).kind, "unavailable-type-claim");
  assert.equal(failureOf(f).binding, "cell");
  assert.equal(f.sites[at(failureOf(f))].kind, "environment");
  assert.equal(marks.proofMark(f)[0], "?");
  assert.equal(marks.outcomeGroup(f).label, "could not be checked");
  assert.equal(marks.outcome(f, null).disagrees, false);
  assert.equal(marks.outcome(f, null).attention, false);
  assert.equal(marks.roleTag("unavailable-type-claim"), "type unavailable");
  // The same kind can name an expression instead of a statement entry.
  const atExpression = structuredClone(unavailable);
  must(atExpression.manifest.results, 'results')[0].location = {
    kind: "unavailable-type-claim",
    pos: claim.pos,
  };
  {
    const f = fromBundle(atExpression).functions[0];
    assert.equal(failureOf(f).kind, "unavailable-type-claim");
    assert.equal(f.sites[at(failureOf(f))].kind, "expression");
  }
  // Verified functions and failed searches keep their own groups.
  assert.equal(
    marks.outcomeGroup({ status: "verified", collection: "complete" }).label,
    "verified",
  );
  assert.equal(
    marks.outcomeGroup({ status: "not-established", collection: "complete" }).label,
    "proof search failed",
  );
}

/* ---------- claim types in surface syntax ---------- */


{
  const cell = (read: ClaimType, write: ClaimType): ClaimType => ({
    top: false,
    atoms: [
      {
        a: "record",
        fields: [{ name: "value", optional: false, read, write }],
        indexes: { string: "synthetic", number: "absent", symbol: "synthetic" },
        call: "absent",
        construct: "absent",
        array: "absent",
      },
    ],
  });
  const of = (...atoms: Atom[]): ClaimType => ({ top: false, atoms });
  const boolean = of({ a: "boolean" });
  const trueLit = of({ a: "booleanlit", v: "true" });
  const shapes = [
    boolean,
    of({ a: "null" }),
    of({ a: "null" }, { a: "boolean" }),
    trueLit,
    of({ a: "stringlit", v: 'a "quoted" value' }),
    of({ a: "numberlit", v: "3" }),
    { top: true, atoms: [] },
    { top: false, atoms: [] },
    cell(boolean, boolean),
    cell(trueLit, boolean),
    of({
      a: "function",
      this: { top: true, atoms: [] },
      params: [boolean],
      result: of({ a: "null" }),
      construct: "unknown",
      array: "unknown",
    }),
  ];
  const printed = shapes.map((t) => surface.printType(t).text);
  assert.deepEqual(printed, [
    "boolean",
    "null",
    "null | boolean",
    "true",
    '"a \\"quoted\\" value"',
    "3",
    "unknown",
    "never",
    '{ value: boolean } @{"call":"absent","construct":"absent","array":"absent","indexes":{"string":"synthetic","number":"absent","symbol":"synthetic"}}',
    '{ value: boolean = (true) } @{"call":"absent","construct":"absent","array":"absent","indexes":{"string":"synthetic","number":"absent","symbol":"synthetic"}}',
    "(boolean) => null",
  ]);
  // Printed types read back without a template, including their object modes.
  for (const [i, type] of shapes.entries())
    assert(surface.roundTrips(type), "round trip: " + printed[i]);

  // A current-content assertion is written against the storage invariant, and
  // reads back as the read/write pair the producer encodes it with. Parentheses
  // are the documented form; a bare union is accepted too.
  {
    const plain = cell(boolean, boolean);
    const observed = surface.parseType("{ value: boolean = (true) }");
    const value = must(atom(observed.atoms[0], "record").fields[0], "the field");
    assert.deepEqual(value.read, trueLit);
    assert.deepEqual(value.write, boolean);
    assert.equal(surface.printType(observed).text, "{ value: boolean = (true) }");
    assert.deepEqual(
      surface.parseType("{ value: boolean = true }"),
      observed,
    );
    // Dropping the assertion says both at once again.
    assert.deepEqual(fieldOf(surface.parseType("{ value: boolean }")).read, boolean);
  }

  // Bare text states default modes; printed nondefault modes are explicit.
  const original = cell(trueLit, boolean);
  const edited = surface.parseType("{ value: boolean }");
  assert.deepEqual(atom(edited.atoms[0], "record").indexes, {string:"absent",number:"absent",symbol:"absent"});
  assert.deepEqual(surface.parseType(surface.printType(original).text), original);
  assert.deepEqual(fieldOf(edited).read, fieldOf(edited).write);
  assert.equal(surface.printType(edited).text, "{ value: boolean }");
  assert.deepEqual(surface.parseType("true | null"), {
    top: false,
    atoms: [{ a: "booleanlit", v: "true" }, { a: "null" }],
  });

  // Missing objects and free signatures use the same self-contained language.
  assert.equal(surface.parseType("{ value: boolean }").atoms[0].a, "record");
  const freshArrow = surface.readClaimValue("expression", "(boolean) => null", undefined);
  assert.deepEqual(freshArrow, of({a: "function", construct: "unknown", array: "unknown",
    this: {top: true, atoms: []}, params: [boolean], result: of({a: "null"})}));
  assert.deepEqual(surface.parseType("(boolean) => null"), freshArrow);
  assert.deepEqual(surface.readClaimValue("expression", "(boolean) => null", {unsupported: true}), freshArrow);
  const factory = surface.parseType("() => (boolean) => null");
  assert.deepEqual(atom(factory.atoms[0], "function").result, freshArrow);
  assert(surface.roundTrips(factory));
  const restricted = structuredClone(freshArrow);
  // `Atom` is a union and only some of its members carry object modes, so the
  // suite says which atom the text it just wrote produced.
  const signature = restricted.atoms[0];
  assert(signature.a === "function", "the text names a free signature");
  signature.construct = "absent";
  signature.array = "absent";
  const changedArrow = atom(
    surface.parseType("(null, boolean) => boolean").atoms[0],
    "function",
  );
  assert.equal(changedArrow.construct, "unknown");
  assert.equal(changedArrow.array, "unknown");
  assert.deepEqual(surface.parseType(surface.printType(restricted).text), restricted);
  assert.throws(() => surface.parseType("boolean &"), /unexpected/);
  assert.throws(() => surface.parseType("{ value boolean }"), /expected :/);
  assert.equal(fieldOf(surface.parseType("{ nope: boolean }")).name,"nope");
  // Dropping a field is expressible, so it is allowed.
  assert.deepEqual(atom(surface.parseType("{ }").atoms[0], "record").fields, []);
  assert.throws(() => surface.parseType("boolean boolean"), /after the type/);

  // An encoding this reader cannot name is summarized, and then not editable.
  // Not built with `of`: the point is that this is not one of the language's
  // atoms, and the reader must say so rather than name it.
  const exotic = { top: false, atoms: [{ a: "tuple", parts: [] }] };
  assert.equal(surface.printType(exotic).printable, false);
  assert.equal(surface.printType(exotic).text, "«tuple»");
  assert.equal(surface.roundTrips(exotic), false);
  assert.equal(surface.printType({ unsupported: true }).text, "(unavailable)");
  assert.equal(surface.roundTrips({ unsupported: true }), false);
}

// A whole claim: one expression's type, or a statement environment. A binding
// the producer could not decode rides along rather than pushing the environment
// back into JSON, and cannot be given a type here.
{
  const boolean = { top: false, atoms: [{ a: "boolean" }] };
  const union = { top: false, atoms: [{ a: "boolean" }, { a: "null" }] };
  const cell = {
    top: false,
    atoms: [
      {
        a: "record",
        fields: [{ name: "value", optional: false, read: boolean, write: boolean }],
        indexes: { string: "absent", number: "absent", symbol: "absent" },
        call: "unknown",
        construct: "unknown",
        array: "unknown",
      },
    ],
  };
  const env = [
    { name: "this", type: { unsupported: true } },
    { name: "value", type: union },
    { name: "cell", type: cell },
  ];
  const text = surface.printClaimValue("environment", env);
  assert.equal(
    text,
    "this: (unavailable), value: boolean | null, cell: { value: boolean }",
  );
  assert.deepEqual(surface.readClaimValue("environment", text, env), env);
  assert.equal(surface.printClaimValue("expression", union), "boolean | null");
  assert.deepEqual(
    surface.readClaimValue("expression", "true", union),
    { top: false, atoms: [{ a: "booleanlit", v: "true" }] },
  );
  // An undecoded claim has nothing to edit against, and is not invented here.
  assert.equal(surface.printClaimValue("expression", { unsupported: true }), "(unavailable)");
  assert.deepEqual(surface.readClaimValue("environment", "this: boolean, value: null, cell: { value: boolean }", env)[0].type, boolean);
  // An expression claim that was never decoded can still be given a type that
  // needs no original to edit against.
  assert.deepEqual(
    surface.readClaimValue("expression", "null", { unsupported: true }),
    { top: false, atoms: [{ a: "null" }] },
  );
  assert.equal(surface.readClaimValue("expression", "{ value: boolean }", { unsupported: true }).atoms[0].a, "record");
  // The binding set is the original's: none added, none dropped, none doubled.
  for (const [bad, complaint] of rows<[string, RegExp]>([
    ["value: null", /binding 'this' is missing/],
    ["this: (unavailable), value: null, cell: { value: boolean }, extra: null", /not a binding/],
    ["this: (unavailable), value: null, value: null, cell: { value: boolean }", /appears twice/],
    ["this: (unavailable), value, cell: { value: boolean }", /needs a name and a type/],
  ]))
    assert.throws(() => surface.readClaimValue("environment", bad, env), complaint);
}

/* ---------- obligation diagnostics, as the panel reads them ---------- */


// Types are label lists into the record's own table, read as a union. The graph
// is finite but may be cyclic, so rendering stops rather than recursing.
{
  const types = [
    ["nul"],
    [{ boolLit: { value: true } }],
    [{ boolLit: { value: false } }],
    [{ refs: { first: [["value", [1, 2]]], rest: [], views: [] } }],
    [{ arrs: { arrows: [[[8], [[[0]], [1, 2]]]] } }],
    [{ mystery: 7 }],
    [{ refs: { first: [["value", [6]]], rest: [], views: [] } }],
  ];
  types.push([{ refs: { first: [["value", [7]]], rest: [], views: [] } }]);
  // Row 8 is the unknown receiver of row 4's signature.
  types.push(["top"]);
  // The table's rows 1 and 2 are the literals a source `boolean` lowers to, and
  // a reference row is printed as the record the source declared.
  assert.equal(ob.typeText(types, [1, 2]), "boolean");
  assert.equal(ob.typeText(types, [1]), "true");
  assert.equal(ob.typeText(types, [0, 1, 2]), "null | boolean");
  assert.equal(ob.typeText(types, []), "never");
  assert.equal(ob.typeText(types, [0]), "null");
  assert.equal(ob.typeText(types, [3]), "{ value: boolean }");
  assert.equal(ob.typeText(types, [4]), "(null) => boolean");
  // A normalized claim is lifted into the structural encoding to be edited,
  // with the current-content assertion as the cell's read side, and lowered
  // back, interning the rows the edit needs into the document's own table.
  const lifted = surface.lift(types, [3], [["value",[1]]]);
  assert.equal(surface.printType(lifted).text, "{ value: boolean = (true) }");
  assert.equal(surface.lift(types, [1], [["value",[1]]]), null);
  const table = structuredClone(types);
  assert.deepEqual(
    surface.lower(table, surface.parseType("{ value: boolean = (true) }")),
    { type: [3], current: [["value", [1]]] },
  );
  assert.deepEqual(surface.lower(table, surface.parseType("{ value: true }")), {
    type: [types.length],
    current: null,
  });
  assert.deepEqual(table[types.length], [{ refs: { first: [["value", [1]]], rest: [], views: [] } }]);
  assert.deepEqual(surface.lower(table, surface.parseType("null | boolean")), {
    type: [0, 1, 2],
    current: null,
  });
  assert.deepEqual(surface.lower(table, [0, 3]), { type: [0, 3] });
  // `unknown` reuses the table's own top row, the receiver of row 4.
  assert.deepEqual(surface.lower(table, surface.parseType("unknown")),{type:[8],current:null});
  assert.equal(table.length, types.length + 1);
  assert.equal(ob.typeText(types, [5]), JSON.stringify({ mystery: 7 }));
  assert.equal(ob.typeText(types, [99]), "type 99");
  assert.match(ob.typeText(types, [6], 2), /…/);
  assert.equal(ob.typeText(types, "nonsense"), "(no type recorded)");
  assert.equal(ob.termText({ var: { i: 2 } }), "slot 2");
  assert.equal(ob.termText("nul"), "nul");
}

const recorded = (d: ObligationDiagnostic) =>
  "obligation-diagnostic: " + JSON.stringify(d);

// A return contract: the claim can be sound and still not establish the result.
{
  const types: TypeGraph = [["nul"], [{ boolLit: { value: true } }], [{ boolLit: { value: false } }]];
  const sourceMap: SourceMapEntry =
    { pos: [370, 374], role: "return-contract", environmentStart: 363, context: [] };
  // Written as the record the decoder admits, so that a field it requires
  // cannot quietly go missing from what the reader is tested on.
  const record: NodeTyping = {
    kind: "node-typing",
    phase: "proof-search",
    outcome: "not-established",
    fuel: 10,
    id: "node:1",
    types,
    requiredResult: [1],
    sequent: { context: [[1, 2], [1, 2]], term: { var: { i: 0 } }, type: [1] },
    source: {
      label: 1,
      node: { continuation: "ret", expression: { var: { i: 0 } } },
      claim: { context: [[1, 2], [1, 2]], type: [1] },
      sourceMap,
      requiredKnowledge: null,
    },
  };
  // The fixture is a record the decoder admits, not a shape invented here: what
  // the reader is typed against and what arrives are the same thing.
  assert(readDiagnostic(recorded(record)), "the decoder refused this fixture");
  const view = ob.obligationView(record);
  assert.equal(view.title, "Return contract");
  assert.equal(view.role, "return-contract");
  assert.equal(view.conclusion, "true");
  assert.equal(view.requiredResult, "true");
  assert.equal(view.term, "slot 0");
  assert.deepEqual(
    view.rows.map((r) => [r.slot, r.have, r.note]),
    [
      [0, "boolean", "the value being returned"],
      [1, "boolean", ""],
    ],
  );
  assert.equal(view.environmentStart, 363);
  const inRole = (role: string): NodeTyping =>
    ({ ...record, source: { ...record.source, sourceMap: { ...sourceMap, role } } });
  // An unknown role stays generic rather than being guessed into a story.
  const odd = ob.obligationView(inRole("future-role"));
  assert.equal(odd.title, "Obligation at this point");
  assert.match(odd.what, /not one this reader knows/);
  // Only a return contract names slot 0 as the returned value.
  assert.equal(ob.obligationView(inRole("expression-claim")).rows[0].note, "");
}

// An edge: the destination map acts on the available context, and the slots
// that differ are the ones to look at. The observation is the edge's premise.
{
  const types: TypeGraph = [["nul"], [{ boolLit: { value: true } }], [{ boolLit: { value: false } }]];
  const at = (pos: Span, role: string, environmentStart: number | null = null): SourceMapEntry =>
    ({ pos, role, environmentStart, context: [] });
  const required: Labels[] = [[1], [0]];
  const record: EdgeCoverage = {
    kind: "edge-coverage",
    phase: "proof-search",
    outcome: "not-established",
    fuel: 10,
    id: "edge:8:1",
    types,
    edgeIndex: 1,
    source: { label: 8, sourceMap: at([10, 14], "expression-claim"),
      node: null, claim: null, requiredKnowledge: null },
    destination: {
      label: 7,
      claim: { context: required, type: [1] },
      sourceMap: at([20, 24], "node-typing"),
      node: null,
      requiredKnowledge: null,
    },
    transfer: {
      available: [[0], [1, 2], [1]],
      target: { label: 7, mapping: [2, 0] },
      booleanObservation: true,
      tagObservation: null,
    },
  };
  assert(readDiagnostic(recorded(record)), "the decoder refused this fixture");
  const view = ob.obligationView(record);
  assert.equal(view.kindLabel, "edge coverage");
  assert.deepEqual(
    view.rows.map((r) => [r.slot, r.have, r.need, r.differs]),
    [
      [0, "true", "true", false],
      [1, "null", "null", false],
    ],
  );
  assert.match(must(view.observation, 'the reader\'s own words'), /slot 0 is true/);
  assert.match(must(view.observation, 'the reader\'s own words'), /not a claim that execution took it/);
  assert.match(must(view.note, 'the reader\'s own words'), /edge 1/);
  assert.deepEqual(
    view.endpoints.map((e) => [e.end, e.sourceMap?.pos]),
    [
      ["from", [10, 14]],
      ["to", [20, 24]],
    ],
  );
  // An edge into a statement checkpoint has no expression claim at its span: it
  // is described by what its destination required, and attaches to that entry.
  const checkpoint = structuredClone(record);
  checkpoint.source.sourceMap = at([1, 5], "binding-annotation");
  checkpoint.destination.sourceMap = at([10, 20], "heap-observation", 10);
  const checkpointView = ob.obligationView(checkpoint);
  assert.equal(checkpointView.title, "Current-content assertion");
  assert.equal(checkpointView.environmentStart, 10);
  assert.deepEqual(
    checkpointView.endpoints.map((e) => e.sourceMap?.pos),
    [
      [1, 5],
      [10, 20],
    ],
  );
  // Two ends can agree on every contract and still differ on what the heap
  // holds. Without the required facts the table looks unanimous, so they are
  // shown, and named as the remaining difference only when they are one.
  assert.deepEqual(checkpointView.knowledge, []);
  const observed = structuredClone(checkpoint);
  observed.transfer.available = required;
  observed.transfer.target.mapping = null;
  observed.destination.requiredKnowledge = {
    cells: [{ slot: 1, contents: ["tru"], field: "value" }],
    values: [{ slot: 0, contents: ["nul", "fls"], field: "value" }],
    links: [{ cell: 1, value: 0, alias: false, field: "value" , distinct: false, other: "value" }],
  };
  const observedView = ob.obligationView(observed);
  assert.equal(
    observedView.rows.every((r) => !r.differs),
    true,
  );
  assert.deepEqual(
    observedView.knowledge.map((r) => [r.binding, r.what]),
    [
      ["slot 1", ".value holds true"],
      ["slot 0", "is null | false"],
      ["slot 0", "is a read of slot 1.value"],
    ],
  );
  assert.equal(observedView.knowledgeIsTheDifference, true);
  assert.match(must(observedView.note, 'the reader\'s own words'), /Every binding's contract already agrees/);
  // A differing contract is still reported as the difference it is.
  const both = structuredClone(observed);
  both.transfer.available = [[2], [0]];
  const bothView = ob.obligationView(both);
  assert.equal(bothView.knowledgeIsTheDifference, false);
  assert.match(must(bothView.note, 'the reader\'s own words'), /slot 0 is where/);
  assert.equal(bothView.knowledge.length, 3);
  // An alias link reads as an equality between slots, not as a heap read.
  assert.equal(
    ob.knowledgeRows({ links: [{ cell: 3, value: 2, alias: true, field: "value" , distinct: false, other: "value" }] })[0].what,
    "is the same value as slot 3",
  );
  // With a source map the same fact reads in the words of the source.
  assert.deepEqual(
    ob
      .knowledgeRows({ cells: [{ slot: 1, contents: ["tru"], field: "value" }] }, ["r", "cell"])
      .map((x) => [x.binding, x.what]),
    [["cell", ".value holds true"]],
  );
  // A descriptor is a name, or the expression whose value the binding holds.
  assert.equal(ob.bindingText({ name: "cell" }, "x"), "cell");
  assert.equal(
    ob.bindingText({ name: "", span: [4, 9] }, "let cell = 1;"),
    "cell",
  );
  assert.deepEqual(
    ob.bindingsOf({ context: [{ name: "seed" }, { name: "", span: [0, 3] }] }, "abc def"),
    ["seed", "abc"],
  );
  assert.equal(ob.contentsText([]), "never");
  const numeric = structuredClone(observed);
  numeric.destination.requiredKnowledge = {
    cells: [{ slot: 1, field: "total", contents: ["num", "nul"] }],
    values: [{ slot: 0, field: "value", contents: [{numLit: {bits:"9223372036854775808"}}] }],
    links: [],
  };
  assert(readDiagnostic(recorded(numeric)), "numeric heap predicates decode");
  assert.deepEqual(ob.obligationView(numeric).knowledge.map(r => r.what), [".total holds number | null", "is -0"]);
  numeric.destination.requiredKnowledge.values[0].contents = [{numLit: {bits:"18446744073709551616"}}];
  assert.equal(readDiagnostic(recorded(numeric)), undefined, "numeric heap bits are checked");


  // Tag dispatch observes the same slot, and reads the same way.
  const tagged = structuredClone(record);
  tagged.transfer.booleanObservation = null;
  tagged.transfer.tagObservation = { test: "isNul", answer: false, slot: 0 };
  tagged.source.sourceMap = at([10, 14], "tag-dispatch");
  const tagView = ob.obligationView(tagged);
  assert.equal(tagView.title, "Tag dispatch");
  assert.match(must(tagView.observation, 'the reader\'s own words'), /tag test isNul answers false on slot 0/);
  assert.match(must(tagView.observation, 'the reader\'s own words'), /not a claim that execution took it/);
  tagged.transfer.tagObservation = { test: { numEq: { bits: "0" } }, answer: true, slot: 0 };
  assert.match(must(ob.obligationView(tagged).observation, "numeric tag observation"), /numEq.*0/);
  // An identity map selects the available context unchanged.
  assert.deepEqual(ob.mapContext([[1], [2]], null), [[1], [2]]);
  const mismatched = structuredClone(record);
  mismatched.transfer.target.mapping = [0, 1];
  assert.deepEqual(
    ob.obligationView(mismatched).rows.map((r) => r.differs),
    [true, true],
  );
}

// The mark says which obligation stopped there, and stays silent when the role
// is generic: a claim must not be labelled as the wrong one.
{
  const source = "function f(): true {\n  return flag;\n}\n";
  const rep = { source, file: "f.ts" };
  const pos: Span = [source.indexOf("flag"), source.indexOf("flag") + 4];
  const fn: ShownFunction = {
    id: "f0",
    name: "f",
    status: "not-established",
    collection: "aborted",
    pos: [0, source.length],
    sites: [
      { kind: "expression", pos, type: "boolean", raw: null, recovery: false },
    ],
    failure: { detail: "reject", kind: "expression-obligation", role: "return-contract", binding: "", at: 0, pos },
  };
  const [mark] = marks.sourceMarks(rep, fn, { density: "key" }).items;
  assert.equal(mark.label, "boolean");
  assert.equal(mark.mark, "✗");
  assert.equal(mark.tag, "return contract");
  assert.equal(marks.roleTag("node-typing"), "");
  assert.equal(marks.roleTag("expression-claim"), "");
  // Packing counts the tag, or the next mark would sit on top of it.
  assert.equal(
    marks.markWidth({ col: 0, end: 4, label: "boolean", mark: "✗", tag: "return contract" }),
    4 + 1 + 7 + 2 + 16,
  );
}

console.log(
  "Report viewer: structured payloads, UTF-16/multiline spans, gaps, comparison, addressing, source marks, surface types, obligations, and legacy comment reports passed",
);

const failureBundle = structuredClone(bundle);
failureBundle.manifest.results = [
  {
    function: "f0",
    status: "not-established",
    detail: "proof search stopped",
    location: { kind: "expression-obligation", pos: claim.pos },
  },
];
/** The failure's site, by kind, so a test says where it attached. */
const failedAt = (bundle: Bundle) => {
  const f = fromBundle(bundle).functions[0];
  return f.failure ? { ...f.failure, site: f.failure.at === null ? null : f.sites[f.failure.at].kind } : null;
};
assert.equal(must(failedAt(failureBundle), 'a located failure').detail, "proof search stopped");
assert.equal(must(failedAt(failureBundle), 'a located failure').site, "expression");
for (const kind of rows<FailureKind>(["edge-obligation", "source-limitation"])) {
  must(
    must(must(failureBundle.manifest.results, "results")[0], "a result").location,
    "a place",
  ).kind = kind;
  assert.equal(must(failedAt(failureBundle), 'a located failure').kind, kind);
  assert.equal(must(failedAt(failureBundle), 'a located failure').site, "expression");
}
failureBundle.manifest.functions[0].entries = [
  { id: "f0e0", pos: entryPos, bindings: [] },
];
must(failureBundle.manifest.results, 'results')[0].location = {
  kind: "environment-obligation",
  start,
};
assert.equal(must(failedAt(failureBundle), 'a located failure').kind, "environment-obligation");
assert.equal(must(failedAt(failureBundle), 'a located failure').site, "environment");
// An edge obligation names both of its claims: the expression at the mapped
// span, and the environment at the mapped statement entry.
// Only the two source maps are read here; the record a verifier writes states
// the rest, and this fixture is about where the reader attaches the ends.
must(failureBundle.manifest.results, "results")[0].obligation = {
  kind: "edge-coverage",
  phase: "proof-search",
  outcome: "not-established",
  fuel: 10,
  types: [],
  id: "edge:0:0",
  edgeIndex: 0,
  source: {
    label: 0,
    sourceMap: sourceMapAt(claim.pos, "binding-annotation"),
    node: null,
    claim: null,
    requiredKnowledge: null,
  },
  destination: {
    label: 1,
    sourceMap: sourceMapAt([start, start], "heap-observation", start),
    node: null,
    claim: null,
    requiredKnowledge: null,
  },
  transfer: {
    available: [],
    target: { label: 1, mapping: null },
    booleanObservation: null,
    tagObservation: null,
  },
};
{
  const f = fromBundle(failureBundle).functions[0];
  const kindAt = (i: number | null) => (i === null ? null : f.sites[i].kind);
  assert.deepEqual([kindAt(must(failureOf(f).edge, 'both ends').from), kindAt(must(failureOf(f).edge, 'both ends').to)], ["expression", "environment"]);
}
delete must(failureBundle.manifest.results, 'results')[0].obligation;
// The declared result is a site of its own, first in source order, and a
// failed return contract is an edge from the returned expression to it.
{
  const contract = structuredClone(bundle);
  const annotation = source.lastIndexOf("boolean");
  contract.manifest.functions[0].resultPos = [annotation, annotation + 7];
  contract.manifest.functions[0].signature = {
    params: [],
    retType: { top: false, atoms: [{ a: "booleanlit", v: "true" }] },
  };
  contract.manifest.results = [
    {
      function: "f0",
      status: "not-established",
      detail: "did not establish true",
      location: { kind: "expression-obligation", pos: claim.pos },
      obligation: {
        kind: "node-typing",
        phase: "proof-search",
        outcome: "not-established",
        fuel: 10,
        types: [],
        id: "node:0",
        source: {
          label: 0,
          sourceMap: sourceMapAt(claim.pos, "return-contract"),
          node: null,
          claim: null,
          requiredKnowledge: null,
        },
        sequent: { context: [], term: "nul", type: [] },
      },
    },
  ];
  const f = fromBundle(contract).functions[0];
  const first = f.sites[0];
  assert(first.kind === "result", "the declared result is drawn first");
  assert.deepEqual([first.kind, first.type], ["result", "true"]);
  assert.equal(f.sites[at(failureOf(f))].kind, "expression");
  assert.deepEqual(failureOf(f).edge, { from: at(failureOf(f)), to: 0 });
  const [drawn] = marks.sourceMarks({ source, file: "f.ts" }, f, { density: "key" }).items;
  assert.equal(drawn.label, "returns true");
  assert.equal(drawn.cls, "result");
}
delete must(failureBundle.manifest.results, 'results')[0].location;
assert.equal(failedAt(failureBundle), null);
must(failureBundle.manifest.results, 'results')[0].location = {
  kind: "expression-obligation",
  pos: claim.pos,
};
must(failureBundle.manifest.results, 'results')[0].status = "verified";
assert.equal(failedAt(failureBundle), null);

// A claim the verifier needed and did not find is reported at the gap that
// already marks that place, and is not presented as a disproved claim.
const absent = structuredClone(bundle);
absent.manifest.functions[0].expressions = [];
absent.manifest.gaps = [
  {
    id: "g0",
    pos: claim.pos,
    status: "expression entered without a type result",
  },
];
absent.manifest.results = [
  {
    function: "f0",
    status: "not-established",
    detail: "reject: no claimed type for the expression at [22,33)",
    location: { kind: "missing-expression-claim", pos: claim.pos },
  },
];
{
  const f = fromBundle(absent).functions[0];
  assert.equal(failureOf(f).kind, "missing-expression-claim");
  assert.match(failureOf(f).detail, /no claimed type/);
  assert.equal(f.sites[at(failureOf(f))].kind, "unclaimed");
  assert.equal(f.detail, must(absent.manifest.results, 'results')[0].detail);
  assert.equal(f.status, "not-established");
}
// Without a gap at that place — an older report — the claim there still carries it.
const absentNoGap = structuredClone(absent);
absentNoGap.manifest.gaps = [];
absentNoGap.manifest.functions[0].expressions = [{ id: "f0x0", ...claim }];
assert.equal(must(failedAt(absentNoGap), 'a located failure').kind, "missing-expression-claim");
assert.equal(must(failedAt(absentNoGap), 'a located failure').site, "expression");
const absentEnv = structuredClone(absent);
absentEnv.manifest.gaps = [
  { id: "g0", pos: [start, end], status: "statement not visited" },
];
must(absentEnv.manifest.results, 'results')[0].location = {
  kind: "missing-environment-claim",
  start,
  binding: "x",
};
assert.equal(must(failedAt(absentEnv), 'a located failure').kind, "missing-environment-claim");
assert.equal(must(failedAt(absentEnv), 'a located failure').binding, "x");
assert.equal(must(failedAt(absentEnv), 'a located failure').site, "unclaimed");

// Self-contained claim language: fields and callable structure do not depend on
// what the producer happened to export, including missing environment bindings.
{
  const texts = [
    '{ flag: boolean, next?: () => { "a,b": null } }',
    '((boolean, null) => () => boolean) & { value: boolean }',
    '{ "x:y": boolean, "a,b": "a,b" }',
  ];
  for (const text of texts) {
    const claim = surface.parseType(text);
    assert.deepEqual(surface.parseType(surface.printType(claim).text),claim);
    assert(surface.roundTrips(claim));
  }
  assert.throws(() => surface.parseType('{ x: boolean, x?: null }'),/twice/);
  assert.throws(() => surface.parseType('{ x: boolean } @{"fields":[]}'),/metadata/);
  const arrow = surface.parseType('(boolean) => null');
  atom(arrow.atoms[0], "function").and =
    [atom(surface.parseType('() => boolean').atoms[0], "function")];
  assert.deepEqual(surface.parseType(surface.printType(arrow).text),arrow);
  const callable = surface.parseType('((boolean) => null) & { value: boolean }');
  const combined = atom(callable.atoms[0], "callable");
  combined.function.construct = 'absent';
  combined.bag.call = 'absent';
  assert.deepEqual(surface.parseType(surface.printType(callable).text),callable);
  const env = [{name:'x',type:surface.parseType('{ "a,b": "a,b" }')}];
  // Printing a claim value returns null where the surface cannot say it all.
  const printedEnv = surface.printClaimValue('environment',env);
  assert(printedEnv !== null,"the environment is printable");
  assert.deepEqual(surface.readClaimValue('environment',printedEnv,env),env);
}

// The exact native graph covers cycles and simultaneous contracts without
// unfolding or dropping overloads. Its complete syntax is validated JSON.
{
  const graph = decodeGraph([
    [{refs:{first: [["value", [0]]],rest: [[["value", [1]]]],views: []}}],
    [{callable:{first: [["value", [0]]],rest: [[["value", [1]]]],arrows:[[[4],[[[0],[1]],[1]]],[[4],[[],[]]]]}}],
    [{arrs:{arrows:[]}}], ["bool"], ["undef"], ["nul"],
    [{boolLit:{value:false}}], [{boolLit:{value:true}}],
  ]);
  assert.deepEqual(parseGraph(printGraph(graph)),graph);
  const rows = graphDefinitions(graph);
  assert.equal(rows[0].definition,'ref{value: #0} & ref{value: #1}');
  assert.match(rows[1].definition,/\(this: #4, #0, #1\) => #1; \(this: #4\) => never/);
  assert.equal(rows.length,graph.length);
  assert.equal(ob.typeText(graph,[6,7]),'boolean');
  for (const invalid of [[["new-clause"]],[[{refs:{first: [["value", [1]]],rest:[], views: []}}]],[[{boolLit:{value:true,extra:0}}]]])
    assert.throws(() => decodeGraph(invalid));
  const term = decodeTerm({makeAt:{call:{closure:{arity:2,body:{invoke:{f:{var:{i:0}},r:"undef",args:["tru","nul"]}}}},names:["left","right"],inits:["undef","tru"]}});
  for (const code of [{variadic:{fixed:1,body:{var:{i:1}}}},{bound:{target:{var:{i:0}},receiver:"nul",pre:["tru"]}}])
    assert.deepEqual(decodeTerm({makeAt:{call:code,names:[],inits:[]}}),{makeAt:{call:code,names:[],inits:[]}});
  assert.deepEqual(decodeTerm({invoke:{f:{var:{i:0}},r:"undef",args:[{spread:{a:{arr:{elems:[0,null]}}}}]}}),
    {invoke:{f:{var:{i:0}},r:"undef",args:[{spread:{a:{arr:{elems:[0,null]}}}}]}});
  assert.throws(() => decodeTerm({call:{f:{var:{i:0}},args:[]}}));
  assert.deepEqual(parseTerm(printTerm(term)),term);
  assert.throws(() => decodeTerm({var:{i:-1}}));
  assert.throws(() => decodeTerm({read:{a:"nul",extra:0}}));
}

{
  const first = surface.parseType('((boolean) => boolean) & { value: boolean }');
  const union = {top:false,atoms:[...first.atoms,{a:"null"}]};
  assert.deepEqual(surface.parseType(surface.printType(union).text),union);
  const number = surface.parseType('1e+21');
  assert.deepEqual(surface.parseType(surface.printType(number).text),number);
  const rows = [["nul"],[{boolLit:{value:true}}],[{boolLit:{value:false}}],["undef"]];
  // A current-content edit must not erase another field during normalization.
  const multi = surface.parseType('{ value: boolean = (true), other: null }');
  const point = surface.lower(rows,multi);
  assert.deepEqual(point.current, [["value",[1]]]);
  assert.equal(surface.printType(surface.lift(rows,point.type,point.current)).text, surface.printType(multi).text);
  assert.throws(() => surface.lower(rows,surface.parseType('{ value: boolean } @{"call":"custom"}')),/mode/);
}
