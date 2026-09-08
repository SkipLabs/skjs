#!/usr/bin/env node
"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const {
  fromBundle,
  parseReport,
  renderType,
  findMark,
  markIdOf,
  nextMark,
  summarize,
  parseReportLink,
  reportLink,
} = require("../report-viewer/model.js");
const { hash, render } = require("../tools/annotate-source.js");

const source =
  "// 😀\nfunction f(x: boolean): boolean {\n  return (\n    x\n  );\n}\n";
const start = source.indexOf("function"),
  expr = source.indexOf("(\n"),
  end = source.indexOf(");") + 1;
const claim = {
  pos: [expr, end],
  type: '{"reference":{"to":7}}',
  raw: { reference: { to: 7 } },
};
const manifest = {
  version: 1,
  producer: "manual",
  source: { file: "f.ts", sha256: hash(source) },
  functions: [
    {
      id: "f0",
      name: "f",
      namePos: [source.indexOf("f("), source.indexOf("f(") + 1],
      pos: [start, source.length - 1],
      entries: [],
      expressions: [{ id: "f0x0", ...claim }],
    },
  ],
  diagnostics: "Producer stopped at this expression",
  gaps: [],
  results: null,
};
const bundle = { source, manifest };
const report = fromBundle(bundle);
assert.equal(report.functions[0].exprs[0].type, claim.type);
assert.deepEqual(JSON.parse(report.functions[0].exprs[0].raw), claim.raw);
assert.equal(
  report.source.slice(...report.functions[0].exprs[0].pos),
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
  changes: [{ span: [expr, end], status: "changed", kind: "expression" }],
};
assert.match(
  fromBundle(changed).functions[0].gaps[0].detail,
  /claim edit: changed/,
);
const missing = structuredClone(bundle);
missing.manifest.functions = [];
missing.manifest.gaps = [
  { id: "g0", pos: [start, source.length - 1], status: "claims unavailable" },
];
assert.equal(fromBundle(missing).functions[0].gaps.length, 1);
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
invalidMissing.manifest.missingFunctions[0].missingSites[0].pos = [0, 1];
assert.throws(() => fromBundle(invalidMissing), /outside function/);
invalidMissing.manifest.missingFunctions[0].namePos = [0, 1];
assert.throws(() => fromBundle(invalidMissing), /identity/);
const annotated = render(source, manifest);
assert.equal(parseReport(annotated).source, source);
assert.equal(parseReport(annotated).functions[0].exprs[0].type, claim.type);
// Realistic comment-format input, built here rather than stored: a rejected
// snapshot with a recovery label, an unvisited statement and an undecodable
// binding. Reading it back must recover the exact source, including non-ASCII.
{
  const text =
    "// 🌍\nfunction partial(): boolean {\n  const x: boolean = true;\n  return x;\n}\n";
  const nameAt = text.indexOf("partial"),
    first = text.indexOf("const");
  const report = {
    version: 1,
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
  assert.equal(partialFn.exprs[0].recovery, true);
  assert.equal(partialFn.entries[0].bindings[0].unavailable, true);
  const unvisited = partialFn.gaps.find(
    (g) => g.reason === "statement-not-visited",
  );
  assert(unvisited);
  assert.equal(text.slice(...unvisited.pos), "return x;");
  assert.equal(partialFn.id, "f0");
  assert.equal(partialFn.exprs[0].id, "f0x0");
}

// Marks are addressed by the writer's manifest id, not by their position in a
// function's lists: a link or a quoted id must survive changed claims.
const addressed = fromBundle(bundle);
assert.deepEqual(findMark(addressed, "f0x0"), {
  fn: 0,
  id: "e0",
  manifestId: "f0x0",
});
assert.deepEqual(findMark(addressed, "f0"), {
  fn: 0,
  id: null,
  manifestId: "f0",
});
assert.equal(findMark(addressed, "f9x9"), null);
assert.equal(findMark(addressed, ""), null);
assert.equal(markIdOf(addressed, 0, "e0"), "f0x0");
assert.equal(markIdOf(addressed, 0, null), "f0");
assert.equal(markIdOf(addressed, 0, "e7"), "");
const shifted = structuredClone(bundle);
shifted.manifest.functions[0].expressions.unshift({
  id: "f0x9",
  pos: [source.indexOf("x\n"), source.indexOf("x\n") + 1],
  type: "boolean",
});
assert.equal(findMark(fromBundle(shifted), "f0x0").id, "e1");
const entryBundle = structuredClone(bundle);
entryBundle.manifest.functions[0].entries = [
  { id: "f0e0", pos: [start, end], bindings: [] },
];
assert.equal(findMark(fromBundle(entryBundle), "f0e0").id, "n0");
const drawn = ["n0", "e0", "e1", "g0"];
assert.equal(nextMark(drawn, "e0", 1), "e1");
assert.equal(nextMark(drawn, "e0", -1), "n0");
assert.equal(nextMark(drawn, "g0", 1), "n0");
assert.equal(nextMark(drawn, "n0", -1), "g0");
assert.equal(nextMark(drawn, null, 1), "n0");
assert.equal(nextMark(drawn, null, -1), "g0");
assert.equal(nextMark(drawn, "e9", 1), "n0");
assert.equal(nextMark([], null, 1), null);
assert.deepEqual(summarize(fromBundle(missing).functions), {
  functions: 1,
  gaps: 1,
  status: { "not-established": 1 },
});
assert.deepEqual(summarize(addressed.functions), {
  functions: 1,
  gaps: 0,
  status: { "not-run": 1 },
});
assert.deepEqual(parseReportLink("?file=a/b.ts&verify=1", "#f0x0"), {
  file: "a/b.ts",
  verify: true,
  mark: "f0x0",
});
assert.deepEqual(parseReportLink("", ""), {
  file: "",
  verify: false,
  mark: "",
});
assert.equal(parseReportLink("?file=a.ts", "").verify, false);
assert.equal(
  reportLink({ file: "a/b.ts", verify: true, mark: "f0x0" }),
  "?file=a%2Fb.ts&verify=1#f0x0",
);
assert.equal(reportLink({ file: "", verify: false, mark: "" }), "");
assert.equal(reportLink({ file: "", verify: false, mark: "g2" }), "#g2");
{
  const round = { file: "verification/x.ts", verify: false, mark: "f1e2" };
  const link = reportLink(round);
  assert.deepEqual(
    parseReportLink(link.split("#")[0], "#" + link.split("#")[1]),
    round,
  );
}

console.log(
  "Report viewer: structured payloads, UTF-16/multiline spans, gaps, comparison, addressing, and legacy samples passed",
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
assert.equal(
  fromBundle(failureBundle).functions[0].exprs[0].failure,
  "proof search stopped",
);
for (const kind of ["edge-obligation", "source-limitation"]) {
  failureBundle.manifest.results[0].location.kind = kind;
  assert.equal(
    fromBundle(failureBundle).functions[0].exprs[0].failureKind,
    kind,
  );
}
failureBundle.manifest.functions[0].entries = [
  { pos: [start, end], bindings: [] },
];
failureBundle.manifest.results[0].location = {
  kind: "environment-obligation",
  start,
};
assert.equal(
  fromBundle(failureBundle).functions[0].entries[0].failureKind,
  "environment-obligation",
);
delete failureBundle.manifest.results[0].location;
assert.equal(
  fromBundle(failureBundle).functions[0].exprs[0].failure,
  undefined,
);
failureBundle.manifest.results[0].location = {
  kind: "expression-obligation",
  pos: claim.pos,
};
failureBundle.manifest.results[0].status = "verified";
assert.equal(
  fromBundle(failureBundle).functions[0].exprs[0].failure,
  undefined,
);

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
  assert.equal(f.gaps[0].failureKind, "missing-expression-claim");
  assert.match(f.gaps[0].failure, /no claimed type/);
  assert.equal(f.detail, absent.manifest.results[0].detail);
  assert.equal(f.result.status, "not-established");
}
// Without a gap at that place — an older report — the claim there still carries it.
const absentNoGap = structuredClone(absent);
absentNoGap.manifest.gaps = [];
absentNoGap.manifest.functions[0].expressions = [{ id: "f0x0", ...claim }];
assert.equal(
  fromBundle(absentNoGap).functions[0].exprs[0].failureKind,
  "missing-expression-claim",
);
const absentEnv = structuredClone(absent);
absentEnv.manifest.gaps = [
  { id: "g0", pos: [start, end], status: "statement not visited" },
];
absentEnv.manifest.results[0].location = {
  kind: "missing-environment-claim",
  start,
  binding: "x",
};
{
  const f = fromBundle(absentEnv).functions[0];
  assert.equal(f.gaps[0].failureKind, "missing-environment-claim");
  assert.equal(f.gaps[0].failureBinding, "x");
}
