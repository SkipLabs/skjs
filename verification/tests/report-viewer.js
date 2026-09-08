#!/usr/bin/env node
"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const {
  fromBundle,
  parseReport,
  renderType,
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
const annotated = render(source, manifest);
assert.equal(parseReport(annotated).source, source);
assert.equal(parseReport(annotated).functions[0].exprs[0].type, claim.type);
for (const file of ["typeof_narrow.accepted", "inverted_narrowing.rejected"]) {
  const sample = fs.readFileSync(
    `verification/report-viewer/samples/${file}.annotated.ts`,
    "utf8",
  );
  assert.equal(parseReport(sample).functions.length, 1);
}
console.log(
  "Report viewer: structured payloads, UTF-16/multiline spans, gaps, comparison, and legacy samples passed",
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
