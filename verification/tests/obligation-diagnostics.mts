import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { hash, fromSourceClaims, verifySkjs, } from "../tools/annotate-source.mts";
import { presentObligation } from "../tools/diagnostic-view.mts";
import { parseGraph, printGraph } from "../tools/type-graph.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
const __dirname = path.dirname(import.meta.filename);
const verifier = path.resolve(process.argv[2]);
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "obligation-diagnostics-"));
let passed = 0;
const test = (name: string, f: any) => {
  f();
  passed++;
  console.log(`  ${name}: OK`);
};
try {
  // Broad claims are true, but cannot carry the precision the result needs.
  const source = "function singleton(flag: true): true { return flag; }\n";
  const file = path.join(tmp, "source.ts");
  fs.writeFileSync(file, source);
  const parsed = spawnSync(
    process.execPath,
    [path.resolve(__dirname, "../tools/parse-source.mts"), file],
    { encoding: "utf8" },
  );
  assert.equal(parsed.status, 0, parsed.stderr);
  const f = JSON.parse(parsed.stdout).functions[0],
    pos = f.body[0].e.pos;
  // Typed as the format itself, so an edit that stops being a valid sidecar
  // is an error here rather than a verifier rejection with a confusing message.
  const base: SourceClaims = {
    types: [
      ["nul"],
      [{ boolLit: { value: true } }],
      [{ boolLit: { value: false } }],
      ["undef"],
    ],
    file,
    sourceSha256: hash(source),
    functions: [
      {
        name: f.name,
        namePos: f.namePos,
        params: [{ name: "flag", type: [1], current: null }],
        result: [1],
        entries: [
          {
            start: f.body[0].pos[0],
            bindings: [{ name: "flag", type: [1, 2], current: null }],
          },
        ],
        expressions: [{ pos, type: [1, 2], current: null }],
      },
    ],
  };
  const verify = (entry: any, expression: any) => {
    const d: SourceClaims = structuredClone(base);
    d.functions[0].entries[0].bindings[0].type = entry;
    d.functions[0].expressions[0].type = expression;
    return verifySkjs(
      file,
      source,
      d,
      file,
      fromSourceClaims(source, file, d, "manual"),
      verifier,
      6,
      true,
    ).results[0];
  };
  // The source map is the reason a reader never shows a slot number, so a live
  // record must carry one descriptor per context binding, each describable.
  test("a live diagnostic names every binding in its context", () => {
    const d = verify([1, 2], [1, 2]).obligation;
    const map = d.source.sourceMap;
    assert.equal(map.context.length, d.sequent.context.length);
    for (const descriptor of map.context)
      assert(
        descriptor.name || Array.isArray(descriptor.span),
        JSON.stringify(descriptor),
      );
    assert.deepEqual(
      map.context.map((x: any) => x.name),
      ["", "flag"],
    );
  });
  test("broad claims locate the separate return-contract obligation", () => {
    const r = verify([1, 2], [1, 2]);
    assert.equal(r.status, "not-established");
    const d = r.obligation;
    assert.equal(d.source.sourceMap.role, "return-contract");
    assert.deepEqual(d.source.sourceMap.pos, pos);
    assert.equal(d.source.sourceMap.environmentStart, f.body[0].pos[0]);
    assert.deepEqual(d.sequent.type, [1]);
    assert.deepEqual(d.sequent.context[0], [1, 2]);
    assert.equal(d.input.sourceSha256, hash(source));
    assert.equal(d.input.functionName, f.name);
    assert.deepEqual(r.obligationView.focus, {
      subject:"flag", available:"boolean", required:"true", requiredLabel:"Required return type",
    });
    assert.equal(r.obligationView.summary,"The available claim for flag is boolean. This return requires true.");
    assert.equal(r.obligationView.namedConclusion,"flag: true");
    // Names follow the actual term slot, not a guess that every goal is slot 0.
    const changed = structuredClone(d);
    changed.sequent.term = {var:{i:1}};
    changed.source.sourceMap.context = [{name:"saved",span:null},{name:"cell.value",span:null}];
    assert.equal(presentObligation(changed,source).focus?.subject,"cell.value");
    changed.sequent.term = {read:{a:{var:{i:1}}}};
    assert.equal(presentObligation(changed,source).focus,undefined);

  });
  test("a checked immutable value justifies the return despite a wider expression claim", () => {
    const r = verify([1], [1, 2]);
    assert.equal(r.status, "verified");
    assert.equal(r.obligation, undefined);
  });
  test("strengthening only the expression fails a different obligation at the same span", () => {
    const a = verify([1, 2], [1, 2]).obligation,
      b = verify([1, 2], [1]).obligation;
    assert.notEqual(a.id, b.id);
    assert.equal(b.source.sourceMap.role, "node-typing");
    assert.deepEqual(a.source.sourceMap.pos, b.source.sourceMap.pos);
    assert.deepEqual(b.sequent.context, [[1, 2]]);
    assert.deepEqual(b.sequent.type, [1]);
    assert.notEqual(a.input.claimsSha256, b.input.claimsSha256);
  });
  test("strengthening both claims verifies independently", () =>
    assert.equal(verify([1], [1]).status, "verified"));
  test("an edge diagnostic identifies the selected mapping even with a shared destination", () => {
    const request: any = {
      types: [
        [{ boolLit: { value: true } }],
        [{ boolLit: { value: false } }],
        ["bool"],
      ],
      program: [
        {
          expression: "tru",
          continuation: {
            branchBind: {
              yes: { label: 1, mapping: [0] },
              no: { label: 1, mapping: [2] },
            },
          },
        },
        { expression: { var: { i: 0 } }, continuation: "ret" },
      ],
      claims: [
        { context: [[0], [2]], type: [2] },
        { context: [[0]], type: [0] },
      ],
      result: [0],
      start: 0,
      inputs: [[0], [2]],
    };
    const rp = path.join(tmp, "request.json"),
      ep = path.join(tmp, "evidence.json");
    fs.writeFileSync(rp, JSON.stringify(request));
    const r = spawnSync(verifier, ["--produce-stateful", rp, ep, "6"], {
      encoding: "utf8",
    });
    assert.notEqual(r.status, 0);
    const d = readDiagnostic(r.stderr);
    assert(d, r.stderr);
    assert.deepEqual(parseGraph(printGraph(d.types)),d.types);
    const shown = presentObligation(d,"");
    assert.match(shown.judgement!.text,/⊢/);
    assert.equal(shown.graph.length,d.types.length);
    assert(d.kind === "edge-coverage");
    // The transfer and the destination's claim are optional in the record and
    // required by what follows, so assert them rather than assume them.
    assert(d.transfer && d.destination.claim);
    assert.equal(d.edgeIndex, 1);
    assert.equal(d.source.label, 0);
    assert.equal(d.destination.label, 1);
    assert.deepEqual(d.transfer.target.mapping, [2]);
    assert.equal(d.transfer.booleanObservation, false);
    assert.deepEqual(d.transfer.available, [[2], [0], [2]]);
    assert.deepEqual(d.destination.claim.context, [[0]]);
    request.program[0].continuation = {
      tagBind: {
        test: "isNul",
        yes: { label: 1, mapping: [0] },
        no: { label: 1, mapping: [2] },
      },
    };
    fs.writeFileSync(rp, JSON.stringify(request));
    const tagged = spawnSync(verifier, ["--produce-stateful", rp, ep, "6"], {
      encoding: "utf8",
    });
    assert.notEqual(tagged.status, 0);
    const td = readDiagnostic(tagged.stderr);
    assert(td, tagged.stderr);
    assert(td.kind === "edge-coverage" && td.transfer);
    assert.equal(td.edgeIndex, 1);
    assert.equal(td.transfer.booleanObservation, null);
    assert.deepEqual(td.transfer.tagObservation, {
      test: "isNul",
      answer: false,
      slot: 0,
    });
  });
  test("unknown malformed and duplicate diagnostic records are not interpreted", () => {
    const {input, ...rawDiagnostic} = verify([1, 2], [1, 2]).obligation;
    const line = "obligation-diagnostic: " + JSON.stringify(rawDiagnostic);
    assert(readDiagnostic(line));
    const parsed = JSON.parse(line.slice("obligation-diagnostic: ".length));
    assert.equal(readDiagnostic("obligation-diagnostic: null"),undefined);
    for (const types of [[["new-clause"]],[[{refs:{first:[99],rest:[]}}]]])
      assert.equal(readDiagnostic("obligation-diagnostic: " + JSON.stringify({...parsed,types})),undefined);
    assert.equal(readDiagnostic(line + "\n" + line), undefined);
    assert.equal(readDiagnostic("obligation-diagnostic: {"), undefined);
    assert.equal(
      readDiagnostic(line.replace('"outcome":"not-established"', '"outcome":"refuted"')),
      undefined,
    );
  });
  console.log(`Obligation diagnostics: ${passed} passed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
