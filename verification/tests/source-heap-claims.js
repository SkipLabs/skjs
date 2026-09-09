"use strict";
// End-to-end source assertions, independent of SKJS inference. Each claim is
// reconstructed at its actual source site before the graph certificate is checked.
const assert = require("node:assert/strict");
const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const { spawnSync } = require("node:child_process");
const { hash } = require("../tools/annotate-source.js");
const verifier = process.argv[2];
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "source-heap-claims-"));
const run = (args) => spawnSync(verifier, args, { encoding: "utf8" });
let passed = 0;
function fixture(body, param = "") {
  const source = `function example(${param}): boolean { ${body} }\n`;
  const file = path.join(tmp, "source.ts");
  const astPath = path.join(tmp, "ast.json"),
    claimsPath = path.join(tmp, "claims.json"),
    evidencePath = path.join(tmp, "evidence.json");
  fs.writeFileSync(file, source);
  const parsed = spawnSync(
    process.execPath,
    [path.resolve(__dirname, "../tools/parse-source.js"), file],
    { encoding: "utf8" },
  );
  assert.equal(parsed.status, 0, parsed.stderr);
  fs.writeFileSync(astPath, parsed.stdout);
  const f = JSON.parse(parsed.stdout).functions[0];
  const entries = [],
    expressions = [];
  const binding = (name) => ({
    name,
    type: name === "cell" ? [4] : [1, 2],
    current: null,
  });
  const expr = (e) => {
    let type;
    switch (e.k) {
      case "id":
        type = binding(e.name).type;
        break;
      case "lit":
        type = e.lit.v === "true" ? [1] : e.lit.v === "false" ? [2] : [0];
        break;
      case "alloc":
        type = [4];
        expr(e.e);
        break;
      case "read":
        type = [1, 2];
        expr(e.e);
        break;
      case "write":
        type = expr(e.rhs);
        expr(e.receiver);
        break;
      default:
        throw Error(`unexpected expression ${e.k}`);
    }
    expressions.push({ pos: e.pos, type, current: null });
    return type;
  };
  const stmts = (ss, names) => {
    for (const st of ss) {
      entries.push({ start: st.pos[0], bindings: names.map(binding) });
      if (st.k === "if") {
        expr(st.cond);
        stmts(st.then, [...names]);
        stmts(st.else_ || [], [...names]);
      } else if (st.k === "while") {
        expr(st.cond);
        stmts(st.body, [...names]);
      } else {
        expr(st.init || st.e);
        if (st.k === "const") names.push(st.name);
      }
    }
  };
  stmts(
    f.body,
    f.params.map((p) => p.name),
  );
  const doc = {
    version: 3,
    profile: "stateful-source-v3",
    // The primitives, then the Boolean cell at label 4.
    types: [
      ["nul"],
      [{ boolLit: { value: true } }],
      [{ boolLit: { value: false } }],
      ["undef"],
      [{ refs: { first: [1, 2], rest: [] } }],
    ],
    file,
    sourceSha256: hash(source),
    functions: [
      {
        name: f.name,
        namePos: f.namePos,
        params: f.params.map((p) => binding(p.name)),
        result: [1, 2],
        entries,
        expressions,
      },
    ],
  };
  const primitive = (labels) => ({
    top: false,
    atoms: labels.map((i) =>
      i === 0
        ? { a: "null" }
        : { a: "booleanlit", v: i === 1 ? "true" : "false" },
    ),
  });
  const rawType = (b) =>
    b.type[0] === 4
      ? {
          top: false,
          atoms: [
            {
              a: "record",
              indexes: { string: "absent", number: "absent", symbol: "absent" },
              call: "absent",
              construct: "absent",
              array: "absent",
              fields: [
                {
                  name: "value",
                  optional: false,
                  read: primitive(b.current ?? [1, 2]),
                  write: primitive([1, 2]),
                },
              ],
            },
          ],
        }
      : primitive(b.type);
  const save = () => fs.writeFileSync(claimsPath, JSON.stringify(doc));
  return {
    f,
    doc,
    entries,
    expressions,
    save,
    produce() {
      save();
      return run([
        "--produce-source-claims",
        astPath,
        claimsPath,
        file,
        evidencePath,
        "10",
      ]);
    },
    check() {
      save();
      return run([
        "--check-source-claims",
        astPath,
        claimsPath,
        file,
        evidencePath,
      ]);
    },
    checkRaw() {
      const c = doc.functions[0];
      const rawPath = path.join(tmp, "raw.json");
      fs.writeFileSync(
        rawPath,
        JSON.stringify([
          {
            file,
            functions: [
              {
                name: c.name,
                namePos: c.namePos,
                params: c.params.map((b) => ({
                  name: b.name,
                  type: rawType(b),
                })),
                retType: primitive(c.result),
                envs: c.entries.map((e) => ({
                  pos: [e.start, e.start + 1],
                  vars: e.bindings.map((b) => ({
                    name: b.name,
                    type: rawType(b),
                  })),
                })),
                exprs: c.expressions.map((e) => ({
                  pos: e.pos,
                  type: rawType(e),
                })),
              },
            ],
          },
        ]),
      );
      return run([
        "--check-stateful-source",
        astPath,
        rawPath,
        file,
        evidencePath,
      ]);
    },
    current(st, R) {
      entries
        .find((e) => e.start === st.pos[0])
        .bindings.find((b) => b.name === "cell").current = R;
    },
    result(e, R) {
      expressions.find((c) => String(c.pos) === String(e.pos)).current = R;
    },
  };
}
function test(name, f) {
  f();
  passed++;
  console.log(`  ${name}: OK`);
}
function accepts(x) {
  const r = x.produce();
  assert.equal(r.status, 0, r.stderr);
  assert.equal(x.check().status, 0);
}
function rejects(x) {
  const r = x.produce();
  assert.notEqual(r.status, 0);
  assert.match(r.stderr, /obligation-diagnostic:/);
  return r;
}
try {
  test("allocation, statement entry and receiver observations are checked", () => {
    const x = fixture(
      "const cell: { value: boolean } = { value: true }; return cell.value;",
    );
    x.result(x.f.body[0].init, [1]);
    x.current(x.f.body[1], [1]);
    x.result(x.f.body[1].e.e, [1]);
    accepts(x);
    const raw = x.checkRaw();
    assert.equal(raw.status, 0, raw.stderr);
    x.result(x.f.body[0].init, [2]);
    assert.notEqual(x.check().status, 0);
    rejects(x);
  });
  test("an impossible observation is retained, not treated as absent", () => {
    const x = fixture(
      "const cell: { value: boolean } = { value: true }; return cell.value;",
    );
    x.current(x.f.body[1], []);
    rejects(x);
  });
  test("write postconditions justify the new observation and reject the old one", () => {
    const x = fixture(
      "const cell: { value: boolean } = { value: true }; cell.value = false; return cell.value;",
    );
    x.current(x.f.body[1], [1]);
    x.current(x.f.body[2], [2]);
    accepts(x);
    x.current(x.f.body[2], [1]);
    assert.notEqual(x.check().status, 0);
    rejects(x);
  });
  test("precise expression claims require an explicit statement-entry observation", () => {
    const x = fixture(
      "const cell: { value: boolean } = { value: true }; return cell.value;",
    );
    x.expressions.find(
      (e) => String(e.pos) === String(x.f.body[1].e.pos),
    ).type = [1];
    rejects(x);
    x.current(x.f.body[1], [1]);
    accepts(x);
    assert.equal(x.checkRaw().status, 0);
  });
  test("guarded read facts justify both branch-entry observations", () => {
    const x = fixture(
      "const cell: { value: boolean } = { value: flag }; if (cell.value) { return cell.value; } else { return cell.value; }",
      "flag: boolean",
    );
    x.current(x.f.body[1].then[0], [1]);
    x.current(x.f.body[1].else_[0], [2]);
    accepts(x);
    x.current(x.f.body[1].then[0], [2]);
    rejects(x);
  });
  test("both incoming branches justify a supplied merge observation", () => {
    const x = fixture(
      "const cell: { value: boolean } = { value: true }; if (flag) { cell.value = true; } else { cell.value = false; } return cell.value;",
      "flag: boolean",
    );
    x.current(x.f.body[2], [1, 2]);
    accepts(x);
    x.current(x.f.body[2], [1]);
    rejects(x);
  });
  test("loop-head observations must survive the backedge", () => {
    const x = fixture(
      "const cell: { value: boolean } = { value: true }; while (flag) { cell.value = false; } return cell.value;",
      "flag: boolean",
    );
    x.current(x.f.body[1], [1, 2]);
    accepts(x);
    x.current(x.f.body[1], [1]);
    rejects(x);
  });
  console.log(`Source heap claims: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
