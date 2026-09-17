import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { hash } from "../tools/annotate-source.mts";
import type { Ast, Expr, Stmt } from "../tools/fragment.mts";
import type { ClaimType } from "../tools/claim.mts";
import type { Labels } from "../tools/type-graph.mts";
import type { Span } from "../tools/span.mts";
import type {
  ClaimType as SidecarClaim,
  EntryClaim,
  ExpressionClaim,
  NamedPoint,
  Point,
  SourceClaims,
} from "../tools/source-claims.mts";
import { expr, must, at as nth, sole, stmt } from "./edits.mts";

/** The labels a claim states, where this fixture only ever states labels. */
const labelsOf = (type: SidecarClaim): Labels => {
  if (!Array.isArray(type)) throw Error("this fixture states labels");
  return type;
};
const __dirname = path.dirname(import.meta.filename);
// End-to-end source assertions, independent of SKJS inference. Each claim is
// reconstructed at its actual source site before the graph certificate is checked.






const verifier = process.argv[2];
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "source-heap-claims-"));
const run = (args: string[]) => spawnSync(verifier, args, { encoding: "utf8" });
let passed = 0;
function fixture(body: string, param = "") {
  const source = `function example(${param}): boolean { ${body} }\n`;
  const file = path.join(tmp, "source.ts");
  const astPath = path.join(tmp, "ast.json"),
    claimsPath = path.join(tmp, "claims.json"),
    evidencePath = path.join(tmp, "evidence.json");
  fs.writeFileSync(file, source);
  const parsed = spawnSync(
    process.execPath,
    [path.resolve(__dirname, "../tools/fragment-parse.mts"), file],
    { encoding: "utf8" },
  );
  assert.equal(parsed.status, 0, parsed.stderr);
  fs.writeFileSync(astPath, parsed.stdout);
  const ast: Ast = JSON.parse(parsed.stdout);
  const f = must(ast.functions[0], "the parsed function");
  const entries: EntryClaim[] = [],
    expressions: ExpressionClaim[] = [];
  const binding = (name: string): NamedPoint => ({
    name,
    type: name === "cell" ? [4] : [1, 2],
    current: null,
  });
  /** The claim this fixture states for one expression, and its subexpressions.
   * Every label it uses is one of the table's own. */
  const expr = (e: Expr): Labels => {
    let type: Labels;
    switch (e.k) {
      case "id":
        type = labelsOf(binding(e.name).type);
        break;
      case "lit":
        type = e.lit.a === "booleanlit" ? (e.lit.v === "true" ? [1] : [2]) : [0];
        break;
      case "alloc":
        type = [4];
        e.fields.forEach((f) => expr(f.e));
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
  const stmts = (ss: Stmt[], names: string[]) => {
    for (const st of ss) {
      entries.push({ start: st.pos[0], bindings: names.map(binding) });
      if (st.k === "if") {
        expr(st.cond);
        stmts(st.then, [...names]);
        stmts(st.else_ || [], [...names]);
      } else if (st.k === "while") {
        expr(st.cond);
        stmts(st.body, [...names]);
      } else if (st.k === "const" || st.k === "let") {
        for (const b of st.bindings) {
          expr(b.init);
          if (st.k === "const") names.push(b.name);
        }
      } else if (st.k === "effect" || st.k === "return") {
        expr(st.e);
      }
    }
  };
  stmts(
    f.body,
    f.params.map((p) => p.name),
  );
  const doc: SourceClaims = {
    // The primitives, then the Boolean cell at label 4.
    types: [
      ["nul"],
      [{ boolLit: { value: true } }],
      [{ boolLit: { value: false } }],
      ["undef"],
      [{ refs: { first: [["value", [1, 2]]], rest: [], views: [] } }],
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
  const primitive = (labels: Labels): ClaimType => ({
    top: false,
    atoms: labels.map((i) =>
      i === 0
        ? { a: "null" }
        : { a: "booleanlit", v: i === 1 ? "true" : "false" },
    ),
  });
  /** The same claim in the producer's own encoding, which is what `checkRaw`
   * hands the other entry point. */
  const rawType = (b: Point): ClaimType =>
    labelsOf(b.type)[0] === 4
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
                  read: primitive(b.current?.[0]?.[1] ?? [1, 2]),
                  write: primitive([1, 2]),
                },
              ],
            },
          ],
        }
      : primitive(labelsOf(b.type));
  const save = () => fs.writeFileSync(claimsPath, JSON.stringify(doc));
  return {
    f,
    /** The i-th statement of the body, and what it carries: an initializer, a
     * returned expression, an arm. Each check names the one it is about. */
    at: (i: number) => nth(f.body, i),
    init: (i: number) => sole(stmt(nth(f.body, i), "const")).init,
    returned: (i: number) => stmt(nth(f.body, i), "return").e,
    arm: (i: number, which: "then" | "else_") => {
      const branch = stmt(nth(f.body, i), "if");
      return nth(which === "then" ? branch.then : must(branch.else_, "an else arm"), 0);
    },
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
                retType: primitive(labelsOf(c.result)),
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
    current(st: { pos: Span }, R: Labels | null) {
      must(
        must(entries.find((e) => e.start === st.pos[0]), "an entry")
          .bindings.find((b) => b.name === "cell"),
        "the cell's claim",
      ).current = R === null ? null : [["value", R]];
    },
    result(e: { pos: Span }, R: Labels | null) {
      must(
        expressions.find((c) => String(c.pos) === String(e.pos)),
        "a claim there",
      ).current = R === null ? null : [["value", R]];
    },
  };
}
function test(name: string, f: () => void) {
  f();
  passed++;
  console.log(`  ${name}: OK`);
}
type Fixture = ReturnType<typeof fixture>;
function accepts(x: Fixture) {
  const r = x.produce();
  assert.equal(r.status, 0, r.stderr);
  assert.equal(x.check().status, 0);
}
function rejects(x: Fixture) {
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
    x.result(x.init(0), [1]);
    x.current(x.at(1), [1]);
    x.result(expr(x.returned(1), "read").e, [1]);
    accepts(x);
    const raw = x.checkRaw();
    assert.equal(raw.status, 0, raw.stderr);
    x.result(x.init(0), [2]);
    assert.notEqual(x.check().status, 0);
    rejects(x);
  });
  test("an impossible observation is retained, not treated as absent", () => {
    const x = fixture(
      "const cell: { value: boolean } = { value: true }; return cell.value;",
    );
    x.current(x.at(1), []);
    rejects(x);
  });
  test("write postconditions justify the new observation and reject the old one", () => {
    const x = fixture(
      "const cell: { value: boolean } = { value: true }; cell.value = false; return cell.value;",
    );
    x.current(x.at(1), [1]);
    x.current(x.at(2), [2]);
    accepts(x);
    x.current(x.at(2), [1]);
    assert.notEqual(x.check().status, 0);
    rejects(x);
  });
  test("precise expression claims require an explicit statement-entry observation", () => {
    const x = fixture(
      "const cell: { value: boolean } = { value: true }; return cell.value;",
    );
    must(
      x.expressions.find((e) => String(e.pos) === String(x.returned(1).pos)),
      "a claim at the returned expression",
    ).type = [1];
    rejects(x);
    x.current(x.at(1), [1]);
    accepts(x);
    assert.equal(x.checkRaw().status, 0);
  });
  test("guarded read facts justify both branch-entry observations", () => {
    const x = fixture(
      "const cell: { value: boolean } = { value: flag }; if (cell.value) { return cell.value; } else { return cell.value; }",
      "flag: boolean",
    );
    x.current(x.arm(1, "then"), [1]);
    x.current(x.arm(1, "else_"), [2]);
    accepts(x);
    x.current(x.arm(1, "then"), [2]);
    rejects(x);
  });
  test("both incoming branches justify a supplied merge observation", () => {
    const x = fixture(
      "const cell: { value: boolean } = { value: true }; if (flag) { cell.value = true; } else { cell.value = false; } return cell.value;",
      "flag: boolean",
    );
    x.current(x.at(2), [1, 2]);
    accepts(x);
    x.current(x.at(2), [1]);
    rejects(x);
  });
  test("loop-head observations must survive the backedge", () => {
    const x = fixture(
      "const cell: { value: boolean } = { value: true }; while (flag) { cell.value = false; } return cell.value;",
      "flag: boolean",
    );
    x.current(x.at(1), [1, 2]);
    accepts(x);
    x.current(x.at(1), [1]);
    rejects(x);
  });
  console.log(`Source heap claims: ${passed} passed, 0 failed`);
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}
