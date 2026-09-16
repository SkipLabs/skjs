#!/usr/bin/env node
/**
 * Everywhere the node side tells the compiler not to check something, found
 * with the compiler the project builds with. `tsc` has no option for any of
 * these, and `typescript-eslint` cannot check them here because it does not
 * support TypeScript 7.
 *
 * Three ways of saying it, one report:
 *
 * A written `any` is not a weaker type, it is the absence of one: the compiler
 * stops reading the expression, so a field that does not exist reads as
 * `undefined` rather than failing. That is not hypothetical here — two checks
 * on type-parameter defaults read `tp.default` through an `any` for as long as
 * they existed, and never once fired.
 *
 * An `as` says the value is something the compiler cannot see that it is, and
 * a `!` says it is there when the compiler cannot see that either. Both are
 * assertions: nothing checks them, and a decoder that establishes the fact is
 * what they stand in for.
 *
 * `as const` is not one of them and is not counted: it asserts nothing about a
 * value, it only asks for the literal type of what is already written there.
 */
import fs from "node:fs";
import path from "node:path";
import * as ts from "typescript/unstable/ast";
import { openText } from "./fragment-parse.mts";

/** What was written, and which of the three it is. */
export type Kind = "any" | "as" | "!";
export interface Written {
  file: string;
  line: number;
  column: number;
  kind: Kind;
  text: string;
}

/** `x as const`, which the parser writes as an `as` with a type reference to
 * the reserved name `const`. */
function isConstAssertion(node: ts.Node): boolean {
  if (!ts.isAsExpression(node)) return false;
  const type = node.type;
  return ts.isTypeReferenceNode(type) && ts.isIdentifier(type.typeName) &&
    type.typeName.text === "const";
}

const KINDS: [number, Kind][] = [
  [ts.SyntaxKind.AnyKeyword, "any"],
  [ts.SyntaxKind.AsExpression, "as"],
  [ts.SyntaxKind.NonNullExpression, "!"],
];

/** Each one written in a file, in source order. */
export function writtenAny(file: string): Written[] {
  const text = fs.readFileSync(file, "utf8");
  const source = openText(path.resolve(file), text);
  const found: Written[] = [];
  const walk = (node: ts.Node): void => {
    const kind = KINDS.find(([syntax]) => syntax === node.kind)?.[1];
    if (kind !== undefined && !isConstAssertion(node)) {
      const at = source.getLineAndCharacterOfPosition(node.getStart(source));
      found.push({
        file,
        line: at.line + 1,
        column: at.character + 1,
        kind,
        text: text.split("\n")[at.line]?.trim() ?? "",
      });
    }
    node.forEachChild(walk);
  };
  source.forEachChild(walk);
  return found;
}

const roots = ["verification/tools", "verification/tests", "verification/report-viewer"];
const files = roots.flatMap((dir) =>
  fs
    .readdirSync(dir)
    .filter((name) => name.endsWith(".mts") || name.endsWith(".ts"))
    .map((name) => `${dir}/${name}`),
);
const wanted = KINDS.map(([, kind]) => kind).filter(
  (kind) => !process.argv.some((a) => a.startsWith("--kind=")) ||
    process.argv.includes(`--kind=${kind}`),
);
const found = files.flatMap(writtenAny).filter((w) => wanted.includes(w.kind));
if (process.argv.includes("--list"))
  for (const w of found)
    console.log(`${w.file}:${w.line}:${w.column}  [${w.kind}]  ${w.text}`);
const byFile = new Map<string, number>();
for (const w of found) byFile.set(w.file, (byFile.get(w.file) ?? 0) + 1);
for (const [file, n] of [...byFile].sort((a, b) => b[1] - a[1]))
  console.log(`${String(n).padStart(4)}  ${file}`);
const counts = wanted.map(
  (kind) => `${found.filter((w) => w.kind === kind).length} \`${kind}\``,
);
console.log(`\n${counts.join(", ")} in ${byFile.size} of ${files.length} files`);
