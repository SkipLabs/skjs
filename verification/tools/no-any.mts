#!/usr/bin/env node
/**
 * Every written `any` in the node side, found with the compiler the project
 * builds with. `noImplicitAny` is already on and governs the ones nobody
 * wrote; this is for the ones somebody did, which `tsc` has no option for and
 * `typescript-eslint` cannot check here because it does not support
 * TypeScript 7.
 *
 * A written `any` is not a weaker type, it is the absence of one: the compiler
 * stops reading the expression, so a field that does not exist reads as
 * `undefined` rather than failing. That is not hypothetical here — two checks
 * on type-parameter defaults read `tp.default` through an `any` for as long as
 * they existed, and never once fired.
 */
import fs from "node:fs";
import path from "node:path";
import * as ts from "typescript/unstable/ast";
import { openText } from "./fragment-parse.mts";

export interface Written {
  file: string;
  line: number;
  column: number;
  text: string;
}

/** Each `any` written in a file, in source order. */
export function writtenAny(file: string): Written[] {
  const text = fs.readFileSync(file, "utf8");
  const source = openText(path.resolve(file), text);
  const found: Written[] = [];
  const walk = (node: ts.Node): void => {
    if (node.kind === ts.SyntaxKind.AnyKeyword) {
      const at = source.getLineAndCharacterOfPosition(node.getStart(source));
      found.push({
        file,
        line: at.line + 1,
        column: at.character + 1,
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
const found = files.flatMap(writtenAny);
if (process.argv.includes("--list"))
  for (const w of found) console.log(`${w.file}:${w.line}:${w.column}  ${w.text}`);
const byFile = new Map<string, number>();
for (const w of found) byFile.set(w.file, (byFile.get(w.file) ?? 0) + 1);
for (const [file, n] of [...byFile].sort((a, b) => b[1] - a[1]))
  console.log(`${String(n).padStart(4)}  ${file}`);
console.log(`\n${found.length} written \`any\` in ${byFile.size} of ${files.length} files`);
