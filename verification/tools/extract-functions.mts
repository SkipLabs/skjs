import fs from "node:fs";
import path from "node:path";
import * as ts from "typescript/unstable/ast";
import { projectFor } from "./fragment-parse.mts";

/** Every named top-level function, with its exact source text. One project
 * open per file: callers that want many functions must not ask one at a time.
 * Ambient declarations have no body and are context, never examples. */
export function listFunctions(file: string): { name: string; text: string }[] {
  const source = fs.readFileSync(file, "utf8");
  const absolute = path.resolve(file);
  const sf = projectFor(absolute).program.getSourceFile(absolute);
  if (!sf) throw Error(`missing compiler source for ${file}`);
  return sf.statements.filter(ts.isFunctionDeclaration)
    .filter(f => f.name && f.body)
    .map(f => ({ name: f.name!.text, text: source.slice(f.getStart(sf), f.end) }));
}
