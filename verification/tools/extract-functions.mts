import fs from "node:fs";
import path from "node:path";
import * as ts from "typescript/unstable/ast";
import { projectFor } from "./parse-source.mts";

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

/** Exact named function bodies for dependency-free source fixtures.
 * Dependencies are not synthesized: callers select self-contained functions. */
export function extractFunctions(file: string, names: string[]): string {
  const functions = listFunctions(file).filter(f => names.includes(f.name));
  if (functions.length !== names.length || new Set(names).size !== names.length)
    throw Error(`expected each selected function exactly once in ${file}`);
  return functions.map(f => f.text).join("\n\n") + "\n";
}
