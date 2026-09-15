import fs from "node:fs";
import path from "node:path";
import * as ts from "typescript/unstable/ast";
import { openText, projectFor } from "./fragment-parse.mts";

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

/** Everything at the top level of a file that is not a function with a body:
 * ambient declarations, type aliases, interfaces and classes. A censused
 * function is extracted alone, and without these it can fail for want of a
 * name its own file declares — an error about the extraction rather than
 * about the program. They are context, never examples. */
export function listContext(file: string): string {
  const source = fs.readFileSync(file, "utf8");
  const absolute = path.resolve(file);
  const sf = projectFor(absolute).program.getSourceFile(absolute);
  if (!sf) throw Error(`missing compiler source for ${file}`);
  return sf.statements
    .filter(s => !(ts.isFunctionDeclaration(s) && s.name && s.body))
    .map(s => source.slice(s.getStart(sf), s.end))
    .join("\n\n");
}

/** The named top-level functions of a version of a file that is not on disk,
 * so a corpus can ask what a file held before a commit. The path is a label
 * the compiler keys the text by; nothing reads it back. */
export function listFunctionsOf(label: string, text: string): string[] {
  const sf = openText(path.resolve(label), text);
  return sf.statements.filter(ts.isFunctionDeclaration)
    .filter(f => f.name && f.body).map(f => f.name!.text);
}
