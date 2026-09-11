/*
 * What `tsc --noEmit` says about one file, for the suites that assert
 * TypeScript's own verdict on a fixture rather than the verifier's.
 *
 * The checking regime is the fixture's own `tsconfig.json`, not options passed
 * from the calling suite: a corpus file is claimed and checked under one
 * configuration, and a suite asserting "TypeScript accepts this" should be
 * asserting it about that configuration. A file no project claims is refused
 * rather than checked under weaker defaults.
 */
import { DiagnosticCategory } from "typescript/unstable/sync";
import { resolve } from "node:path";
import { projectFor } from "./parse-source.mts";

export interface TypeError {
  file: string;
  /** Offset of the reported span, in UTF-16 code units. */
  pos: number;
  code: number;
  text: string;
}

export function typeErrors(file: string): TypeError[] {
  const absolute = resolve(file);
  const project = projectFor(absolute);
  if (!project.compilerOptions.strict)
    throw new Error(
      `${file} is not covered by a tsconfig.json with "strict": true`,
    );
  return [
    ...project.program.getSyntacticDiagnostics(absolute),
    ...project.program.getSemanticDiagnostics(absolute),
  ]
    .filter((d) => d.category === DiagnosticCategory.Error)
    .map((d) => ({
      file: d.fileName ?? absolute,
      pos: d.pos,
      code: d.code,
      text: d.text,
    }));
}
