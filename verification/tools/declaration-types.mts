/** The declaration document shared by the source parser, the Fragment AST
 * and readers. TypeScript's checker, under the source's configured project,
 * decides which declaration each name denotes; the document records the source
 * equations of the declarations reached. They are not evidence that a
 * producer's claim follows from them. This module has no runtime dependencies,
 * so importing its types does not pull the compiler into a reader's project. */
import type { Span } from "./span.mts";
/** One type alias or interface: its module (a path relative to the project's
 * tsconfig, the client's absolute path, or `typescript/lib/<file>`), its name
 * and its span there. */
export type DeclarationIdentity = {
  module: string;
  name: string;
  span: Span;
};
/** A name the client binds to a declaration: an imported name (the span is
 * the import declaration's) or one of the client's own declarations. */
export type TypeRoot = {
  binding:
    | { kind: "import"; local: string; imported: string; specifier: string; span: Span }
    | { kind: "local"; local: string; span: Span };
  declaration: DeclarationIdentity;
};
/** A reference inside a declaration, with the declaration TypeScript resolves it to. */
export type Reference = {
  name: string;
  span: Span;
  arguments: Span[];
  target: DeclarationIdentity;
};
/** A source type before translation to the positive graph: a declaration's
 * equation or a function annotation, read by type-term.mts. */
export type TypeTerm =
  | { k: "atom"; name: "null" | "undefined" | "boolean" | "number" | "string" | "unknown" | "never" | "void"; span: Span }
  | { k: "literal"; name: "true" | "false" | "string" | "number"; text: string; span: Span }
  | { k: "union" | "intersection"; parts: TypeTerm[]; span: Span }
  | { k: "array"; readonly: boolean; element: TypeTerm; span: Span }
  | { k: "tuple"; readonly: boolean; required: TypeTerm[];
      optional: TypeTerm[]; rest: TypeTerm | null; span: Span }
  | { k: "object"; fields: { name: string; optional: boolean; readonly: boolean; type: TypeTerm; span: Span }[];
      stringIndex: { readonly: boolean; value: TypeTerm; span: Span } | null;
      calls: Extract<TypeTerm, { k: "function" }>[]; span: Span }
  | { k: "function"; receiver: TypeTerm | null; params: TypeTerm[];
      rest: TypeTerm | null; result: TypeTerm; span: Span }
  /** The containing declaration is the implicit receiver of a method signature. */
  | { k: "self"; span: Span }
  | { k: "parameter"; index: number; span: Span }
  /** A type parameter of an enclosing function, by its spelling: annotations
   * only. A declaration's own parameters are positional. */
  | { k: "binder"; name: string; span: Span }
  | { k: "reference"; reference: Reference; args: TypeTerm[]; span: Span };
export type TypeDefinition = {
  declaration: DeclarationIdentity;
  sha256: string;
  parameters: { name: string; span: Span; bound: TypeTerm | null;
    default: TypeTerm | null }[];
  body: Span;
  /** Interface heritage remains a source edge; consumers derive its members. */
  bases: TypeTerm[];
  expression: TypeTerm;
  references: Reference[];
};
/** Every declaration reachable from the roots, each once. `sha256` on a
 * definition records the bytes of its module; nothing checks it. */
export type DeclarationDocument = {
  roots: TypeRoot[];
  definitions: TypeDefinition[];
};
