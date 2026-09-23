/** The imported declaration document shared by resolution, the Fragment AST,
 * and readers. These are source equations and provenance, not evidence that a
 * producer's claim follows from them. This module has no runtime dependencies
 * so importing its types does not pull the resolver into a reader's project. */
import type { Span } from "./span.mts";

export type ModuleEdge = {
  span: Span;
  specifier: string;
  kind: "import" | "reexport";
  imported: string;
  local: string;
  typeOnly: boolean;
};
export type DeclarationIdentity = {
  module: string;
  name: string;
  span: Span;
  capability: "type" | "value" | "both";
};
export type MappingStep = {
  virtual: string;
  canonical: string;
  source: string;
  sha256: string;
};
export type RouteStep = { module: string; sha256: string };
export type ResolvedImport = {
  binding: ModuleEdge;
  declaration: DeclarationIdentity;
  available: DeclarationIdentity["capability"];
  route: RouteStep[];
  mappings: MappingStep[];
};
export type Reference = {
  name: string;
  span: Span;
  arguments: Span[];
  target: DeclarationIdentity;
  route: RouteStep[];
  mappings: MappingStep[];
};
/** A source type equation before translation to the positive graph. */
export type TypeTerm =
  | { k: "atom"; name: "null" | "undefined" | "boolean" | "number" | "string" | "unknown" | "never" | "void"; span: Span }
  | { k: "literal"; name: "true" | "false" | "string" | "number"; text: string; span: Span }
  | { k: "union" | "intersection"; parts: TypeTerm[]; span: Span }
  | { k: "array"; readonly: boolean; element: TypeTerm; span: Span }
  | { k: "object"; fields: { name: string; optional: boolean; readonly: boolean; type: TypeTerm; span: Span }[];
      stringIndex: { readonly: boolean; value: TypeTerm; span: Span } | null; span: Span }
  | { k: "function"; receiver: TypeTerm | null; params: TypeTerm[];
      result: TypeTerm; span: Span }
  /** The containing declaration is the implicit receiver of a method signature. */
  | { k: "self"; span: Span }
  | { k: "parameter"; index: number; span: Span }
  | { k: "reference"; reference: Reference; args: TypeTerm[]; span: Span };
export type TypeDefinition = {
  declaration: DeclarationIdentity;
  sha256: string;
  parameters: { name: string; span: Span; bound: TypeTerm | null }[];
  body: Span;
  expression: TypeTerm;
  references: Reference[];
};
export type TypeClosure = { root: ResolvedImport; definitions: TypeDefinition[] };
/** The complete, self-contained source provenance for one client's imports.
 * Source and mapping bytes are each stored once even when several roots share
 * a reexport route or a mutually recursive definition. */
export type ImportDocument = {
  roots: ResolvedImport[];
  definitions: TypeDefinition[];
  sources: { module: string; sha256: string; text: string }[];
  mappings: { source: string; sha256: string; text: string }[];
};
