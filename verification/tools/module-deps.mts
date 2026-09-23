/** Source module edges, before any type or value from an import is trusted.
 * Parsing records source spellings and type erasure. Resolution must later
 * attach a module identity and exact exported declaration to each edge.
 */
import * as ts from "typescript/unstable/ast";
import type { SourceFile } from "typescript/unstable/ast";
import type { Span } from "./span.mts";

export type ModuleEdge = {
  span: Span;
  specifier: string;
  kind: "import" | "reexport";
  imported: string;
  local: string;
  typeOnly: boolean;
};

/** Preserve each binding separately. `*` marks a namespace or star reexport;
 * an empty imported name is a side-effect-only import. This is an inventory,
 * never evidence that the imported contract is valid or even resolved. */
export function moduleEdges(file: SourceFile): ModuleEdge[] {
  const edges: ModuleEdge[] = [];
  const add = (
    statement: { getStart(file: SourceFile): number; end: number },
    specifier: string,
    kind: ModuleEdge["kind"],
    imported: string,
    local: string,
    typeOnly: boolean,
  ) => edges.push({
    span: [statement.getStart(file), statement.end],
    specifier, kind, imported, local, typeOnly,
  });
  for (const statement of file.statements) {
    if (ts.isImportDeclaration(statement)) {
      if (!ts.isStringLiteral(statement.moduleSpecifier))
        throw Error("module import needs a literal specifier");
      const source = statement.moduleSpecifier.text;
      const clause = statement.importClause;
      if (!clause) {
        add(statement, source, "import", "", "", false);
        continue;
      }
      // The unstable AST exposes this runtime field but omits it from the
      // ImportClause interface. Narrow it before reading it.
      const clauseTypeOnly = "isTypeOnly" in clause && clause.isTypeOnly === true;
      if (clause.name)
        add(statement, source, "import", "default", clause.name.text, clauseTypeOnly);
      const names = clause.namedBindings;
      if (!names) continue;
      if (ts.isNamespaceImport(names))
        add(statement, source, "import", "*", names.name.text, clauseTypeOnly);
      else if (ts.isNamedImports(names))
        for (const name of names.elements)
          add(statement, source, "import", name.propertyName?.text ?? name.name.text,
            name.name.text, clauseTypeOnly || name.isTypeOnly);
    } else if (ts.isExportDeclaration(statement) && statement.moduleSpecifier) {
      if (!ts.isStringLiteral(statement.moduleSpecifier))
        throw Error("module reexport needs a literal specifier");
      const source = statement.moduleSpecifier.text;
      const names = statement.exportClause;
      if (!names)
        add(statement, source, "reexport", "*", "*", statement.isTypeOnly);
      else if (ts.isNamespaceExport(names))
        add(statement, source, "reexport", "*", names.name.text, statement.isTypeOnly);
      else if (ts.isNamedExports(names))
        for (const name of names.elements)
          add(statement, source, "reexport", name.propertyName?.text ?? name.name.text,
            name.name.text, statement.isTypeOnly || name.isTypeOnly);
    }
  }
  return edges;
}
