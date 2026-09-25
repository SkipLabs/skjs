/** Types TypeScript computes from other types: `typeof x`, `keyof T`, `T[K]`
 * and template literal types (DESIGN.md, "Computed types"). Their meaning is
 * the type TypeScript computes, which the checker gives; this module states it
 * as the equivalent type term the fragment already has, or refuses it with
 * the reason no such term exists. Nothing here is a second reading of type
 * syntax: a type the result names is read by `type-term.mts`, where it is
 * declared. */
import { TypeFlags, type Checker, type Type } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { Node, TypeNode } from "typescript/unstable/ast";
import type { Span } from "./span.mts";
import type { TypeTerm } from "./declaration-types.mts";
import { computedForm, optionalTerm } from "./type-term.mts";

/** What the evaluator reads with: the project's checker, and the reader of a
 * declaration's own annotation, in that declaration's scope, with the binders
 * of the functions enclosing it (`binders`), or of the value a name denotes, as
 * an import of it is read. */
export type ComputedContext = {
  checker: Checker;
  annotation(node: TypeNode, at: Node, binders: string[]): TypeTerm;
  /** The type of the value `declarations` bind, read as an imported one's
   * is, with its binders (a generic value has some). */
  value(declarations: readonly Node[], what: string): { typeParams: readonly unknown[]; type: TypeTerm };
};

/** The number's decimal spelling, as a literal type's text is written. */
function numberText(value: number): string | null {
  return Number.isFinite(value) ? String(value) : null;
}

/** A bigint literal type's value, which the checker sends as its decimal
 * spelling, a bigint, or a sign and digits. */
function bigintValue(value: unknown): string | null {
  if (typeof value === "bigint" || typeof value === "string") return String(value);
  if (value && typeof value === "object" && "base10Value" in value && typeof value.base10Value === "string")
    return ("negative" in value && value.negative === true ? "-" : "") + value.base10Value;
  return null;
}

/** `type` as a union of the fragment's primitive families and literals, when
 * it is exactly one: each part a literal (string, number, bigint, Boolean), a
 * primitive family, `null`, `undefined`, `void`, `unknown` or `never`. An enum
 * literal, a unique symbol, an object, a type parameter or a string pattern
 * is not one, and the answer is null. */
export function literalUnion(type: Type, span: Span): TypeTerm | null {
  const parts = type.isUnionType() ? type.getTypes() : [type];
  const terms: TypeTerm[] = [];
  const atom = (name: Extract<TypeTerm, { k: "atom" }>["name"]): TypeTerm => ({ k: "atom", name, span });
  for (const part of parts) {
    const f = part.flags;
    if (f & TypeFlags.EnumLiteral) return null;
    if (part.isStringLiteralType()) terms.push({ k: "literal", name: "string", text: part.value, span });
    else if (part.isNumberLiteralType()) {
      const text = numberText(part.value);
      if (text === null) return null;
      terms.push({ k: "literal", name: "number", text, span });
    } else if (part.isBigIntLiteralType()) {
      const text = bigintValue(part.value);
      if (text === null) return null;
      terms.push({ k: "literal", name: "bigint", text, span });
    } else if (part.isBooleanLiteralType())
      terms.push(part.value
        ? { k: "literal", name: "true", text: "true", span }
        : { k: "literal", name: "false", text: "false", span });
    else if (f & TypeFlags.String) terms.push(atom("string"));
    else if (f & TypeFlags.Number) terms.push(atom("number"));
    else if (f & TypeFlags.BigInt) terms.push(atom("bigint"));
    else if (f & TypeFlags.ESSymbol) terms.push(atom("symbol"));
    else if (f & TypeFlags.Null) terms.push(atom("null"));
    else if (f & TypeFlags.Undefined) terms.push(atom("undefined"));
    else if (f & TypeFlags.Void) terms.push(atom("void"));
    else if (f & TypeFlags.Unknown) terms.push(atom("unknown"));
    else if (f & TypeFlags.Never) terms.push(atom("never"));
    else return null;
  }
  const [only] = terms;
  if (!only) return atom("never");
  return terms.length === 1 ? only : { k: "union", parts: terms, span };
}

/** The names of the type parameters of every declaration enclosing `node`:
 * the binders an annotation there reads by spelling. */
export function enclosingBinders(node: Node): string[] {
  const names: string[] = [];
  for (let at: Node | undefined = node.parent; at; at = at.parent) {
    const parameters = (at as { typeParameters?: readonly ts.TypeParameterDeclaration[] }).typeParameters;
    for (const p of parameters ?? []) names.push(p.name.text);
  }
  return names;
}

const describe = (checker: Checker, type: Type): string => checker.typeToString(type);

/** The type term of a computed type `node` (`computedForm`), located at
 * `span`; `read` reads an operand in the scope `node` is written in. */
export function computedType(context: ComputedContext, node: TypeNode, span: Span,
    read: (node: TypeNode) => TypeTerm): TypeTerm {
  const { checker } = context;
  const form = computedForm(node) ?? "a computed type";
  const type = checker.getTypeFromTypeNode(node);
  if (!type || type.isErrorType()) throw Error(`TypeScript computes no type for this ${form}: it is not valid TypeScript`);
  const literals = literalUnion(type, span);
  if (literals) return literals;
  const computed = describe(checker, type);
  if (ts.isTypeQueryNode(node)) return typeQuery(context, node, type, span);
  if (ts.isIndexedAccessTypeNode(node)) return indexedAccess(context, node, type, span, read);
  if (ts.isTemplateLiteralTypeNode(node) || type.isTemplateLiteralType() || type.isStringMappingType())
    throw Error(`the template literal type ${computed} is a string pattern: it holds infinitely many ` +
      "strings, not a union of literals, and the fragment has no string-pattern type");
  if (generic(type))
    throw Error(`${form} over a type parameter, ${computed}, is computed only at an instance`);
  throw Error(`${form} is ${computed}, ${inexpressible(checker, type)}`);
}

/** Why `type` is not a union of literals and primitives: its first part that
 * is not one. */
function inexpressible(checker: Checker, type: Type): string {
  const parts = type.isUnionType() ? type.getTypes() : [type];
  const part = parts.find(p => literalUnion(p, [0, 0]) === null) ?? type;
  const what = part.flags & TypeFlags.UniqueESSymbol ? "a unique symbol, which no type of the fragment names"
    : part.flags & TypeFlags.EnumLiteral ? "an enum member, outside the fragment"
    : "not a literal or a primitive";
  return `whose part ${checker.typeToString(part)} is ${what}`;
}

/** Whether `type` still names a type parameter: TypeScript defers it. */
function generic(type: Type): boolean {
  if (type.isTypeParameter() || type.isIndexType() || type.isIndexedAccessType() || type.isConditionalType() ||
      type.isSubstitutionType()) return true;
  return type.isUnionType() && type.getTypes().some(generic);
}

/** The declaration of the value or member a name denotes, with the type node
 * it is annotated with, if it has one. */
type Declared = { node: Node; annotation: TypeNode | undefined; optional: boolean };

function declared(node: Node): Declared {
  const typed = node as { type?: TypeNode; questionToken?: Node; postfixToken?: Node };
  const annotation = ts.isVariableDeclaration(node) || ts.isParameterDeclaration(node) ||
    ts.isPropertySignatureDeclaration(node) || ts.isPropertyDeclaration(node) ? typed.type : undefined;
  const optional = !!typed.questionToken || typed.postfixToken?.kind === ts.SyntaxKind.QuestionToken;
  return { node, annotation, optional };
}

/** `typeof x` and `typeof x.y`: the value's type as its declaration states
 * it. A function or class is read as an imported one is; a binding or member
 * by its annotation, which must denote exactly the type TypeScript computes
 * for the query (not a narrowed one, nor an instance of a generic member). A
 * binding TypeScript types by inference has no annotation to read. */
function typeQuery(context: ComputedContext, node: ts.TypeQueryNode, type: Type, span: Span): TypeTerm {
  const { checker } = context;
  const computed = describe(checker, type);
  if (node.typeArguments?.length) throw Error("typeof with type arguments is an instantiation, outside the fragment");
  const name = node.exprName;
  const last = ts.isIdentifier(name) ? name : name.right;
  const what = `typeof ${name.getText(node.getSourceFile())}`;
  const symbol = checker.getSymbolAtLocation(last);
  // A name that is also an interface or type alias denotes its value here.
  const nodes = (symbol?.declarations ?? []).map(d => d.resolve()).filter((d): d is Node =>
    !!d && !ts.isInterfaceDeclaration(d) && !ts.isTypeAliasDeclaration(d));
  const [first] = nodes;
  if (!first) throw Error(`${what} names nothing TypeScript declares`);
  // An annotation's `typeof E` is the enum's object type, which the parser
  // reads (DESIGN.md, "Enums"); the declaration reader does not read enums.
  if (ts.isEnumDeclaration(first))
    throw Error(`${what} is an enum's object type, which only an annotation of the enum's module states`);
  if (nodes.every(n => ts.isFunctionDeclaration(n)) || (nodes.length === 1 && ts.isClassDeclaration(first))) {
    if (ts.isClassDeclaration(first) && first.members.some(m =>
        (m as { modifiers?: readonly Node[] }).modifiers?.some(k => k.kind === ts.SyntaxKind.StaticKeyword)))
      throw Error(`${what} is a class with static members: its statics are bindings of their own, not ` +
        "members of the class value's type");
    const value = context.value(nodes, what);
    if (value.typeParams.length) throw Error(`${what} is generic, ${computed}: a generic value type is outside the fragment`);
    return value.type;
  }
  if (nodes.length !== 1) throw Error(`${what} has ${nodes.length} declarations`);
  const { annotation, optional } = declared(first);
  if (!annotation) throw Error(`${what} is ${computed}, the type TypeScript infers for a binding without an ` +
    "annotation, and not a union of literals and primitives");
  const stated = checker.getTypeFromTypeNode(annotation);
  const same = stated?.id === type.id;
  // `x?: T` is `T | undefined` where it is read.
  const orUndefined = optional && !same && stated !== undefined &&
    checker.getNonNullableType(type)?.id === checker.getNonNullableType(stated)?.id &&
    type.isUnionType() && type.getTypes().some(t => (t.flags & TypeFlags.Undefined) !== 0);
  if (!same && !orUndefined)
    throw Error(`${what} is ${computed}, not the type its declaration states (a narrowed binding, or a ` +
      "member of a generic type's instance)");
  const term = context.annotation(annotation, first, enclosingBinders(first));
  return orUndefined ? optionalTerm(term, span) : term;
}

/** `T[K]`: the member, element or position of `T` at each key `K` denotes,
 * read from `T` as this scope reads it; a member of a named type is its
 * declaration's annotation, which must denote exactly the type TypeScript
 * computes. */
function indexedAccess(context: ComputedContext, node: ts.IndexedAccessTypeNode, type: Type, span: Span,
    read: (node: TypeNode) => TypeTerm): TypeTerm {
  const { checker } = context;
  const computed = describe(checker, type);
  const keyType = checker.getTypeFromTypeNode(node.indexType);
  const keys = keyType ? literalUnion(keyType, span) : null;
  if (!keys) throw Error(`the indexed access ${computed} has a key that is not a union of literals and primitives`);
  const keyList = keys.k === "union" ? keys.parts : [keys];
  const union = (parts: TypeTerm[]): TypeTerm => {
    const [only] = parts;
    return parts.length === 1 && only ? only : { k: "union", parts, span };
  };
  const project = (object: TypeTerm): TypeTerm => {
    switch (object.k) {
      case "union": return union(object.parts.map(project));
      case "array":
        if (keyList.every(k => k.k === "atom" && k.name === "number")) return object.element;
        break;
      case "tuple": {
        const at = (key: TypeTerm): TypeTerm[] => {
          if (key.k === "atom" && key.name === "number")
            return [...object.required, ...object.optional.map(t => optionalTerm(t, span)),
              ...(object.rest ? [object.rest] : [])];
          if (key.k !== "literal" || key.name !== "number" || !/^[0-9]+$/.test(key.text)) return [];
          const i = Number(key.text);
          const position = object.required[i] ?? object.optional[i - object.required.length];
          if (position) return [i < object.required.length ? position : optionalTerm(position, span)];
          return object.rest ? [object.rest] : [];
        };
        const perKey = keyList.map(at);
        if (perKey.every(p => p.length)) return union(perKey.flat());
        break;
      }
      case "object": {
        const parts = keyList.map(key => {
          if (key.k !== "literal" || key.name !== "string") return null;
          const field = object.fields.find(f => f.name === key.text);
          return field ? (field.optional ? optionalTerm(field.type, span) : field.type) : null;
        });
        if (parts.every((p): p is TypeTerm => p !== null)) return union(parts);
        break;
      }
      case "parameter": case "binder":
        throw Error(`the indexed access ${computed} over a type parameter is computed only at an instance`);
      case "reference": {
        // A type alias without parameters is its equation, read where it is
        // declared.
        const alias = aliasOf(node.objectType);
        if (alias && object.args.length === 0)
          return project(context.annotation(alias.type, alias, []));
        return member();
      }
    }
    throw Error(`the indexed access ${computed} has no member, element or position at its key`);
  };
  // The type alias without parameters a type reference names.
  const aliasOf = (reference: TypeNode): ts.TypeAliasDeclaration | null => {
    if (!ts.isTypeReferenceNode(reference) || !ts.isIdentifier(reference.typeName)) return null;
    const nodes = (checker.getSymbolAtLocation(reference.typeName)?.declarations ?? []).map(d => d.resolve());
    const [only] = nodes;
    return nodes.length === 1 && only && ts.isTypeAliasDeclaration(only) && !only.typeParameters?.length
      ? only : null;
  };
  // A member of a named type: its declaration's annotation, when that is
  // exactly what TypeScript computes and names no type parameter.
  const member = (): TypeTerm => {
    const objectType = checker.getTypeFromTypeNode(node.objectType);
    const [key] = keyList;
    if (!objectType || keyList.length !== 1 || key?.k !== "literal" || key.name !== "string")
      throw Error(`the indexed access ${computed} into a named type needs one string key`);
    const property = checker.getPropertyOfType(objectType, key.text);
    const nodes = (property?.declarations ?? []).map(d => d.resolve()).filter((d): d is Node => !!d);
    const [only] = nodes;
    const { annotation, optional } = only && nodes.length === 1 ? declared(only) : { annotation: undefined, optional: false };
    if (!only || !annotation || optional || enclosingBinders(only).length ||
        checker.getTypeFromTypeNode(annotation)?.id !== type.id)
      throw Error(`the indexed access ${computed} is not a member a declaration states as it is`);
    return context.annotation(annotation, only, []);
  };
  try {
    return project(read(node.objectType));
  } catch (error) {
    // TypeScript defers an access it cannot compute before an instance.
    if (generic(type))
      throw Error(`the indexed access ${computed} over a type parameter is computed only at an instance`);
    throw error;
  }
}
