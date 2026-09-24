/** The one reading of TypeScript type syntax as a source type term. Function
 * annotations and declaration bodies share it: what differs between them is
 * where a name resolves, which the caller's scope decides, and which record
 * forms an annotation may state. */
import * as ts from "typescript/unstable/ast";
import type { Node, SourceFile, TypeElement, TypeNode, TypeReferenceNode } from "typescript/unstable/ast";
import type { Span } from "./span.mts";
import type { TypeTerm } from "./declaration-types.mts";

// Numeric literals in the fragment are plain decimals; every other spelling
// (hex, binary, octal, separators, bigint) is outside it.
const DECIMAL = /^[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?$/;

export const REST_CONTRACT =
  "a rest parameter needs a tuple of required positions or a mutable array";

export type TermScope = {
  source: SourceFile;
  fail(node: Node | null, message: string): never;
  /** A type reference: a binder in scope or a declaration. */
  named(node: TypeReferenceNode, span: Span, read: (node: TypeNode) => TypeTerm): TypeTerm;
  /** An annotation states records as the source fragment always has: named,
   * required fields and at most one readonly string index. A declaration body
   * states what its equation says, and Lean decides what lowers. */
  annotation: boolean;
};

type FunctionTerm = Extract<TypeTerm, { k: "function" }>;

const spanOf = (scope: TermScope, node: Node): Span => [node.getStart(scope.source), node.end];

const unwrap = (node: TypeNode): TypeNode => {
  while (ts.isParenthesizedTypeNode(node)) node = node.type;
  return node;
};

/** `x?: T` is `T | undefined` where the parameter is read: `undefined` is the
 * value bound when a call omits that position. */
export function optionalTerm(type: TypeTerm, span: Span): TypeTerm {
  return { k: "union", parts: [type, { k: "atom", name: "undefined", span }], span };
}

/** The rest parameter's contract as positions of the signature: a tuple of
 * required positions is a fixed number of further arguments, a mutable array
 * any number of them. Anything else has no reading as a signature. */
export function restPositions(type: TypeTerm): { positions: TypeTerm[] } | { element: TypeTerm } | null {
  if (type.k === "array" && !type.readonly) return { element: type.element };
  if (type.k === "tuple" && !type.readonly && !type.optional.length && type.rest === null)
    return { positions: type.required };
  return null;
}

export function typeTerm(scope: TermScope, node: TypeNode | undefined, at: Node | null = null): TypeTerm {
  if (!node) return scope.fail(at, "missing type annotation");
  const span = spanOf(scope, node);
  const atom = (name: Extract<TypeTerm, { k: "atom" }>["name"]): TypeTerm => ({ k: "atom", name, span });
  switch (node.kind) {
    case ts.SyntaxKind.NullKeyword: return atom("null");
    case ts.SyntaxKind.UndefinedKeyword: return atom("undefined");
    case ts.SyntaxKind.BooleanKeyword: return atom("boolean");
    case ts.SyntaxKind.NumberKeyword: return atom("number");
    case ts.SyntaxKind.StringKeyword: return atom("string");
    case ts.SyntaxKind.UnknownKeyword: return atom("unknown");
    case ts.SyntaxKind.NeverKeyword: return atom("never");
    case ts.SyntaxKind.VoidKeyword: return atom("void");
  }
  if (ts.isParenthesizedTypeNode(node)) return typeTerm(scope, node.type);
  if (ts.isUnionTypeNode(node))
    return { k: "union", parts: node.types.map(t => typeTerm(scope, t)), span };
  if (ts.isIntersectionTypeNode(node)) return intersection(scope, node, span);
  if (ts.isArrayTypeNode(node))
    return { k: "array", readonly: false, element: typeTerm(scope, node.elementType), span };
  if (ts.isTupleTypeNode(node)) return tuple(scope, node, false, span);
  if (ts.isTypeOperatorNode(node) && node.operator === ts.SyntaxKind.ReadonlyKeyword) {
    // `readonly T[]` and `readonly [..]`: the same contract as a view.
    const inner = unwrap(node.type);
    if (ts.isArrayTypeNode(inner))
      return { k: "array", readonly: true, element: typeTerm(scope, inner.elementType), span };
    if (ts.isTupleTypeNode(inner)) return tuple(scope, inner, true, span);
    return scope.fail(node, "readonly applies to an array or tuple type");
  }
  if (ts.isLiteralTypeNode(node)) {
    // `literal` is declared as a bare Node, so it too is read by predicate.
    const literal = node.literal;
    if (literal.kind === ts.SyntaxKind.NullKeyword) return atom("null");
    if (literal.kind === ts.SyntaxKind.TrueKeyword || literal.kind === ts.SyntaxKind.FalseKeyword)
      return { k: "literal", name: literal.kind === ts.SyntaxKind.TrueKeyword ? "true" : "false",
        text: literal.kind === ts.SyntaxKind.TrueKeyword ? "true" : "false", span };
    // The literal's value: a string without its quotes, a number as its
    // decimal spelling.
    if (ts.isStringLiteral(literal)) return { k: "literal", name: "string", text: literal.text, span };
    if (ts.isNumericLiteral(literal)) {
      if (!DECIMAL.test(literal.text)) scope.fail(literal, "non-decimal numeric literal type");
      return { k: "literal", name: "number", text: literal.text, span };
    }
    return scope.fail(literal, "literal type outside the fragment");
  }
  if (ts.isTypeLiteralNode(node)) return members(scope, node.members, node, span, false);
  if (ts.isFunctionTypeNode(node)) {
    if (node.typeParameters?.length) scope.fail(node, "generic function types are outside the fragment");
    return signature(scope, node.parameters, node.type, node, span);
  }
  if (ts.isTypeReferenceNode(node)) {
    if (node.typeName.kind !== ts.SyntaxKind.Identifier)
      return scope.fail(node, "type reference outside the fragment");
    return scope.named(node, span, part => typeTerm(scope, part));
  }
  return scope.fail(node, `type outside the fragment (${ts.SyntaxKind[node.kind]})`);
}

function tuple(scope: TermScope, node: ts.TupleTypeNode, readonly: boolean, span: Span): TypeTerm {
  const required: TypeTerm[] = [], optional: TypeTerm[] = [];
  let rest: TypeTerm | null = null;
  for (const element of node.elements) {
    if (ts.isNamedTupleMember(element)) scope.fail(element, "named tuple members are outside the fragment");
    if (ts.isRestTypeNode(element)) {
      if (rest !== null || !ts.isArrayTypeNode(element.type))
        scope.fail(element, "a tuple rest must be one final array");
      rest = typeTerm(scope, element.type.elementType);
    } else if (ts.isOptionalTypeNode(element)) {
      if (rest !== null) scope.fail(element, "an optional position cannot follow the rest");
      optional.push(typeTerm(scope, element.type));
    } else {
      if (optional.length || rest !== null)
        scope.fail(element, "a required position cannot follow an optional one");
      required.push(typeTerm(scope, element));
    }
  }
  return { k: "tuple", readonly, required, optional, rest, span };
}

/** Union is a list of parts; conjunction is written only where the clause
 * language has one: a location under several contracts, a function with
 * several signatures. An annotation says so in its syntax. A declaration's
 * operands are met in Lean, which refuses a meet it cannot represent. */
function intersection(scope: TermScope, node: ts.IntersectionTypeNode, span: Span): TypeTerm {
  const operands: TypeNode[] = [];
  const flatten = (t: TypeNode): void => {
    t = unwrap(t);
    if (ts.isIntersectionTypeNode(t)) t.types.forEach(flatten);
    else operands.push(t);
  };
  flatten(node);
  const parts = operands.map(operand => typeTerm(scope, operand));
  if (scope.annotation) {
    const shape = (part: TypeTerm, operand: TypeNode): string => {
      switch (part.k) {
        case "object": return "record";
        case "function": return "function";
        case "reference": return "alias";
        case "binder": return "param";
        case "array": case "tuple": return "array";
        case "literal": return part.name === "true" || part.name === "false" ? "booleanlit"
          : part.name === "number" ? "numberlit" : "stringlit";
        case "atom":
          if (part.name !== "unknown" && part.name !== "never") return part.name;
      }
      return scope.fail(operand, "an intersection operand must be a single type");
    };
    const shapes = parts.map((part, i) => shape(part, operands[i] ?? node));
    const head = shapes[0];
    if (shapes.some(s => s !== head)) scope.fail(node, "intersection operands must have the same shape");
    if (head !== "record" && head !== "function")
      scope.fail(node, `intersection of ${head} types is outside the fragment`);
  }
  return { k: "intersection", parts, span };
}

/** A signature's parameters: a leading `this: T` is the receiver a call must
 * pass, and without one the signature accepts any receiver. */
export function signature(scope: TermScope, parameters: readonly ts.ParameterDeclaration[],
    result: TypeNode | undefined, at: Node, span: Span,
    // A declared function's defaulted parameter may be omitted: `undefined`
    // is what a short call binds there. Function types have no defaults.
    declared = false): FunctionTerm {
  const head = parameters[0];
  const stated = !!head && ts.isIdentifier(head.name) && head.name.text === "this";
  if (stated && (!head.type || head.questionToken || head.dotDotDotToken || head.initializer))
    scope.fail(head, "a receiver needs a required type annotation");
  const receiver = stated ? typeTerm(scope, head.type, head) : null;
  const ordinary = stated ? parameters.slice(1) : [...parameters];
  const optional = (p: ts.ParameterDeclaration) => !!p.questionToken || (declared && !!p.initializer);
  const firstOptional = ordinary.findIndex(optional);
  const params: TypeTerm[] = [];
  let rest: TypeTerm | null = null;
  for (const [index, p] of ordinary.entries()) {
    if (!ts.isIdentifier(p.name) || p.name.text === "this" || (p.initializer && !declared))
      scope.fail(p, "expected an ordinary parameter");
    if (p.dotDotDotToken) {
      if (index !== ordinary.length - 1) scope.fail(p, "a rest parameter must be the last one");
      // A tuple rest is a fixed number of further positions, which is how
      // TypeScript itself reads it, so the signature carries them. An array
      // rest is any number of them: the signature says what each one is.
      const contract = restPositions(typeTerm(scope, p.type, p));
      if (!contract) scope.fail(p, REST_CONTRACT);
      if ("positions" in contract) params.push(...contract.positions);
      else rest = contract.element;
    } else {
      if (!optional(p) && firstOptional >= 0 && index > firstOptional)
        scope.fail(p, "a required parameter cannot follow an optional one");
      const type = typeTerm(scope, p.type, p);
      params.push(optional(p) ? optionalTerm(type, spanOf(scope, p)) : type);
    }
  }
  return { k: "function", receiver, params, rest, result: typeTerm(scope, result, at), span };
}

/** A record, or an interface body when `methods` is set: its method
 * signatures read the containing declaration as their receiver. */
export function members(scope: TermScope, list: readonly TypeElement[], at: Node, span: Span,
    methods: boolean): TypeTerm {
  const fields: Extract<TypeTerm, { k: "object" }>["fields"] = [];
  let stringIndex: Extract<TypeTerm, { k: "object" }>["stringIndex"] = null;
  const calls: FunctionTerm[] = [];
  const names = new Set<string>();
  const readonlyOnly = (modifiers: readonly Node[] | undefined) =>
    !modifiers?.some(m => m.kind !== ts.SyntaxKind.ReadonlyKeyword);
  const isReadonly = (modifiers: readonly Node[] | undefined) =>
    modifiers?.some(m => m.kind === ts.SyntaxKind.ReadonlyKeyword) === true;
  const named = (member: TypeElement & { name?: Node }, message: string): string => {
    const name = member.name;
    if (!name || !(ts.isIdentifier(name) || (!scope.annotation && ts.isStringLiteral(name))))
      return scope.fail(member, message);
    const text = name.text;
    if (names.has(text)) scope.fail(member, "duplicate field name in a record");
    names.add(text);
    return text;
  };
  if (scope.annotation && !list.length) scope.fail(at, "a record with no field has no location");
  // An annotation's index signature is checked first, then its fields, and
  // only then is any other member refused.
  const ordered = scope.annotation
    ? [...list.filter(ts.isIndexSignatureDeclaration), ...list.filter(ts.isPropertySignatureDeclaration),
       ...list.filter(m => !ts.isIndexSignatureDeclaration(m) && !ts.isPropertySignatureDeclaration(m))]
    : list;
  if (scope.annotation && list.filter(ts.isIndexSignatureDeclaration).length > 1)
    scope.fail(at, "multiple string index signatures are outside the fragment");
  for (const member of ordered) {
    const memberSpan = spanOf(scope, member);
    if (ts.isPropertySignatureDeclaration(member)) {
      // A `readonly` member is a read capability: its write contract is
      // `never`, and nothing else about the field changes. A member's `?` is
      // its postfix token.
      const optional = member.postfixToken?.kind === ts.SyntaxKind.QuestionToken;
      const message = scope.annotation ? "expected a required mutable field" : "unsupported property signature";
      if (!readonlyOnly(member.modifiers) || (scope.annotation && member.postfixToken) || !member.type)
        scope.fail(member, message);
      const name = named(member, message);
      fields.push({ name, optional, readonly: isReadonly(member.modifiers),
        type: typeTerm(scope, member.type, member), span: memberSpan });
    } else if (ts.isIndexSignatureDeclaration(member)) {
      const parameter = member.parameters[0];
      const message = scope.annotation ? "expected a readonly string index signature" : "unsupported index signature";
      if (stringIndex) scope.fail(member, message);
      if (member.parameters.length !== 1 || parameter?.type?.kind !== ts.SyntaxKind.StringKeyword ||
          !member.type || !readonlyOnly(member.modifiers) ||
          (scope.annotation && !isReadonly(member.modifiers)))
        scope.fail(member, message);
      stringIndex = { readonly: isReadonly(member.modifiers),
        value: typeTerm(scope, member.type, member), span: memberSpan };
    } else if (scope.annotation) {
      scope.fail(at, "unsupported member in a record type");
    } else if (ts.isMethodSignatureDeclaration(member) && methods && member.typeParameters?.length &&
        !member.postfixToken && !member.modifiers?.length) {
      // A generic method is read as an opaque readonly member: a program may
      // read it, never call it, and any value is one. Calling it needs its
      // instances, which are not yet derived for members.
      const name = named(member, "unsupported method signature");
      fields.push({ name, optional: false, readonly: true,
        type: { k: "atom", name: "unknown", span: memberSpan }, span: memberSpan });
    } else if (ts.isMethodSignatureDeclaration(member)) {
      if (!methods || !member.type || member.postfixToken?.kind === ts.SyntaxKind.QuestionToken ||
          member.typeParameters?.length || member.modifiers?.length)
        scope.fail(member, "unsupported method signature");
      const name = named(member, "unsupported method signature");
      const method = signature(scope, member.parameters, member.type, member, memberSpan);
      if (method.receiver) scope.fail(member, "unsupported method signature");
      fields.push({ name, optional: false, readonly: false,
        type: { ...method, receiver: { k: "self", span: memberSpan } }, span: memberSpan });
    } else if (ts.isCallSignatureDeclaration(member)) {
      if (member.typeParameters?.length || !member.type)
        scope.fail(member, "generic or incomplete call signature");
      calls.push(signature(scope, member.parameters, member.type, member, memberSpan));
    } else scope.fail(member, "unsupported object member");
  }
  return { k: "object", fields, stringIndex, calls, span };
}

/** A class declaration's instance type: its fields at their annotations and
 * its methods as readonly fields whose receiver is the instance. An instance
 * reaches a method through the prototype; within the fragment nothing tells a
 * prototype member from an own one, and no write reaches either, so the
 * readonly field is exact. Construction is the class value's concern. */
export function classInstance(scope: TermScope, node: ts.ClassDeclaration, span: Span): TypeTerm {
  const fields: Extract<TypeTerm, { k: "object" }>["fields"] = [];
  const names = new Set<string>();
  const named = (member: ts.ClassElement & { name?: Node }): string => {
    const name = member.name;
    if (!name || !ts.isIdentifier(name)) return scope.fail(member, "a class member needs a plain name");
    if (names.has(name.text)) scope.fail(member, "duplicate class member");
    names.add(name.text);
    return name.text;
  };
  const only = (member: ts.ClassElement, allowed: ts.SyntaxKind[]) => {
    const modifiers = (member as { modifiers?: readonly Node[] }).modifiers;
    if (modifiers?.some(m => !allowed.includes(m.kind)))
      scope.fail(member, "a class member modifier outside the fragment");
  };
  for (const member of node.members) {
    const memberSpan = spanOf(scope, member);
    if (ts.isPropertyDeclaration(member)) {
      only(member, [ts.SyntaxKind.ReadonlyKeyword]);
      if (member.postfixToken)
        scope.fail(member, "an optional or definitely-assigned class field is outside the fragment");
      const name = named(member);
      fields.push({ name, optional: false,
        readonly: member.modifiers?.some(m => m.kind === ts.SyntaxKind.ReadonlyKeyword) === true,
        type: typeTerm(scope, member.type, member), span: memberSpan });
    } else if (ts.isMethodDeclaration(member)) {
      only(member, []);
      if (member.postfixToken || member.asteriskToken || member.typeParameters?.length)
        scope.fail(member, "an optional, generator or generic method is outside the fragment");
      const name = named(member);
      const method = signature(scope, member.parameters, member.type, member, memberSpan);
      if (method.receiver) scope.fail(member, "a method receiver is its instance");
      fields.push({ name, optional: false, readonly: true,
        type: { ...method, receiver: { k: "self", span: memberSpan } }, span: memberSpan });
    } else if (ts.isConstructorDeclaration(member)) {
      // A parameter property is a field the constructor assigns from its
      // parameter. Its visibility is TypeScript's alone; `readonly` is the
      // field's.
      for (const p of member.parameters) {
        if (!p.modifiers?.length) continue;
        if (!ts.isIdentifier(p.name) || p.questionToken || p.dotDotDotToken || p.initializer)
          scope.fail(p, "a parameter property needs a plain required parameter");
        const name = p.name.text;
        if (names.has(name)) scope.fail(p, "duplicate class member");
        names.add(name);
        fields.push({ name, optional: false,
          readonly: p.modifiers.some(m => m.kind === ts.SyntaxKind.ReadonlyKeyword),
          type: typeTerm(scope, p.type, p), span: spanOf(scope, p) });
      }
    } else if (!ts.isSemicolonClassElement(member)) {
      scope.fail(member, "a class member outside the fragment");
    }
  }
  return { k: "object", fields, stringIndex: null, calls: [], span };
}
