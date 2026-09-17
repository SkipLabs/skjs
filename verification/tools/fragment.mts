/** The fragment: the subset of TypeScript this pipeline accepts, written as an
 * abstract syntax tree. Mirrors Fragment.lean, whose decoders read exactly these
 * shapes. They are structural on purpose: this is a wire format, and its field
 * names are the contract. The parser that produces a tree is fragment-parse.mts.
 */
import type { ClaimType, Atom } from "./claim.mts";
import type { Span } from "./span.mts";

export type Expr =
  | { k: "id"; pos: Span; name: string }
  | { k: "lit"; pos: Span; lit: Atom }
  | { k: "not" | "typeof"; pos: Span; e: Expr }
  /* An object literal: one named field per initializer, in source order. */
  | { k: "alloc"; pos: Span; fields: { name: string; e: Expr }[] }
  | { k: "read"; pos: Span; field: string; e: Expr }
  | { k: "bin"; pos: Span; op: string; l: Expr; r: Expr }
  | { k: "coalesce"; pos: Span; left: Expr; right: Expr }
  | { k: "write"; pos: Span; field: string; receiver: Expr; rhs: Expr }
  /* A nullish assignment also reads the target at namePos. */
  | { k: "nullishAssign"; pos: Span; name: string; namePos: Span; rhs: Expr }
  /* Assignment to a mutable local. An expression, because JavaScript's is:
     it yields the value written, which the calculus's write does not. */
  | { k: "assign"; pos: Span; name: string; namePos: Span; rhs: Expr }
  | { k: "withValue"; pos: Span; fn: Expr; initial: Expr; functionType: ClaimType; bagType: ClaimType }
  | { k: "functionTest"; pos: Span; equal: boolean; e: Expr }
  | { k: "apply"; pos: Span; callee: Expr; args: Expr[] }
  | { k: "callWithReceiver" | "bindWithReceiver"; pos: Span; callee: Expr; receiver: Expr; args: Expr[] }
  | { k: "conditional"; pos: Span; cond: Expr; then: Expr; else_: Expr }
  | {
      k: "lambda";
      pos: Span;
      params: { name: string; type: ClaimType }[];
      result: ClaimType;
      body: Expr;
    }
  /* A block-bodied closure, lowered to nested expressions: the calculus has no
     statements inside a closure, so the parser does the lowering the verifier
     would otherwise have to invent. */
  | { k: "doneBody"; pos: Span }
  | { k: "returnBody"; pos: Span; e: Expr }
  | { k: "seqBody"; pos: Span; init: Expr; body: Expr }
  | {
      k: "letBody";
      pos: Span;
      name: string;
      annot: ClaimType | null;
      init: Expr;
      body: Expr;
    }
  | {
      k: "ifBody";
      pos: Span;
      result: ClaimType;
      cond: Expr;
      then: Expr;
      else_: Expr;
    };

export type Stmt =
  | { k: "effect"; pos: Span; e: Expr }
  | { k: "return"; pos: Span; e: Expr }
  | { k: "break" | "continue"; pos: Span }
  | { k: "while"; pos: Span; cond: Expr; body: Stmt[] }
  | { k: "if"; pos: Span; cond: Expr; then: Stmt[]; else_: Stmt[] | null }
  | {
      k: "const";
      pos: Span;
      name: string;
      namePos: Span;
      annot: ClaimType | null;
      init: Expr;
    }
  /* A mutable local. `annot` is the storage contract every assignment is
     checked against. Absent, the producer supplies one and the adapter checks
     it; an initializer's type is what the binding happens to hold first, not
     what it may hold, so it is never taken for the contract. */
  | {
      k: "let";
      pos: Span;
      name: string;
      namePos: Span;
      annot: ClaimType | null;
      init: Expr;
    };

export interface TypeParamAst {
  name: string;
  bound: ClaimType | null;
}

export interface FunctionAst {
  name: string;
  namePos: Span;
  typeParams: TypeParamAst[];
  params: { name: string; pos: Span; type: ClaimType }[];
  retType: ClaimType;
  body: Stmt[];
}

export interface TypeAliasAst {
  name: string;
  typeParams: TypeParamAst[];
  body: ClaimType;
}

export interface Ast {
  file: string;
  sourceSha256: string;
  aliases: TypeAliasAst[];
  functions: FunctionAst[];
}
