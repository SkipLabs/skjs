/** The fragment: the subset of TypeScript this pipeline accepts, written as an
 * abstract syntax tree. Mirrors Fragment.lean, whose decoders read exactly these
 * shapes. They are structural on purpose: this is a wire format, and its field
 * names are the contract. The parser that produces a tree is fragment-parse.mts.
 */
import type { ClaimType, Atom } from "./claim.mts";
import type { Span } from "./span.mts";

export type ArithOp = "add" | "sub" | "mul" | "div";
export type Expr =
  | { k: "id"; pos: Span; name: string }
  | { k: "lit"; pos: Span; lit: Atom }
  | { k: "not" | "typeof"; pos: Span; e: Expr }
  /* `e as T`, `e satisfies T` or `e!`: the operand's value, unchanged. The
     annotation, when there is one, is what the operand must meet. */
  | {
      k: "cast";
      pos: Span;
      cast: "as" | "satisfies" | "nonNull";
      annot: ClaimType | null;
      e: Expr;
    }
  /* An object literal: one named field per initializer, in source order. */
  | { k: "alloc"; pos: Span; fields: { name: string; e: Expr }[] }
  | { k: "read"; pos: Span; field: string; e: Expr }
  /* `e[key]`: the receiver, then the key, then the read of the field the
     key's claimed type names, a string singleton. */
  | { k: "index"; pos: Span; e: Expr; key: Expr }
  /* An array literal: one element per initializer, in source order. */
  | { k: "arrayLit"; pos: Span; elems: Expr[] }
  /* `[a, b = d] = rhs`: the right side once, then each mutable local takes
     its position of the store, or its default when that read is undefined.
     The expression's value is the right side. */
  | { k: "arrayAssign"; pos: Span; targets: ArrayElemAst[]; rhs: Expr }
  | { k: "indexWrite"; pos: Span; receiver: Expr; key: Expr; rhs: Expr }
  | { k: "bin"; pos: Span; op: string; l: Expr; r: Expr }
  /* Arithmetic on two numbers: `l`, then `r`, then the double operation. */
  | { k: "arith"; pos: Span; op: ArithOp; l: Expr; r: Expr }
  /* `target op= rhs`, `target++` and the like: the target's parts are
     evaluated once, its current value read, the right side (1 for an
     increment) evaluated, the operation applied and the result written back.
     `post` selects the old value as the expression's value. */
  | {
      k: "update";
      pos: Span;
      op: ArithOp;
      target: Expr;
      rhs: Expr | null;
      post: boolean;
    }
  | { k: "coalesce"; pos: Span; left: Expr; right: Expr }
  | { k: "write"; pos: Span; field: string; receiver: Expr; rhs: Expr }
  /* `target ??= rhs`, `||=` or `&&=` on a field, an element or, for the
     Boolean forms, a name: the target's parts once, its value read, the test
     on that value, and the right side written only on the writing arm. */
  | {
      k: "logicalAssign";
      pos: Span;
      op: "nullish" | "or" | "and";
      target: Expr;
      rhs: Expr;
    }
  /* A nullish assignment also reads the target at namePos. */
  | { k: "nullishAssign"; pos: Span; name: string; namePos: Span; rhs: Expr }
  /* Assignment to a mutable local. An expression, because JavaScript's is:
     it yields the value written, which the calculus's write does not. */
  | { k: "assign"; pos: Span; name: string; namePos: Span; rhs: Expr }
  | {
      k: "withValue";
      pos: Span;
      fn: Expr;
      initial: Expr;
      functionType: ClaimType;
      bagType: ClaimType;
    }
  | { k: "functionTest"; pos: Span; equal: boolean; e: Expr }
  /* `spreads` are the indices of the arguments written with `...`: each
     stands for the elements of its operand, read where it is written. */
  | { k: "apply"; pos: Span; callee: Expr; args: Expr[]; spreads?: number[] }
  | {
      k: "callWithReceiver" | "bindWithReceiver";
      pos: Span;
      callee: Expr;
      receiver: Expr;
      args: Expr[];
    }
  | { k: "conditional"; pos: Span; cond: Expr; then: Expr; else_: Expr }
  | {
      k: "lambda";
      pos: Span;
      typeParams: TypeParamAst[];
      /* `type` is what the body reads. A parameter with a `default` also
         admits `undefined` where the closure is called: that is the value a
         short call binds, and the default replaces it before the body runs. A
         `rest` parameter's type is the array its arguments are collected into:
         a tuple, whose required elements are positions of the signature, or a
         `T[]`, which collects any number of them. */
      params: { name: string; type: ClaimType; default?: Expr; rest?: true }[];
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
  /* A declaration statement binds one or more names, left to right, each
     initializer seeing the earlier bindings. The statement is the entry; the
     producer states no cut between its declarators. */
  | { k: "const"; pos: Span; bindings: BindingAst[] }
  /* Mutable locals. A binding's `annot` is the storage contract every
     assignment is checked against. Absent, the producer supplies one and the
     adapter checks it; an initializer's type is what the binding happens to
     hold first, not what it may hold, so it is never taken for the contract. */
  | { k: "let"; pos: Span; bindings: BindingAst[] }
  /* An object pattern on a `const`. The initializer is evaluated once; each
     property is then read in pattern order, and a default is evaluated only
     when that read is undefined. Every binding is an immutable local. */
  | { k: "pattern"; pos: Span; props: PatternPropAst[]; init: Expr }
  /* An array pattern `const [a, b = d] = init`: each element reads its
     position of the array's store, with a default when the read is
     undefined. */
  | { k: "arrayPattern"; pos: Span; elems: ArrayElemAst[]; init: Expr };

/** One element of an array pattern: position `index` binds `name`. */
export interface ArrayElemAst {
  index: number;
  name: string;
  namePos: Span;
  default_: Expr | null;
}

/** One property of an object pattern: `field: name = default_`. */
export interface PatternPropAst {
  field: string;
  name: string;
  namePos: Span;
  default_: Expr | null;
}

/** One declarator of a `const` or `let` statement. */
export interface BindingAst {
  name: string;
  namePos: Span;
  annot: ClaimType | null;
  init: Expr;
}

export interface TypeParamAst {
  name: string;
  bound: ClaimType | null;
}

export interface FunctionAst {
  name: string;
  namePos: Span;
  typeParams: TypeParamAst[];
  params: { name: string; pos: Span; type: ClaimType; rest?: true }[];
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
