/** The fragment: the subset of TypeScript this pipeline accepts, written as an
 * abstract syntax tree. Mirrors Fragment.lean, whose decoders read exactly these
 * shapes. They are structural on purpose: this is a wire format, and its field
 * names are the contract. The parser that produces a tree is fragment-parse.mts.
 * Every annotation is a source type term, the language of declaration bodies.
 */
import type { Atom } from "./claim.mts";
import type { DeclarationDocument, TypeTerm } from "./declaration-types.mts";
import type { Span } from "./span.mts";

export type ArithOp = "add" | "sub" | "mul" | "div";
export type TypeofShape = "number" | "string" | "boolean" | "undefined" | "function" | "bigint" | "symbol";
export type Expr =
  | { k: "id"; pos: Span; name: string }
  /* `this`: the receiver of the nearest enclosing ordinary function. An arrow
     has no receiver of its own, so inside one this is a capture. */
  | { k: "this"; pos: Span }
  | { k: "lit"; pos: Span; lit: Atom }
  | { k: "not" | "typeof"; pos: Span; e: Expr }
  /* `e as T`, `e satisfies T` or `e!`: the operand's value, unchanged. The
     annotation, when there is one, is what the operand must meet. */
  | {
      k: "cast";
      pos: Span;
      cast: "as" | "satisfies" | "nonNull";
      annot: TypeTerm | null;
      e: Expr;
    }
  /* An object literal: one named field per initializer, in source order. A
     shorthand `{ x }` is `{ x: x }`. */
  | { k: "alloc"; pos: Span; fields: { name: string; e: Expr }[] }
  | { k: "read"; pos: Span; field: string; e: Expr }
  /* `e[key]`: evaluate the receiver, then the key. A string singleton names
     one field; a broad string reads through a dictionary view. */
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
      functionType: TypeTerm;
      bagType: TypeTerm;
    }
  /* `typeof e === "…"` (or `!==`, operands in either order): a test of the
     operand's shape. `"object"` is not one shape, since it includes null. */
  | { k: "typeofTest"; pos: Span; shape: TypeofShape; equal: boolean; e: Expr }
  /* `spreads` are the indices of the arguments written with `...`: each
     stands for the elements of its operand, read where it is written. `await
     e` and an async body's returns are written as calls of intrinsics
     (`intrinsics.mts`), whose names no source identifier spells. */
  | { k: "apply"; pos: Span; callee: Expr; args: Expr[]; spreads?: number[] }
  /* `new callee(args)`: the callee, then the arguments left to right, then
     the callee's construct-only code runs. A plain function cannot be one. */
  | { k: "new"; pos: Span; callee: Expr; args: Expr[] }
  /* A class value: its constructor lambda as construct-only code, which only
     `new` runs. */
  | { k: "ctor"; pos: Span; lambda: Expr }
  /* A call through a property reference, `o.m(a)` or `o[k](a)`, parentheses
     around the reference included: the object is saved, the method read from
     it and saved, the arguments evaluated, and the saved method invoked with
     the saved object as its receiver. `callee` is the `read` or `index`. */
  /* `typeArgs`, when written, instantiate the method's leading binders. */
  | { k: "invoke"; pos: Span; callee: Expr; args: Expr[]; spreads?: number[]; typeArgs?: TypeTerm[] }
  /* `f.apply(r, list)`: the target, the receiver and the list are evaluated
     and saved, then the list's length and each indexed element are read in
     order, then the target is invoked with the receiver and those actuals. A
     missing, null or undefined list gives no actuals. */
  | {
      k: "applyWithReceiver";
      pos: Span;
      callee: Expr;
      receiver: Expr;
      list: Expr | null;
    }
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
      params: { name: string; type: TypeTerm; default?: Expr; rest?: true }[];
      /* An arrow has none. An ordinary function expression binds the
         receiver of each call: `type` is its `this` annotation, `unknown`
         where it states none, and `strict` records that the code is strict
         (a module or a "use strict" directive), which the receiver rule
         assumes. */
      receiver: { type: TypeTerm; strict: boolean } | null;
      /* The result annotation; null where the source states none, and the
         producer's claim at the closure proposes the result instead. */
      result: TypeTerm | null;
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
      annot: TypeTerm | null;
      init: Expr;
      body: Expr;
    }
  | {
      k: "ifBody";
      pos: Span;
      result: TypeTerm;
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
  annot: TypeTerm | null;
  init: Expr;
}

export interface TypeParamAst {
  name: string;
  bound: TypeTerm | null;
}

export interface FunctionAst {
  name: string;
  namePos: Span;
  typeParams: TypeParamAst[];
  params: { name: string; pos: Span; type: TypeTerm; rest?: true }[];
  retType: TypeTerm;
  body: Stmt[];
}

export interface Ast {
  file: string;
  sourceSha256: string;
  /** Resolved, fingerprinted source declarations. Lean refuses nonempty
   * closures until their graph interpretation joins the certified plan. */
  declarations: DeclarationDocument;
  /* The module's top-level code in source order: constant bindings and
     expression statements, run once after the function declarations exist. */
  init: Stmt[];
  functions: FunctionAst[];
}
