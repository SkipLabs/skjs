// Minimal examples for generic constraints ("extends") + instantiation behavior.
//
// These examples are intended to typecheck cleanly under SKJS.

type StrOrNum = string | number;

export function narrowConstrainedGeneric<T extends StrOrNum>(x: T): number {
  if (typeof x === "string") {
    // In this branch x should be string.
    return x.length;
  }
  // In this branch x should be number (the non-string part of the constraint).
  return x;
}

type Mapper<K extends StrOrNum> = { map(): K };

interface Collection {
  map<K extends StrOrNum>(mapper: Mapper<K>): K;
}

export function instantiateShouldNotClose(col: Collection): string {
  const m: Mapper<string> = { map: (): string => "x" };
  return col.map(m);
}

// Same idea, but with an implicit instantiation where the type argument is a
// fresh inference variable (not an explicit concrete type like `string`).
type Box<T extends StrOrNum> = { readonly v: T };

function mkBox<T extends StrOrNum>(v: T): Box<T> {
  return { v: v };
}

export function instantiateWithInferredTypeArg(x: StrOrNum): number {
  const b = mkBox(x); // type args inferred; `Box<T>` is instantiated with a fresh type variable.
  // NOTE: SKJS refinements like typeof are most reliable on locals.
  const v = b.v;
  if (typeof v === "string") {
    return v.length;
  }
  // After excluding string, the else branch should deduce number.
  return v;
}

// Nested generic constraint: ensure instantiating a constrained alias with a
// type-variable argument does not "close" the variable to the constraint.
type IdConstrained<B extends Box<StrOrNum>> = B;

function idBox<B extends Box<StrOrNum>>(b: B): IdConstrained<B> {
  return b;
}

export function instantiateNestedGenericShouldNotClose(): string {
  const b: Box<string> = { v: "x" };
  // Here `B` is inferred at the call site. The result type is `IdConstrained<B>`,
  // which instantiates the constrained alias with an inference type variable.
  const r = idBox(b);
  return r.v;
}

// Dependent constraints across multiple parameters: U's constraint mentions T.
type Dep<T extends StrOrNum, U extends Box<T>> = { t: T; u: U };

function mkDep<T extends StrOrNum>(t: T): Dep<T, Box<T>> {
  const u: Box<T> = { v: t };
  return { t: t, u: u };
}

export function dependentConstraintInference(): string {
  const d = mkDep("x");
  return d.u.v;
}

// Class instantiation path (Class tparams go through TEnv::instantiate for the
// instance type), with inferred type arguments.
class Wrap<T extends StrOrNum> {
  public v: T;
  constructor(v: T) {
    this.v = v;
  }
}

function mkWrap<T extends StrOrNum>(v: T): Wrap<T> {
  return new Wrap<T>(v);
}

export function classInstantiationWithInferredTypeArg(x: StrOrNum): number {
  const w = mkWrap(x);
  const v = w.v;
  if (typeof v === "string") {
    return v.length;
  }
  return v;
}
