// Object-literal spread of a union-typed source loses branch-specific named
// fields. TypeCheckExpr.sk's spread path calls TObject::getFields, which
// folds TFields::union over branches; non-shared named fields without a
// covering index are dropped. TypeScript distributes spread over unions and
// accepts both cases below.
type AB = { a: number } | { b: string };

function spreadUnion(x: AB): AB {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { ...x };
}

// Weaker target — even allowing a and b to be optional fails, confirming
// the fields are dropped entirely rather than merely losing required-ness.
function spreadIntoPartial(x: AB): { a?: number; b?: string } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { ...x };
}
