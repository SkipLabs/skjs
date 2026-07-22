// Optional method-syntax members `m?(): R` carry their optionality, exactly like
// optional property members `m?: () => R`: an inhabiting object may omit the
// member, and calling it without first narrowing away `undefined` is unsound
// (the member may be absent at runtime).

// An object that omits an optional method-syntax member inhabits the type.
type WithOptMethod = { data: number; m?(): number };
export function omitOk(): WithOptMethod {
  return { data: 1 };
}

// Calling an optional method without narrowing may reach `undefined`.
type OnlyOptMethod = { m?(): number };
export function callUnguarded(o: OnlyOptMethod): number {
  // `o.m` is optional, so it may be undefined at the call.
  // @skjs-expect-error This expression is not callable
  return o.m();
}

// A required method-syntax member is unaffected: still attach-callable.
type WithReqMethod = { m(): number };
export function callRequired(o: WithReqMethod): number {
  return o.m();
}

// Control: an optional property-syntax member already carried its optionality.
type WithOptProp = { data: number; p?: () => number };
export function omitPropOk(): WithOptProp {
  return { data: 1 };
}
