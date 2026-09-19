// A constructor's membership protocol must survive structural widening.
class MembershipPlain {
  value: number = 0;
}
class MembershipNumeric {
  value: number = 0;
  static [Symbol.hasInstance](x: { value: number }): boolean {
    return x.value.toFixed(0) === "0";
  }
}
function erasedConstructorHook(x: { other: number }): boolean {
  const ctor: typeof MembershipPlain = MembershipNumeric;
  return x instanceof ctor;
}
function erasedFunctionHook(x: { other: number }): boolean {
  const ctor: Function = MembershipNumeric;
  return x instanceof ctor;
}
function retainedMembershipProtocol(x: { value: number }): boolean {
  const ctor: {
    new (): MembershipPlain;
    readonly [Symbol.hasInstance]: (x: { value: number }) => boolean;
  } = MembershipNumeric;
  return x instanceof ctor;
}
// Forgetting callability is safe: this view cannot perform membership tests.
function opaqueMembershipObject(): {} {
  return MembershipNumeric;
}
