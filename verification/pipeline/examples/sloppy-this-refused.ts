// A script without a "use strict" directive is sloppy code, where a plain
// call passes the global object as `this`: the model's receiver rule is
// strict code's, so a function reading `this` there is refused.
function readsThis(this: { n: number }): number {
  return this.n;
}
function caller(): number {
  return readsThis.call({ n: 1 });
}
