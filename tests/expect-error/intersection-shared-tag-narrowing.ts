// Regression for the STypes::inter per-tag zeroing bug (soundness).
// "a" | 0 and "a" | 1 share the string value "a", so `x === y` is satisfiable
// and must NOT narrow `x` to `never`. Before the fix, intersecting the two
// tag-keyed unions collapsed to bottom because the empty `num` tag (0 vs 1)
// zeroed the whole map; that made the branch look dead and let a live value be
// typed `never`.
function t(x: "a" | 0, y: "a" | 1): void {
  if (x === y) {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    // @skjs-expect-error-line2 Type 'a'
    // @skjs-expect-error-line3 is not assignable to type never
    const z: never = x;
    console.log(z);
  }
}
t("a", "a");
