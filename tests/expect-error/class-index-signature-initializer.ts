// A class index signature `[a: string]: T` is not a property: the
// no-constructor definite-assignment check must not report "has no
// initializer" for it (matches tsc). Regular fields still do.
class C {
  [a: string]: number;
  // @skjs-expect-error Field 'v' has no initializer and is not assigned in the constructor
  v: number;
}
