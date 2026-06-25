// Issue #720: type-argument constraints in `declare class` member types are
// not checked at the declaration site.
//
// `checkDef_` routes `Declare(TopLevelFunDef)` through signature normalization,
// but `Declare(Class _)` falls through a catch-all to `void` — so member types
// in a declared class are never normalized and a constraint violation (`Id<number>`
// for `type Id<P extends string>`) escapes detection when the class is unused.
//
// tsc rejects both declarations below regardless of use (TS2344).
// BEFORE the fix: skjs accepts them because the class is never used and
//   normalization is never triggered lazily.
// AFTER the fix: skjs rejects them at the declaration site.

type Id<P extends string> = P;

// Field type in an unused declared class — escapes skjs today.
declare class WithField {
  x: Id<number>;
}

// Method parameter type in an unused declared class — also escapes.
declare class WithMethod {
  method(x: Id<number>): void;
}
