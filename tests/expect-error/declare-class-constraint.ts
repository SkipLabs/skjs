// Issue #720: type-argument constraints in `declare class` member types are
// not checked at the declaration site.
//
// `checkDef_` routes `Declare(TopLevelFunDef)` through signature normalization,
// but `Declare(Class _)` fell through a catch-all to `void` — so member types
// in a declared class were never normalized and a constraint violation (`Id<number>`
// for `type Id<P extends string>`) escaped detection when the class was unused.
//
// After the fix: each violating argument is rejected at the declaration site,
// matching tsc (TS2344), whether the class is used or not.

type Id<P extends string> = P;

// Field type in an unused declared class.
declare class WithField {
  // @skjs-expect-error Type argument does not satisfy the constraint
  x: Id<number>;
}

// Method parameter type in an unused declared class.
declare class WithMethod {
  // @skjs-expect-error Type argument does not satisfy the constraint
  method(x: Id<number>): void;
}

// Valid: satisfied constraints are still accepted.
declare class Valid {
  x: Id<string>;
  method(x: Id<"literal">): void;
}
