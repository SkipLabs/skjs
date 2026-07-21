// A module-level `const` with no type annotation derives its type from its
// value: when referenced from a context where it is not in the local scope
// (here, another module-level `const`'s initializer), the reference re-folds
// the value expression to recover its precise type.
//
// An `as const` value folds to its literal type, so a consumer with an
// incompatible annotation is rejected (tsc: TS2322, `5` not assignable to `6`).
// Re-folding the value emits the redundant-`as const` warning a second time on
// the declaration; one annotation covers both occurrences.

// @skjs-expect-warning This 'as const' is unnecessary
const foldedConst = 5 as const;

// @skjs-expect-error Type of initializer is not assignable to the declared type annotation
const consumer: 6 = foldedConst;
