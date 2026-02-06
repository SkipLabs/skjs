// Duplicate property declarations in object type literals should produce
// user-facing typing errors, not internal map invariant failures.

// @skjs-expect-error Duplicate field a
type DuplicateProperty = { a: number; a: string };

// @skjs-expect-error Duplicate field f
type DuplicateMethodAndProperty = { f(): number; f: number };

const ok: DuplicateProperty = { a: 1 };
console.log(ok);
