// A wrong type-argument count is reported once as an arity error (TS2707), even
// when the supplied arguments would also violate a constraint. The count error
// takes precedence; no constraint error (TS2344) is additionally reported for
// the same reference.

type Id<P extends string> = P;

// @skjs-expect-error Expected 1 type arguments, but got 2
type TooMany = Id<number, number>;
