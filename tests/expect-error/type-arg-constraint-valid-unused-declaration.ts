// Counterpart to type-arg-constraint-unused-declaration: an unused ambient
// declaration whose signature satisfies the constraint is accepted. Checking
// every ambient declaration's signature must not over-reject a valid one.

type Id<P extends string> = P;

declare function validUnused(x: Id<"literal">): void;

export { validUnused };
