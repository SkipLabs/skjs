// An ambient declaration's signature is checked at its declaration site, even
// when the declared name is never used anywhere else: `Id<number>` does not
// satisfy `P extends string`, so the parameter type is rejected (TS2344), the
// same place TypeScript rejects it.

type Id<P extends string> = P;

// @skjs-expect-error Type argument does not satisfy the constraint
declare function unusedDeclaration(x: Id<number>): void;

export { unusedDeclaration };
