// FIXME: `Id<number>` does not satisfy `P extends string`, so this declaration
// should be rejected (TypeScript rejects it with TS2344). skjs does not check it,
// because an ambient declaration whose signature is normalized nowhere — the
// declared name is used in no checked position — is not constraint-checked. When
// that gap is closed, this declaration should error and this file will need an
// expect-error annotation.

type Id<P extends string> = P;

declare function unusedDeclaration(x: Id<number>): void;

export { unusedDeclaration };
