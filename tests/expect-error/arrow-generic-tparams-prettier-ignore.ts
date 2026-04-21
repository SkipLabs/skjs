// prettier-ignore
// TODO: FIXME generic arrow with multiple type parameters fails to parse.

// @skjs-expect-error Expected token >
const f = <T, U>(x: T, y: U): void => { void x; void y; };
