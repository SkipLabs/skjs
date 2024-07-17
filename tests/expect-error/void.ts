function returningVoid(): void { }

function returningVoid2(): void { return; }

function returningVoid3(): void { while (true) { } }

function returningVoid4(): void { throw {}; }

function returningVoid5(): void { return undefined; }

function returningVoid6(): void { return returningVoid(); }

// @ts-expect-error Invalid return type
function returningVoid7(): void { return null; }

const x: void = returningVoid();

const x2: void = undefined;

// @ts-expect-error Invalid definition
const x3: void = {};

// @ts-expect-error Invalid definition
const x4: () => void = () => null;

// @ts-expect-error Expected an array
const x5: undefined = returningVoid()['bla'];

// @ts-expect-error Invalid comparison. You can only compare strings, numbers, and booleans.
const x6: boolean = returningVoid() < returningVoid();

const x7: boolean = returningVoid() === returningVoid();

type t = void | undefined; // We may want an error here (see #76)

function returningVoidOrNull(): void | null { }
function returningVoidOrNumber(): void | number { }
function returningVoidOrUndefined(): void | undefined { }

// @ts-expect-error Invalid '.'
const x8: string | undefined = returningVoid()?.toString();

// @ts-expect-error Invalid '.'
const x9: string | undefined = returningVoidOrNumber()?.toString();

// @ts-expect-error Invalid operator on type void
const x10: number | undefined = returningVoid() ?? 0;

// @ts-expect-error Invalid operator on type void
const x11: number | undefined = returningVoidOrNumber() ?? 0;

// @ts-expect-error Invalid operator on type void
const x12: number | undefined = returningVoidOrUndefined() ?? 0;

// @ts-expect-error Invalid operator on type void
const x13: number | void | null = returningVoidOrNull() ?? 0;

// @ts-expect-error Invalid ||
const x14: number | undefined = returningVoid() || 0;

// @ts-expect-error Invalid ||
const x15: number | undefined = returningVoidOrNumber() || 0;

// @ts-expect-error Invalid ||
const x16: number | undefined = returningVoidOrUndefined() || 0;

// @ts-expect-error Invalid ||
const x17: number | void | null = returningVoidOrNull() || 0;

function unsafeInTypescript(b: boolean, returningVoid: () => void): string {
    // @ts-expect-error Invalid operator on type void
    return (b ? null : returningVoid()) ?? 'a';
}
// @ts-expect-error Invalid call
unsafeInTypescript(false, returningVoidOrNumber);
