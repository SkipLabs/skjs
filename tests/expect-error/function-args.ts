// @ts-expect-error Missing type annotation
function paramNoType(p): void {}

// @ts-expect-error Missing type annotation
function paramNoTypeDefault(p = 3): void {}

// @ts-expect-error Missing type annotation
function paramNoTypeOptional(p?): void {}

// @ts-expect-error Missing type annotation
function paramNoTypeDefaultOptional(p? = 3): void {}

function paramTypeDefault(p: number = 3): void {}

function callDefault(): void {
  paramTypeDefault();
}

function callDefaultWithUndefined(): void {
  // @ts-expect-error Invalid call
  paramTypeDefault(undefined);
}

function paramTypeOptional(p?: number): void {}

function callOptional(): void {
  paramTypeOptional();
}

function callOptionalWithUndefined(): void {
  paramTypeOptional(undefined);
}

function paramTypeOptionalCanBeUndefined(p?: number): number {
  return p ?? 1;
}

function paramTypeOptionalCanBeUndefinedWitness(p: number): number {
  // @ts-expect-error This operator is useless
  return p ?? 1;
}

function paramTypeOptionalCanBeUndefined2(p?: number): number {
  // @ts-expect-error Invalid call
  return paramTypeOptionalCanBeUndefinedWitness(p);
}

// @ts-expect-error A parameter cannot both be optional and have a default value
function paramTypeDefaultOptional(p?: number = 3): void {}

// @ts-expect-error Default value doesn't have the expected type
function paramDefaultWrongType(p: number = "3"): void {}

// @ts-expect-error Missing type annotation
function restNoType(...rest): void {}

// Disabling prettier because it fixes some issues

// prettier-ignore
// @ts-expect-error Missing type annotation
function restNoTypeDefault(...rest = new Array()): void {}

// prettier-ignore
// @ts-expect-error Missing type annotation
function restNoTypeOptional(...rest?): void {}

// prettier-ignore
// @ts-expect-error Missing type annotation
function restNoTypeDefaultOptional(...rest? = new Array()): void {}

// prettier-ignore
// @ts-expect-error ... cannot have a default value
function restTypeDefault(...rest: number[] = new Array()): void {}

// prettier-ignore
// @ts-expect-error ... cannot be optional
function restTypeOptional(...rest?: number[]): void {}

// prettier-ignore
// @ts-expect-error A parameter cannot both be optional and have a default value
function restTypeDefaultOptional(...rest?: number[] = new Array()): void {}

// TODO: wrong type
function restNotArray(...rest: number): void {}

// @ts-expect-error ... should be the last parameter
function restNotLast(...rest: number[], other): void {}
