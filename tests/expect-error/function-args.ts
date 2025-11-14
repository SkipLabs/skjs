// @ts-expect-error Missing type annotation
function paramNoType(_p): void {}

// @ts-expect-error Missing type annotation
function paramNoTypeDefault(_p = 3): void {}

// @ts-expect-error Missing type annotation
function paramNoTypeOptional(_p?): void {}

// @ts-expect-error Missing type annotation
function paramNoTypeDefaultOptional(_p? = 3): void {}

function paramTypeDefault(_p: number = 3): void {}

function callDefault(): void {
  paramTypeDefault();
}

function callDefaultWithUndefined(): void {
  // @ts-expect-error Invalid call
  paramTypeDefault(undefined);
}

function paramTypeOptional(_p?: number): void {}

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
function paramTypeDefaultOptional(_p?: number = 3): void {}

// @ts-expect-error Default value doesn't have the expected type
function paramDefaultWrongType(_p: number = "3"): void {}

// @ts-expect-error Missing type annotation
function restNoType(..._rest): void {}

// Disabling prettier because it fixes some issues

// prettier-ignore
// @ts-expect-error Missing type annotation
function restNoTypeDefault(..._rest = new Array()): void {}

// prettier-ignore
// @ts-expect-error Missing type annotation
function restNoTypeOptional(..._rest?): void {}

// prettier-ignore
// @ts-expect-error Missing type annotation
function restNoTypeDefaultOptional(..._rest? = new Array()): void {}

// prettier-ignore
// @ts-expect-error ... cannot have a default value
function restTypeDefault(..._rest: number[] = new Array()): void {}

// prettier-ignore
// @ts-expect-error ... cannot be optional
function restTypeOptional(..._rest?: number[]): void {}

// prettier-ignore
// @ts-expect-error A parameter cannot both be optional and have a default value
function restTypeDefaultOptional(..._rest?: number[] = new Array()): void {}

// TODO: wrong type
function restNotArray(..._rest: number): void {}

// @ts-expect-error ... should be the last parameter
function restNotLast(..._rest: number[], _other): void {}
