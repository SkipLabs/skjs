// @ts-expect-error Missing type annotation
function paramNoType(p): void {}

// @ts-expect-error Missing type annotation
function paramNoTypeDefault(p = 3): void {}

// @ts-expect-error Missing type annotation
function paramNoTypeOptional(p?): void {}

// @ts-expect-error Missing type annotation
function paramNoTypeDefaultOptional(p? = 3): void {}

function paramTypeDefault(p: number = 3): void {}

function paramTypeOptional(p?: number): void {}

function paramTypeDefaultOptional(p?: number = 3): void {}

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
function restTypeDefault(...rest: number[] = new Array()): void {}

// prettier-ignore
function restTypeOptional(...rest?: number[]): void {}

// prettier-ignore
function restTypeDefaultOptional(...rest?: number[] = new Array()): void {}

function restNotArray(...rest: number): void {}

// @ts-expect-error ... should be the last parameter
function restNotLast(...rest: number[], other): void {}
