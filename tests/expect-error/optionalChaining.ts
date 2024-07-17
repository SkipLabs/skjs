const obj: { f: number } = { f: 1 };

const obj2: { f?: number } = {};

function returningVoid(): void { };

function maybeObj(): { f: number } | undefined { return undefined; }
function maybeObj2(): { f?: number } | null { return {}; }

const x1: number = obj?.f;

const x2: number | undefined = obj2?.f;

const x3: undefined = undefined?.f;

const x4: undefined = null?.f;

// @ts-expect-error Invalid definition
const x5: null = null?.f;

// @ts-expect-error Invalid '.'
const x6: undefined = returningVoid()?.f;

// @ts-expect-error Invalid definition
const x7: undefined = maybeObj()?.f;

// @ts-expect-error Invalid definition
const x8: number = maybeObj()?.f;

const x9: number | undefined = maybeObj()?.f;

// @ts-expect-error Invalid definition
const x10: undefined = maybeObj2()?.f;

// @ts-expect-error Invalid definition
const x11: number = maybeObj2()?.f;

const x12: number | undefined = maybeObj2()?.f;

// @ts-expect-error Unbound field: g
const x13: number | undefined = obj?.g;
